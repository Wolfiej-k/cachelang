use core::fmt;
use regex::Regex;
use std::{
    collections::HashMap,
    env, fs,
    io::{self, Read},
    process::{exit, Command},
};

/// Value type.
#[derive(Debug, Clone)]
enum Type {
    Scalar,        // Single integer.
    Vector(usize), // List of integers.
}

/// Value data-level.
#[derive(Debug, Clone)]
enum Level {
    Memory,   // Heap memory.
    Cache,    // L1-L3 cache.
    Register, // r8d-r11d register.
}

/// Expression operand.
#[derive(Debug, Clone)]
enum Value {
    Literal(i32),              // Scalar literal.
    Variable(String),          // Scalar or vector reference.
    Index(String, Box<Value>), // Scalar index into vector.
}

/// Bound variable context.
type Context = HashMap<String, (Type, Level, usize)>;

#[derive(Debug)]
enum CompilerError {
    InvalidSyntax(String),
    UndefinedVariable(String),
    RedeclaredVariable(String),
    InvalidType(Type),
    InvalidLevel(Level),
    ResourceLimit(Level),
}

impl Value {
    /// Parse token into DSL value.
    pub fn parse(value: &str) -> Result<Self, CompilerError> {
        if let Ok(x) = value.parse::<i32>() {
            Ok(Value::Literal(x))
        } else if value.contains("[") && value.ends_with("]") {
            let bracket = value.find('[').unwrap();
            let name = &value[..bracket];
            let index = &value[bracket + 1..value.len() - 1];
            Ok(Value::Index(
                name.to_string(),
                Box::new(Self::parse(index)?),
            ))
        } else {
            Ok(Value::Variable(value.to_string()))
        }
    }

    /// Type-check and generate C code.
    pub fn resolve(&self, context: &Context) -> Result<(Type, String), CompilerError> {
        match self {
            Value::Literal(x) => Ok((Type::Scalar, x.to_string())),
            Value::Variable(name) => match context.get(name) {
                Some((ty, level, offset)) => match ty {
                    Type::Scalar => match level {
                        Level::Memory => Ok((ty.clone(), format!("*(mem + {})", offset))),
                        Level::Cache => Ok((ty.clone(), format!("*(cache + {})", offset))),
                        Level::Register => Ok((ty.clone(), format!("reg{}", offset))),
                    },
                    Type::Vector(_) => match level {
                        Level::Memory => Ok((ty.clone(), format!("(mem + {})", offset))),
                        Level::Cache => Ok((ty.clone(), format!("(cache + {})", offset))),
                        Level::Register => Err(CompilerError::InvalidLevel(Level::Register)),
                    },
                },
                None => Err(CompilerError::UndefinedVariable(name.to_string())),
            },
            Value::Index(name, index) => match context.get(name) {
                Some((ty, level, offset)) => match ty {
                    Type::Vector(_) => match index.resolve(context)? {
                        (Type::Scalar, i) => match level {
                            Level::Memory => {
                                Ok((Type::Scalar, format!("(mem + {})[{}]", offset, i)))
                            }
                            Level::Cache => {
                                Ok((Type::Scalar, format!("(cache + {})[{}]", offset, i)))
                            }
                            Level::Register => Err(CompilerError::InvalidLevel(Level::Register)),
                        },
                        (ty, _) => Err(CompilerError::InvalidType(ty.clone())),
                    },
                    _ => Err(CompilerError::InvalidType(ty.clone())),
                },
                None => Err(CompilerError::UndefinedVariable(name.to_string())),
            },
        }
    }
}

/// Value assignment or `flush`.
#[derive(Debug)]
enum Expr {
    // Single assignment, e.g., `x = y`.
    Single {
        name: String,
        level: Level,
        value: Value,
    },
    // Multiple assignment, e.g., `x = [a, b, c, d]`.
    Multiple {
        name: String,
        level: Level,
        values: Vec<Value>,
    },
    // Binary-op assignment, e.g., `x = a * b`.
    Operation {
        name: String,
        level: Level,
        left: Value,
        right: Value,
        op: char,
    },
    // Load from file, e.g., `x = load(10)`.
    Load {
        name: String,
        level: Level,
        length: usize,
    },
    // Print results and clear cache.
    Flush(Vec<String>),
}

impl Expr {
    /// Parse line into DSL expression.
    pub fn parse(line: &str) -> Result<Self, CompilerError> {
        // Flush primitive.
        if line.starts_with("flush(") && line.ends_with(')') {
            let args = &line[6..line.len() - 1];
            let vars = args
                .split(',')
                .map(|v| v.trim().to_string())
                .collect::<Vec<String>>();
            return Ok(Expr::Flush(vars));
        }

        // Handle variable assignment.
        let re = Regex::new(r"^\s*(\w+)\s*@\s*(\w+)\s*=\s*(.*)$").unwrap();
        if let Some(caps) = re.captures(&line) {
            let name = caps.get(1).map_or("", |m| m.as_str()).to_string();
            let level = match caps.get(2).map_or("", |m| m.as_str()) {
                "mem" => Level::Memory,
                "cache" => Level::Cache,
                "reg" => Level::Register,
                x => return Err(CompilerError::InvalidSyntax(x.to_string())),
            };
            let rhs = caps.get(3).map_or("", |m| m.as_str());

            // Load primitive.
            if rhs.starts_with("load(") && rhs.ends_with(")") {
                if let Ok(length) = rhs[5..rhs.len() - 1].parse::<usize>() {
                    if length > 0 {
                        return Ok(Expr::Load {
                            name,
                            level,
                            length,
                        });
                    }
                }
                return Err(CompilerError::InvalidSyntax(rhs.to_string()));
            }

            // Multiple assignment.
            if rhs.starts_with('[') && rhs.ends_with(']') {
                let values = rhs[1..rhs.len() - 1]
                    .split(',')
                    .map(|v| v.trim())
                    .map(|v| {
                        if let Ok(num) = v.parse::<i32>() {
                            Ok(Value::Literal(num))
                        } else {
                            Ok(Value::Variable(v.to_string()))
                        }
                    })
                    .collect::<Result<Vec<Value>, _>>()?;
                return Ok(Expr::Multiple {
                    name,
                    level,
                    values,
                });
            }

            // Binary-op assignment.
            let re = Regex::new(r"^\s*(\S+)\s*([+\-*/])\s*(\S+)\s*$").unwrap();
            if let Some(caps) = re.captures(&rhs) {
                let left = caps.get(1).map_or("", |m| m.as_str());
                let op = caps.get(2).map_or("", |m| m.as_str());
                let right = caps.get(3).map_or("", |m| m.as_str());
                return Ok(Expr::Operation {
                    name,
                    level,
                    left: Value::parse(left)?,
                    right: Value::parse(right)?,
                    op: op.chars().next().unwrap(),
                });
            }

            // Single assignment.
            let value = Value::parse(rhs)?;
            Ok(Expr::Single { name, level, value })
        } else {
            Err(CompilerError::InvalidSyntax(line.to_string()))
        }
    }
}

/// DSL-to-C compiler.
struct Compiler {
    memory: usize,
    cache: usize,
    registers: u8,
}

impl Compiler {
    const CACHE_LINE: usize = 64;
    const CACHE_INTS: usize = 16;

    /// New compiler instance for target system.
    pub fn new(memory: usize, cache: usize) -> Self {
        Self {
            memory: Self::align(memory),
            cache: Self::align(cache),
            registers: 4,
        }
    }

    /// Translate DSL program to C.
    pub fn translate(&self, source: &str) -> Result<String, CompilerError> {
        let mut context = Context::new();
        let mut output = String::new();
        let mut mem_offset = 0;
        let mut cache_offset = 0;
        let mut reg_offset = 0;
        let mut load_offset = 0;

        for line in source.lines() {
            // Resource invariants.
            if mem_offset > self.memory {
                return Err(CompilerError::ResourceLimit(Level::Memory));
            }

            if cache_offset > self.cache {
                return Err(CompilerError::ResourceLimit(Level::Cache));
            }

            if reg_offset > self.registers {
                return Err(CompilerError::ResourceLimit(Level::Register));
            }

            // Empty or comment line.
            let line: String = line.chars().filter(|&c| !c.is_whitespace()).collect();
            if line.is_empty() || line.starts_with("//") {
                continue;
            }

            match Expr::parse(&line)? {
                Expr::Single { name, level, value } => {
                    // Variable already declared.
                    if context.contains_key(&name) {
                        return Err(CompilerError::RedeclaredVariable(name.to_string()));
                    }

                    // Declare new variable.
                    match value.resolve(&context)? {
                        (Type::Scalar, value_code) => match level {
                            Level::Memory => {
                                context.insert(name.to_string(), (Type::Scalar, level, mem_offset));
                                output.push_str(&format!(
                                    "{}    *(mem + {}) = {};\n",
                                    self.prefetch(cache_offset, "    "),
                                    mem_offset,
                                    value_code
                                ));
                                mem_offset += 1
                            }
                            Level::Cache => {
                                context
                                    .insert(name.to_string(), (Type::Scalar, level, cache_offset));
                                output.push_str(&format!(
                                    "{}    *(cache + {}) = {};\n",
                                    self.prefetch(cache_offset + 1, "    "),
                                    cache_offset,
                                    value_code
                                ));
                                cache_offset += 1
                            }
                            Level::Register => {
                                context.insert(
                                    name.to_string(),
                                    (Type::Scalar, level, reg_offset.into()),
                                );
                                output.push_str(&format!(
                                    "{}    reg{} = {};\n",
                                    self.prefetch(cache_offset, "    "),
                                    reg_offset,
                                    value_code
                                ));
                                reg_offset += 1
                            }
                        },
                        (Type::Vector(length), value_code) => match level {
                            Level::Memory => {
                                context.insert(
                                    name.to_string(),
                                    (Type::Vector(length), level, mem_offset),
                                );
                                output.push_str(&format!(
                                    "    for (int i = 0; i < {}; i += 16) {{\n{}        for (int j = i; j < i + 16 && j < {}; j++) {{\n            (mem + {})[j] = {}[j];\n        }}\n    }}\n",
                                    length, self.prefetch(cache_offset, "        "), length, mem_offset, value_code
                                ));
                                mem_offset += length
                            }
                            Level::Cache => {
                                cache_offset = Self::align(cache_offset);
                                context.insert(
                                    name.to_string(),
                                    (Type::Vector(length), level, cache_offset),
                                );
                                output.push_str(&format!(
                                    "    for (int i = 0; i < {}; i += 16) {{\n{}        for (int j = i; j < i + 16 && j < {}; j++) {{\n            (cache + {})[j] = {}[j];\n        }}\n    }}\n",
                                    length, self.prefetch(cache_offset + length, "        "), length, cache_offset, value_code
                                ));
                                cache_offset += length
                            }
                            Level::Register => return Err(CompilerError::InvalidLevel(level)),
                        },
                    }
                }
                Expr::Multiple {
                    name,
                    level,
                    values,
                } => {
                    // Variable already declared.
                    if context.contains_key(&name) {
                        return Err(CompilerError::RedeclaredVariable(name.to_string()));
                    }

                    // Declare new variable.
                    match level {
                        Level::Memory => {
                            let mut code = Vec::new();
                            for (i, value) in values.iter().enumerate() {
                                match value.resolve(&context)? {
                                    (Type::Scalar, value_code) => code.push(format!(
                                        "    (mem + {})[{}] = {};\n",
                                        mem_offset, i, value_code
                                    )),
                                    (value_type, _) => {
                                        return Err(CompilerError::InvalidType(value_type))
                                    }
                                }
                            }

                            context.insert(
                                name.to_string(),
                                (Type::Vector(values.len()), level, mem_offset),
                            );
                            let prefetch = self.prefetch(cache_offset, "    ");
                            for line in code {
                                output.push_str(&prefetch);
                                output.push_str(&line);
                            }
                            mem_offset += values.len();
                        }
                        Level::Cache => {
                            let mut code = Vec::new();
                            for (i, value) in values.iter().enumerate() {
                                match value.resolve(&context)? {
                                    (Type::Scalar, value_code) => code.push(format!(
                                        "    (cache + {})[{}] = {};\n",
                                        cache_offset, i, value_code
                                    )),
                                    (value_type, _) => {
                                        return Err(CompilerError::InvalidType(value_type))
                                    }
                                }
                            }

                            context.insert(
                                name.to_string(),
                                (Type::Vector(values.len()), level, cache_offset),
                            );
                            let prefetch = self.prefetch(cache_offset + values.len(), "    ");
                            for line in code {
                                output.push_str(&prefetch);
                                output.push_str(&line);
                            }
                            cache_offset += values.len();
                        }
                        Level::Register => return Err(CompilerError::InvalidLevel(level)),
                    }
                }
                Expr::Operation {
                    name,
                    level,
                    left,
                    right,
                    op,
                } => {
                    // Variable already declared.
                    if context.contains_key(&name) {
                        return Err(CompilerError::RedeclaredVariable(name.to_string()));
                    }

                    match (left.resolve(&context)?, right.resolve(&context)?, &level) {
                        ((Type::Scalar, left_code), (Type::Scalar, right_code), Level::Memory) => {
                            // Declare new variable.
                            context.insert(name.to_string(), (Type::Scalar, level, mem_offset));
                            output.push_str(&format!(
                                "{}    *(mem + {}) = {} {} {};\n",
                                self.prefetch(cache_offset, "    "),
                                mem_offset,
                                left_code,
                                op,
                                right_code
                            ));
                            mem_offset += 1
                        }
                        ((Type::Scalar, left_code), (Type::Scalar, right_code), Level::Cache) => {
                            // Declare new variable.
                            context.insert(name.to_string(), (Type::Scalar, level, cache_offset));
                            output.push_str(&format!(
                                "{}    *(cache + {}) = {} {} {};\n",
                                self.prefetch(cache_offset, "    "),
                                cache_offset,
                                left_code,
                                op,
                                right_code
                            ));
                            cache_offset += 1
                        }
                        (
                            (Type::Scalar, left_code),
                            (Type::Scalar, right_code),
                            Level::Register,
                        ) => {
                            // Declare new variable.
                            context
                                .insert(name.to_string(), (Type::Scalar, level, reg_offset.into()));
                            output.push_str(&format!(
                                "{}    reg{} = {} {} {};\n",
                                self.prefetch(cache_offset, "    "),
                                reg_offset,
                                left_code,
                                op,
                                right_code
                            ));
                            reg_offset += 1
                        }
                        (
                            (Type::Vector(length), left_code),
                            (Type::Vector(_length), right_code),
                            Level::Memory,
                        ) if length == _length => {
                            // Declare new variable.
                            context.insert(
                                name.to_string(),
                                (Type::Vector(length), level, mem_offset),
                            );
                            output.push_str(&format!(
                                "    for (int i = 0; i < {}; i += 16) {{\n{}        for (int j = i; j < i + 16 && j < {}; j++) {{\n            (mem + {})[j] = {}[j] {} {}[j];\n        }}\n    }}\n",
                                length, self.prefetch(cache_offset, "        "), length, mem_offset, left_code, op, right_code
                            ));
                            mem_offset += length
                        }
                        (
                            (Type::Vector(length), left_code),
                            (Type::Vector(_length), right_code),
                            Level::Cache,
                        ) if length == _length => {
                            // Declare new variable.
                            context.insert(
                                name.to_string(),
                                (Type::Vector(length), level, cache_offset),
                            );
                            output.push_str(&format!(
                                "    for (int i = 0; i < {}; i += 16) {{\n{}        for (int j = i; j < i + 16 && j < {}; j++) {{\n            (cache + {})[j] = {}[j] {} {}[j];\n        }}\n    }}\n",
                                length, self.prefetch(cache_offset + length, "        "), length, cache_offset, left_code, op, right_code
                            ));
                            cache_offset += length
                        }
                        (
                            (Type::Scalar, left_code),
                            (Type::Vector(length), right_code),
                            Level::Memory,
                        ) => {
                            // Declare new variable.
                            context.insert(
                                name.to_string(),
                                (Type::Vector(length), level, mem_offset),
                            );
                            output.push_str(&format!(
                                "    for (int i = 0; i < {}; i += 16) {{\n{}        for (int j = i; j < i + 16 && j < {}; j++) {{\n            (mem + {})[j] = {} {} {}[j];\n        }}\n    }}\n",
                                length, self.prefetch(cache_offset, "        "), length, mem_offset, left_code, op, right_code
                            ));
                            mem_offset += length
                        }
                        (
                            (Type::Scalar, left_code),
                            (Type::Vector(length), right_code),
                            Level::Cache,
                        ) => {
                            // Declare new variable.
                            context.insert(
                                name.to_string(),
                                (Type::Vector(length), level, cache_offset),
                            );
                            output.push_str(&format!(
                                "    for (int i = 0; i < {}; i += 16) {{\n{}        for (int j = i; j < i + 16 && j < {}; j++) {{\n            (cache + {})[j] = {} {} {}[j];\n        }}\n    }}\n",
                                length, self.prefetch(cache_offset + length, "        "), length, cache_offset, left_code, op, right_code
                            ));
                            cache_offset += length
                        }
                        (
                            (Type::Vector(length), left_code),
                            (Type::Scalar, right_code),
                            Level::Memory,
                        ) => {
                            // Declare new variable.
                            context.insert(
                                name.to_string(),
                                (Type::Vector(length), level, mem_offset),
                            );
                            output.push_str(&format!(
                                "    for (int i = 0; i < {}; i += 16) {{\n{}        for (int j = i; j < i + 16 && j < {}; j++) {{\n            (mem + {})[j] = {}[j] {} {};\n        }}\n    }}\n",
                                length, self.prefetch(cache_offset, "        "), length, mem_offset, left_code, op, right_code
                            ));
                            mem_offset += length
                        }
                        (
                            (Type::Vector(length), left_code),
                            (Type::Scalar, right_code),
                            Level::Cache,
                        ) => {
                            // Declare new variable.
                            context.insert(
                                name.to_string(),
                                (Type::Vector(length), level, cache_offset),
                            );
                            output.push_str(&format!(
                                "    for (int i = 0; i < {}; i += 16) {{\n{}        for (int j = i; j < i + 16 && j < {}; j++) {{\n            (cache + {})[j] = {}[j] {} {};\n        }}\n    }}\n",
                                length, self.prefetch(cache_offset + length, "        "), length, cache_offset, left_code, op, right_code
                            ));
                            cache_offset += length
                        }
                        (_, (right_type, _), Level::Memory | Level::Cache) => {
                            return Err(CompilerError::InvalidType(right_type))
                        }
                        (_, _, Level::Register) => return Err(CompilerError::InvalidLevel(level)),
                    }
                }
                Expr::Load {
                    name,
                    level,
                    length,
                } => {
                    match level {
                        Level::Memory => {
                            // Copy from stdin to memory.
                            let code = format!(
                                "    if (fread(mem + {}, sizeof(int), {}, stdin) < {}) {{\n        return 1;\n    }}\n",
                                mem_offset, length, length
                            );
                            output.insert_str(load_offset, &code);

                            // Declare new variable.
                            context.insert(
                                name.to_string(),
                                if length > 1 {
                                    (Type::Vector(length), level, mem_offset)
                                } else {
                                    (Type::Scalar, level, mem_offset)
                                },
                            );

                            // Update offsets.
                            mem_offset += length;
                            load_offset += code.len();
                        }
                        Level::Cache => {
                            // Copy from stdin to cache.
                            let code = format!(
                                "    if (fread(cache + {}, sizeof(int), {}, stdin) < {}) {{\n        return 1;\n    }}\n",
                                cache_offset, length, length
                            );
                            output.insert_str(load_offset, &code);

                            // Declare new variable.
                            context.insert(
                                name.to_string(),
                                if length > 1 {
                                    (Type::Vector(length), level, cache_offset)
                                } else {
                                    (Type::Scalar, level, cache_offset)
                                },
                            );

                            // Update offsets.
                            cache_offset += length;
                            load_offset += code.len();
                        }
                        Level::Register => return Err(CompilerError::InvalidLevel(level)),
                    }
                }
                Expr::Flush(vars) => {
                    // Print each variable.
                    for var in vars {
                        match Value::Variable(var.clone()).resolve(&context)? {
                            (Type::Scalar, var_code) => {
                                output.push_str(&format!(
                                    "    printf(\"{} = %d\\n\", {});\n",
                                    var, var_code
                                ));
                            }
                            (Type::Vector(length), var_code) => {
                                output.push_str(&format!(
                                    "    printf(\"{} = [\");\n    for (int i = 0; i < {}; i++) {{\n        printf(\"%d\", {}[i]);\n        if (i < {} - 1) printf(\", \");\n    }}\n    printf(\"]\\n\");\n",
                                    var, length, var_code, length
                                ));
                            }
                        }
                    }

                    output.push_str("\n");

                    // "Flush" all variables.
                    context.clear();

                    mem_offset = 0;
                    cache_offset = 0;
                    reg_offset = 0;
                    load_offset = output.len();
                }
            }
        }

        Ok(format!(
            r#"
#include <stdlib.h>
#include <stdio.h>

register int reg0 asm("r12");
register int reg1 asm("r13");
register int reg2 asm("r14");
register int reg3 asm("r15");

int main() {{
    int *restrict mem = aligned_alloc({}, {});
    int *restrict cache = aligned_alloc({}, {});

{}    return 0;
}}
        "#,
            Self::CACHE_LINE,
            self.memory * size_of::<i32>(),
            Self::CACHE_LINE,
            self.cache * size_of::<i32>(),
            output
        ))
    }

    /// Prefetch all cache variables.
    fn prefetch(&self, offset: usize, indent: &str) -> String {
        if offset == 0 {
            String::new()
        } else {
            format!(
                "{}for (int j = 0; j < {}; j += {}) {{\n{}    volatile int _ = cache[j];\n{}}}\n",
                indent,
                offset,
                Self::CACHE_INTS,
                indent,
                indent
            )
        }
    }

    /// Align offset to cache line boundary.
    fn align(offset: usize) -> usize {
        (offset + Self::CACHE_INTS - 1) & !(Self::CACHE_INTS - 1)
    }
}

impl fmt::Display for CompilerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CompilerError::InvalidSyntax(line) => write!(f, "Invalid syntax: {}", line),
            CompilerError::UndefinedVariable(name) => write!(f, "Undefined variable: {}", name),
            CompilerError::RedeclaredVariable(name) => write!(f, "Redeclared variable: {}", name),
            CompilerError::InvalidType(ty) => write!(f, "Invalid type: {:?}", ty),
            CompilerError::InvalidLevel(level) => write!(f, "Invalid level: {:?}", level),
            CompilerError::ResourceLimit(level) => write!(f, "Resource limit: {:?}", level),
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 || (args.len() > 3 && args.len() != 5) {
        eprintln!("Usage: <memory> <cache> [--compile <output>]");
        exit(1);
    }

    let memory: usize = match args[1].parse() {
        Ok(value) => value,
        Err(_) => {
            eprintln!("Invalid memory size: {}", args[1]);
            exit(1);
        }
    };

    let cache: usize = match args[2].parse() {
        Ok(value) => value,
        Err(_) => {
            eprintln!("Invalid cache size: {}", args[2]);
            exit(1);
        }
    };

    let compile = args.contains(&"--compile".to_string());
    let output = if compile {
        match args.get(4) {
            Some(name) => name.clone(),
            None => {
                eprintln!("Specify an output file when using --compile.");
                exit(1);
            }
        }
    } else {
        String::new()
    };

    let mut source = String::new();
    if let Err(err) = io::stdin().read_to_string(&mut source) {
        eprintln!("Failed to read source: {}", err);
        exit(1);
    }

    let compiler = Compiler::new(memory, cache);
    match compiler.translate(&source) {
        Ok(target) => {
            if !compile {
                println!("{}", target);
            } else {
                let tempfile = format!("{}.tmp.c", output);
                if let Err(err) = fs::write(&tempfile, target) {
                    eprintln!("Failed to write to file {}: {}", tempfile, err);
                    exit(1);
                }

                let gcc = Command::new("gcc")
                    .arg("-O3")
                    .arg("-g")
                    .arg("-ffixed-r12")
                    .arg("-ffixed-r13")
                    .arg("-ffixed-r14")
                    .arg("-ffixed-r15")
                    .arg(&tempfile)
                    .arg("-o")
                    .arg(output)
                    .status();

                if let Err(err) = fs::remove_file(&tempfile) {
                    eprintln!("Failed to remove temporary file {}: {}", tempfile, err);
                }

                match gcc {
                    Ok(status) if status.success() => exit(0),
                    Ok(status) => {
                        eprintln!("GCC failed with exit code: {}", status)
                    }
                    Err(err) => eprintln!("Failed to run GCC: {}", err),
                }
            }
        }
        Err(err) => {
            eprintln!("Compiler error: {}", err);
            exit(1);
        }
    }
}
