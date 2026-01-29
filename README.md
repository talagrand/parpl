![parpl](docs/parpl-logo.svg)

# <span style="color:#7851A9">parpl</span>: Parse Programming Languages

[![CI](https://github.com/talagrand/parpl/workflows/CI/badge.svg)](https://github.com/talagrand/parpl/actions)
[![Crates.io](https://img.shields.io/crates/v/parpl.svg)](https://crates.io/crates/parpl)
[![Documentation](https://docs.rs/parpl/badge.svg)](https://docs.rs/parpl)

## NOT RELEASED YET
**Note:** parpl is not released to crates.io yet, but will be soon!
##

**A foundation for building interpreters, compilers, and code analysis tools**

Parpl provides standards-conformant parsers for programming languages, designed 
to integrate into your project via trait abstractions. You bring your own AST 
representation; parpl handles the parsing.

## Design

Parpl is a library that provides:

- Standards-conformant parsing that strictly follows language specifications
- Trait-based AST construction so you define your own node types
- Zero opinions about your memory management (arena, Rc, Box—your choice)

Starter implementations are included and designed to be forked. Use them as-is
for quick integration, or adapt the code to your project's needs.

## Supported Parsers

| Parser | Feature Flag | Specification |
|--------|--------------|---------------|
| **CEL** | `cel` | [Common Expression Language](https://github.com/google/cel-spec) |
| **Scheme** | `scheme` | [R7RS Small](https://small.r7rs.org/) external representations |

## Installation

```toml
[dependencies]
parpl = { version = "0.1", features = ["cel", "scheme"] }

# Include starter implementations (use as-is or fork)
parpl = { version = "0.1", features = ["cel", "scheme", "reference"] }
```

## Core Concepts

### Bring Your Own AST

The key abstraction is the **writer trait**. You implement it to construct your 
AST nodes as the parser encounters each construct:

```rust,ignore
// For CEL: implement CelWriter
impl CelWriter for MyInterpreter {
    type Expr = MyExpr;
    type StringId = MySymbolId;
    ...
    
    fn binary(&mut self, op: BinaryOp, left: Self::Expr, right: Self::Expr, span: Span) 
        -> Result<Self::Expr, Self::Error> 
    {
        // Build your own binary expression node
        Ok(MyExpr::Binary { op, left, right })
    }
    
    // ... additional methods
}

// For Scheme: implement DatumWriter
impl DatumWriter for MySchemeReader {
    type Output = MyDatum;
    type StringId = MySymbolId;
    ...
    
    fn list<I>(&mut self, items: I, span: Span) -> Result<Self::Output, Self::Error> {
        // Build your own list representation
        Ok(MyDatum::List(items.collect()))
    }
    
    // ... additional methods
}
```

### Using the Parsers

```
# #[cfg(feature = "reference")]
# fn example() -> Result<(), parpl::Error> {
# use bumpalo::Bump;
# use parpl::StringPool;
# use parpl::scheme::reference::arena::ArenaDatumWriter;
# use parpl::cel::reference::arena::ArenaCelWriter;
# let arena = Bump::new();
# let mut interner = StringPool::new();
// CEL
let parser = parpl::cel::CelParser::default();
# let mut cel_writer = ArenaCelWriter::new(&arena, &mut interner);
let ast = parser.parse("user.age >= 18", &mut cel_writer)?;

// Scheme
let parser = parpl::scheme::SchemeParser::default();
# let mut scheme_writer = ArenaDatumWriter::new(&arena, &mut interner);
let datum = parser.parse("(+ 1 2 3)", &mut scheme_writer)?;
# Ok(())
# }
```

### Starter Implementations

The `reference` feature includes working implementations designed to be forked.
Use them as-is for quick integration, or adapt the code to your project's needs.

```
# #[cfg(feature = "reference")]
# fn example() -> Result<(), parpl::Error> {
use bumpalo::Bump;
use parpl::StringPool;
use parpl::scheme::reference::arena::{ArenaDatumWriter, Datum};

let arena = Bump::new();
let mut interner = StringPool::new();
let mut writer = ArenaDatumWriter::new(&arena, &mut interner);
let parser = parpl::scheme::SchemeParser::default();
let datum = parser.parse("(lambda (x) x)", &mut writer)?;
# Ok(())
# }
```

## Features

- **Specification Conformant**: Strictly follows CEL spec and R7RS Scheme standard
- **Zero-Copy Parsing**: Lexers borrow from input; your AST controls allocation
- **Memory Safe**: Configurable depth limits prevent stack overflow attacks
- **Rich Error Reporting**: Source spans on all errors, REPL-friendly incomplete detection
- **String Interning**: Shared infrastructure for efficient symbol handling

## Safety Limits

Both parsers enforce configurable depth limits to prevent stack overflow:

```
# #[cfg(feature = "reference")]
# fn example() -> Result<(), parpl::Error> {
# use bumpalo::Bump;
# use parpl::StringPool;
# use parpl::scheme::reference::arena::ArenaDatumWriter;
# let arena = Bump::new();
# let mut interner = StringPool::new();
# let source = "(+ 1 2)";
# let mut datum_writer = ArenaDatumWriter::new(&arena, &mut interner);
// CEL: Two-phase depth protection
let parser = parpl::cel::Builder::default()
    .max_parse_depth(128)  // Heuristic pre-validation
    .max_ast_depth(24)     // Precise AST recursion limit
    .max_call_limit(10_000_000)  // DoS protection
    .build();

// Scheme: Single depth limit
let parser = parpl::scheme::Builder::default()
    .max_depth(64)
    .build();
let datum = parser.parse(source, &mut datum_writer)?;
# Ok(())
# }
```

## Error Handling

All errors include source spans for precise error reporting. The parser distinguishes incomplete 
input (for REPL use) from syntax errors, and propagates errors from your writer implementation. 
See [`Error`](https://docs.rs/parpl/latest/parpl/enum.Error.html) for details.

## Feature Flags

| Feature | Description | Default |
|---------|-------------|---------|
| `cel` | CEL parser | No |
| `scheme` | Scheme parser | No |
| `reference` | Starter implementations (use as-is or fork) | No |

Parpl ships with **no default features**. Enable the parser(s) you need.

## Current Status

### Implemented
- [x] Complete CEL lexer and parser (pest-based)
- [x] Complete R7RS Scheme lexer (winnow-based) and reader
- [x] Reference implementations demonstrating trait usage
- [x] Configurable safety limits
- [x] Comprehensive error types with spans
- [x] String interning infrastructure

### Future Plans
- [ ] R7RS `define-syntax` macro expander
- [ ] Additional language parsers

## Related Projects

- [rulesxp](https://github.com/microsoft/rulesxp) - Expression evaluator for Scheme and JsonLogic

## License

MIT License - see LICENSE file for details.
