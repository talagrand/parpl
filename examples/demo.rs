// Comprehensive CEL Parser Demo
//
// This example demonstrates the key features of the CEL parser:
// 1. A scoped parsing helper (closure-based) that keeps lifetimes safe
// 2. Builder pattern configuration and config inspection
// 3. Pretty-printing ASTs (with and without spans)
// 4. Error handling
// 5. Reuse patterns (driver reuse + arena reuse)

use bumpalo::Bump;
use parpl::cel::samples::cel::ArenaCelWriter;
use parpl::cel::traits::CelWriter;
use parpl::cel::{
    Builder, CelParser, Expr, PrettyConfig, Result, pretty_print, pretty_print_with_config,
};
use parpl::common::StringPool;

fn parse_scoped<R>(
    parser: &CelParser,
    input: &str,
    f: impl for<'arena> FnOnce(&'arena Expr<'arena>, &StringPool) -> Result<R>,
) -> Result<R> {
    let bump = Bump::new();
    let mut pool = StringPool::new();
    let mut writer = ArenaCelWriter::new(&bump, &mut pool);
    let ast = parser.parse(input, &mut writer)?;
    f(ast, writer.interner_ref())
}

struct DemoContext {
    bump: Bump,
    pool: StringPool,
}

impl DemoContext {
    fn new() -> Self {
        Self {
            bump: Bump::new(),
            pool: StringPool::new(),
        }
    }

    fn parse_and_print(&mut self, parser: &CelParser, input: &str) -> Result<()> {
        self.bump.reset();
        let mut writer = ArenaCelWriter::new(&self.bump, &mut self.pool);
        let ast = parser.parse(input, &mut writer)?;
        println!("{}", pretty_print(ast, writer.interner_ref()));
        Ok(())
    }
}

fn main() -> Result<()> {
    println!("=== CEL Parser Demo ===\n");

    // ========================================================================
    // 1. SCOPED API - Safe arena-based parsing
    // ========================================================================
    println!("1. Scoped API (automatic memory management):");

    // Create the parser driver (reusable across parses).
    let parser = Builder::default().build();

    parse_scoped(&parser, "1 + 2 * 3", |ast, interner| {
        println!("   Expression: 1 + 2 * 3");
        println!("{}", pretty_print(ast, interner));
        Ok(())
    })?;

    // ========================================================================
    // 2. PRETTY-PRINTING - Visualize AST structure
    // ========================================================================
    println!("\n2. Pretty-printing AST:");

    parse_scoped(&parser, "x > 0 ? x : -x", |ast, interner| {
        println!("   Expression: x > 0 ? x : -x");
        println!("{}", pretty_print(ast, interner));
        Ok(())
    })?;

    // With span information
    println!("\n   With source locations:");
    parse_scoped(&parser, "true && false", |ast, interner| {
        let config = PrettyConfig::default().with_spans();
        println!("   Expression: true && false");
        println!("{}", pretty_print_with_config(ast, &config, interner));
        Ok(())
    })?;

    // ========================================================================
    // 3. BUILDER PATTERN - Custom configuration
    // ========================================================================
    println!("\n3. Builder with configuration:");

    let parser_config = Builder::default()
        .max_parse_depth(64)
        .max_ast_depth(20)
        .max_call_limit(1_000_000)
        .strict_mode(true)
        .build();

    let cfg = parser_config.config();
    println!("   max_parse_depth: {}", cfg.max_parse_depth);
    println!("   max_ast_depth:   {}", cfg.max_ast_depth);
    println!("   max_call_limit:  {}", cfg.max_call_limit);
    println!("   strict_mode:     {}", parser_config.is_strict_mode());

    parse_scoped(&parser_config, "42", |_, _| {
        println!("   ✓ Configuration applied");
        Ok(())
    })?;

    // ========================================================================
    // 4. CONTEXT REUSE - Parse multiple expressions
    // ========================================================================
    println!("\n4. Context reuse:");

    // `Cel` is trivially reusable; for arena-backed ASTs, reuse is about how you
    // manage the arena lifetime. Here we reuse an arena+interner and reset the arena
    // between parses (safe because we don't keep AST references).
    let mut ctx = DemoContext::new();

    println!("   First parse: [1, 2, 3]");
    ctx.parse_and_print(&parser, "[1, 2, 3]")?;

    println!("   Second parse: {{\"a\": 1, \"b\": 2}}");
    ctx.parse_and_print(&parser, "{\"a\": 1, \"b\": 2}")?;

    println!("   ✓ Same driver + reused arena/pool");

    // ========================================================================
    // 5. ERROR HANDLING - Graceful failure
    // ========================================================================
    println!("\n5. Error handling:");

    // Syntax error
    match parse_scoped(&parser, "1 + + 2", |_, _| Ok(())) {
        Ok(_) => println!("   ✗ Should have failed"),
        Err(e) => println!("   ✓ Syntax error caught: {e}"),
    }

    // Reserved word error
    match parse_scoped(&parser, "for", |_, _| Ok(())) {
        Ok(_) => println!("   ✗ Should have failed"),
        Err(e) => println!("   ✓ Reserved word rejected: {e}"),
    }

    // ========================================================================
    // 6. COMPLEX EXPRESSIONS - Real-world examples
    // ========================================================================
    println!("\n6. Complex expressions:");

    let examples = vec![
        "items.filter(x, x.price > 100).map(x, x.name)",
        "user.age >= 18 && user.country == \"US\"",
        "timestamp(\"2024-01-01T00:00:00Z\") + duration(\"1h\")",
        "[1, 2, 3].exists(x, x > 2)",
    ];

    for expr in examples {
        match parse_scoped(&parser, expr, |_, _| Ok(())) {
            Ok(_) => println!("   ✓ Parsed: {expr}"),
            Err(e) => println!("   ✗ Failed: {expr} - {e}"),
        }
    }

    println!("\n=== Demo Complete ===");
    Ok(())
}
