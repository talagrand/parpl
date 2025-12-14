// Comprehensive CEL Parser Demo
//
// This example demonstrates the key features of the CEL parser:
// 1. Basic parsing with the scoped API
// 2. Builder pattern with configuration
// 3. Pretty-printing ASTs
// 4. Error handling
// 5. Context reuse

use parpl::cel::{Builder, PrettyConfig, Result, pretty_print, pretty_print_with_config};

fn main() -> Result<()> {
    println!("=== CEL Parser Demo ===\n");

    // ========================================================================
    // 1. SCOPED API - Safe arena-based parsing
    // ========================================================================
    println!("1. Scoped API (automatic memory management):");

    Builder::new().parse_scoped("1 + 2 * 3", |ctx| {
        let ast = ctx.ast()?;
        println!("   Expression: 1 + 2 * 3");
        println!("   Result: {}", ast);
        Ok(())
    })?;

    // ========================================================================
    // 2. PRETTY-PRINTING - Visualize AST structure
    // ========================================================================
    println!("\n2. Pretty-printing AST:");

    Builder::new().parse_scoped("x > 0 ? x : -x", |ctx| {
        let ast = ctx.ast()?;
        println!("   Expression: x > 0 ? x : -x");
        println!("{}", pretty_print(ast));
        Ok(())
    })?;

    // With span information
    println!("\n   With source locations:");
    Builder::new().parse_scoped("true && false", |ctx| {
        let ast = ctx.ast()?;
        let config = PrettyConfig::new().with_spans();
        println!("   Expression: true && false");
        println!("{}", pretty_print_with_config(ast, &config));
        Ok(())
    })?;

    // ========================================================================
    // 3. BUILDER PATTERN - Custom configuration
    // ========================================================================
    println!("\n3. Builder with configuration:");

    Builder::new()
        .max_nesting_depth(20)
        .max_call_limit(1_000_000)
        .parse_scoped("42", |ctx| {
            println!(
                "   Max nesting depth: {}",
                ctx.config().get_max_nesting_depth()
            );
            println!("   Max call limit: {}", ctx.config().get_max_call_limit());
            println!("   ✓ Configuration applied");
            Ok(())
        })?;

    // ========================================================================
    // 4. CONTEXT REUSE - Parse multiple expressions
    // ========================================================================
    println!("\n4. Context reuse:");

    let mut ctx = Builder::new().build();

    ctx.parse("[1, 2, 3]")?;
    println!("   First parse: {}", ctx.input().unwrap());

    ctx.parse("{\"a\": 1, \"b\": 2}")?;
    println!("   Second parse: {}", ctx.input().unwrap());
    println!("   ✓ Same context, different expressions");

    // ========================================================================
    // 5. ERROR HANDLING - Graceful failure
    // ========================================================================
    println!("\n5. Error handling:");

    // Syntax error
    match Builder::new().parse_scoped("1 + + 2", |ctx| ctx.ast().map(|_| ())) {
        Ok(_) => println!("   ✗ Should have failed"),
        Err(e) => println!("   ✓ Syntax error caught: {}", e),
    }

    // Reserved word error
    match Builder::new().parse_scoped("for", |ctx| ctx.ast().map(|_| ())) {
        Ok(_) => println!("   ✗ Should have failed"),
        Err(e) => println!("   ✓ Reserved word rejected: {}", e),
    } // ========================================================================
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
        match Builder::new().parse_scoped(expr, |ctx| ctx.ast().map(|_| ())) {
            Ok(_) => println!("   ✓ Parsed: {}", expr),
            Err(e) => println!("   ✗ Failed: {} - {}", expr, e),
        }
    }

    println!("\n=== Demo Complete ===");
    Ok(())
}
