// Simple parse throughput benchmark for the CEL parser
//
// This example parses a fixed CEL expression 200,000 times and reports
// the total time and parses per second.
//
// Run with:
//   cargo run --release --example bench_parse

use bumpalo::Bump;
use parpl::{
    cel::{Builder, Result, samples::cel::ArenaCelWriter},
    common::StringPool,
};
use std::time::Instant;

fn main() -> Result<()> {
    const ITERATIONS: u64 = 200_000;

    // Choose a moderately complex expression to exercise the parser.
    let expr = "user.age >= 18 && user.country == \"US\" && \n        items.filter(x, x.price > 100).map(x, x.name).size() > 0";

    println!("CEL parser benchmark");
    println!("Expression: {}", expr.replace('\n', " "));
    println!("Target iterations: {}", ITERATIONS);

    // Setup memory management
    let mut bump = Bump::new();
    let mut pool = StringPool::new();

    // Reuse a single parser driver
    let cel = Builder::default().build();

    let start = Instant::now();
    let mut iterations: u64 = 0;

    while iterations < ITERATIONS {
        // Reset the arena to avoid unbounded memory growth
        bump.reset();

        // Create a writer for this iteration
        let mut writer = ArenaCelWriter::new(&bump, &mut pool);

        // Parse
        cel.parse(expr, &mut writer)?;

        iterations += 1;
    }

    let elapsed = start.elapsed();
    let secs = elapsed.as_secs_f64();
    let throughput = if secs > 0.0 {
        iterations as f64 / secs
    } else {
        0.0
    };

    println!("\nCompleted {} parses in {:?}", iterations, elapsed);
    println!("Throughput: {:.0} parses/second", throughput);

    Ok(())
}
