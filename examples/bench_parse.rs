// Simple parse throughput benchmark for Cello
//
// This example parses a fixed CEL expression 200,000 times and reports
// the total time and parses per second.
//
// Run with:
//   cargo run --release --example bench_parse

use parpl::cel::{CelloBuilder, Result};
use std::time::Instant;

fn main() -> Result<()> {
    const ITERATIONS: u64 = 200_000;

    // Choose a moderately complex expression to exercise the parser.
    let expr = "user.age >= 18 && user.country == \"US\" && \n        items.filter(x, x.price > 100).map(x, x.name).size() > 0";

    println!("Cello parse benchmark");
    println!("Expression: {}", expr.replace('\n', " "));
    println!("Target iterations: {}", ITERATIONS);

    // Reuse a single context to avoid measuring builder construction each time.
    let mut ctx = CelloBuilder::new().build();

    let start = Instant::now();
    let mut iterations: u64 = 0;

    while iterations < ITERATIONS {
        ctx.parse(expr)?;
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
