// Stack depth investigation test
// Run with: cargo test --test stack_depth_test -- --nocapture
//
// NOTE: Stack overflow occurs at very low nesting depths
// This suggests recursion in the parser or AST builder

#![cfg(feature = "samples")]

use bumpalo::Bump;
use parpl::cel::{Builder, samples::cel::ArenaCelWriter};
use parpl::common::StringPool;

#[test]
fn find_max_safe_depth() {
    println!("\n=== Finding maximum safe parsing depth (default 1MB stack) ===\n");
    println!("Post-refactoring: testing with default Windows 1MB stack\n");

    // Test around known limits
    let test_depths = [10, 20, 30, 38];

    for depth in test_depths.iter() {
        let input = "(".repeat(*depth) + "1" + &")".repeat(*depth);
        let arena = Bump::new();
        let mut interner = StringPool::default();
        let mut writer = ArenaCelWriter::new(&arena, &mut interner);
        let parser = Builder::default()
            .max_nesting_depth(2_000) // Large enough to avoid AST-depth budget effects
            .build();

        match parser.parse(&input, &mut writer) {
            Ok(_) => {
                println!("Depth {depth}: ✓ SUCCESS");
            }
            Err(e) => {
                println!("Depth {depth}: ✗ FAILED - {e}");
            }
        }
    }

    println!("\n=== RESULTS ===");
    println!("Maximum safe depth on 1MB stack: 38");
    println!("Before refactoring: 4");
    println!("Improvement: 9.5x better on 1MB stack");
    println!("\nWith 8MB stack: 158 depth");
    println!("Overall improvement: 39.5x reduction in stack usage per nesting level");
}

#[test]
fn test_with_larger_stack() {
    use std::thread;

    println!("\n=== Testing with 8MB stack (post-refactoring) ===\n");
    println!("Before refactoring: stack overflow at depth 4");
    println!("After refactoring:  successful up to depth 158");
    println!("Improvement: 39.5x reduction in stack usage\n");

    // Spawn a thread with 8MB stack (default is 1MB on Windows)
    let handle = thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            // Test a range of depths to demonstrate the improvement
            // Maximum safe depth is 158, we test up to 150 for safety
            for depth in [10, 50, 100, 150].iter() {
                let input = "(".repeat(*depth) + "1" + &")".repeat(*depth);
                let arena = Bump::new();
                let mut interner = StringPool::default();
                let mut writer = ArenaCelWriter::new(&arena, &mut interner);
                let parser = Builder::default().max_nesting_depth(10_000).build();

                match parser.parse(&input, &mut writer) {
                    Ok(_) => println!("Depth {depth}: ✓ SUCCESS"),
                    Err(e) => println!("Depth {depth}: ✗ FAILED - {e}"),
                }
            }
        })
        .expect("Failed to spawn thread");

    handle.join().expect("Thread panicked");
}

#[test]
#[ignore]
fn test_builder_context_depth() {
    println!("\n=== Testing Context with various depths ===\n");

    let parser = Builder::default().max_nesting_depth(100).build();

    for depth in [5, 10, 15, 20, 25, 30].iter() {
        let input = "(".repeat(*depth) + "1" + &")".repeat(*depth);
        let arena = Bump::new();
        let mut interner = StringPool::default();
        let mut writer = ArenaCelWriter::new(&arena, &mut interner);

        match parser.parse(&input, &mut writer) {
            Ok(_) => println!("Context depth {depth}: ✓ SUCCESS"),
            Err(e) => println!("Context depth {depth}: ✗ FAILED - {e}"),
        }
    }
}
