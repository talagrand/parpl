// Stack depth investigation test
// Run with: cargo test --test stack_depth_test -- --nocapture --ignored
//
// NOTE: These tests are ignored due to known stack overflow bug
// TODO: Fix stack overflow issue before re-enabling

use cello::CelloBuilder;

#[test]
#[ignore]
fn find_max_safe_depth() {
    println!("\n=== Finding maximum safe parsing depth (default 1MB stack) ===\n");

    for depth in [5, 10, 15, 20, 22, 23, 24].iter() {
        let input = "(".repeat(*depth) + "1" + &")".repeat(*depth);

        match CelloBuilder::new().parse_scoped(&input, |ctx| ctx.ast().map(|_| ())) {
            Ok(_) => println!("Depth {}: ✓ SUCCESS", depth),
            Err(e) => println!("Depth {}: ✗ FAILED - {}", depth, e),
        }
    }
}

#[test]
#[ignore]
fn test_with_larger_stack() {
    use std::thread;

    println!("\n=== Testing with 8MB stack ===\n");

    // Spawn a thread with 8MB stack (default is 1MB on Windows)
    let handle = thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            for depth in [10, 20, 30, 40, 50, 60, 70, 80].iter() {
                let input = "(".repeat(*depth) + "1" + &")".repeat(*depth);

                match CelloBuilder::new().parse_scoped(&input, |ctx| ctx.ast().map(|_| ())) {
                    Ok(_) => println!("Depth {} (8MB stack): ✓ SUCCESS", depth),
                    Err(e) => println!("Depth {} (8MB stack): ✗ FAILED - {}", depth, e),
                }
            }
        })
        .expect("Failed to spawn thread");

    handle.join().expect("Thread panicked");
}

#[test]
#[ignore]
fn test_builder_context_depth() {
    println!("\n=== Testing CelloContext with various depths ===\n");

    let mut ctx = CelloBuilder::new().max_nesting_depth(100).build();

    for depth in [5, 10, 15, 20, 25, 30].iter() {
        let input = "(".repeat(*depth) + "1" + &")".repeat(*depth);

        match ctx.parse(&input) {
            Ok(_) => println!("Context depth {}: ✓ SUCCESS", depth),
            Err(e) => println!("Context depth {}: ✗ FAILED - {}", depth, e),
        }
    }
}
