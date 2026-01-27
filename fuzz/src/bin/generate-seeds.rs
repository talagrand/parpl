//! Generates seed corpus files from the in-code seed definitions.
//!
//! Run with: `cargo run --manifest-path fuzz/Cargo.toml --bin generate-seeds`
//!
//! This writes seed files to the corpus directories where libFuzzer
//! will pick them up. Files are not overwritten if they already exist,
//! so the fuzzer's discoveries are preserved.

use parpl_fuzz::seeds;
use std::{fs, path::Path};

fn main() {
    let fuzz_dir = Path::new(env!("CARGO_MANIFEST_DIR"));

    write_seeds(
        &fuzz_dir.join("corpus/parse_cel"),
        seeds::CEL_SEEDS,
        "parse_cel",
    );

    write_seeds(
        &fuzz_dir.join("corpus/parse_scheme"),
        seeds::SCHEME_SEEDS,
        "parse_scheme",
    );
}

fn write_seeds(dir: &Path, seeds: &[(&str, &str)], target: &str) {
    fs::create_dir_all(dir).expect("failed to create corpus directory");

    let mut written = 0;
    let mut skipped = 0;

    for (name, content) in seeds {
        let path = dir.join(name);
        if path.exists() {
            skipped += 1;
        } else {
            fs::write(&path, content).expect("failed to write seed file");
            written += 1;
        }
    }

    println!("{target}: wrote {written} seeds, skipped {skipped} existing");
}
