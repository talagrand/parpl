//! Tests to verify that version numbers and MSRV mentioned in README.md
//! match the values in Cargo.toml.

fn get_version_from_cargo_toml(prefix: &str) -> String {
    let cargo_toml = std::fs::read_to_string("Cargo.toml").expect("Could not read Cargo.toml");
    let error_msg = format!("Could not find {prefix} in Cargo.toml");

    // Extract version from Cargo.toml
    cargo_toml
        .lines()
        .find(|line| line.starts_with(prefix))
        .and_then(|line| line.split('"').nth(1))
        .expect(&error_msg)
        .to_owned()
}

fn assert_readme_contains(expected: &str) {
    let readme = std::fs::read_to_string("README.md").expect("Could not read README.md");
    assert!(
        readme.contains(expected),
        "README.md should contain \"{expected}\"",
    );
}

/// Verify that README.md mentions the correct MSRV from Cargo.toml.
#[test]
fn readme_mentions_correct_msrv() {
    let msrv = get_version_from_cargo_toml("rust-version");

    assert_readme_contains(&format!("Requires Rust {msrv} or later."));
}

/// Verify that README.md mentions a compatible crate version.
/// The README uses "0.1" format while Cargo.toml has "0.1.0".
#[test]
fn readme_mentions_correct_version() {
    // Extract version from Cargo.toml (e.g., "0.1.0")
    let crate_version = get_version_from_cargo_toml("version = ");

    // Extract major.minor (e.g., "0.1" from "0.1.0")
    let major_minor_crate_version = crate_version
        .rsplit_once('.')
        .expect("Invalid version format")
        .0;

    assert_readme_contains(&format!(
        "parpl = {{ version = \"{major_minor_crate_version}\""
    ));
}
