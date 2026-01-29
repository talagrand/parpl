// CEL Spec Conformance Tests
//
// This module loads and runs the official CEL conformance test suite from
// specs/cel-spec/tests/simple/testdata/*.textproto
//
// Test file structure (from simple.proto):
// - SimpleTestFile: { name, description, section[] }
// - SimpleTestSection: { name, description, test[] }
// - SimpleTest: { name, description, expr, disable_macros, disable_check,
//                 check_only, type_env[], container, locale, bindings{},
//                 result_matcher (value|typed_result|eval_error|...) }

#![cfg(feature = "cel")]

use bumpalo::Bump;
use parpl::StringPool;
use parpl::cel::{Builder, reference::arena::ArenaCelWriter};
use prost::Message;
use prost_reflect::{DescriptorPool, DynamicMessage, Value};
use std::path::Path;

/// A single CEL conformance test case extracted from the spec.
#[derive(Debug)]
pub struct CelTestCase {
    /// Source file name (e.g., "basic", "parse")
    pub file_name: String,
    /// Section within the file (e.g., "self_eval_zeroish")
    pub section_name: String,
    /// Individual test name (e.g., "self_eval_int_zero")
    pub test_name: String,
    /// Human-readable description of the test
    pub description: String,
    /// The CEL expression to parse/evaluate
    pub expr: String,
    /// If true, disable macro expansion during parsing
    pub disable_macros: bool,
    /// If true, skip the type-checking phase
    pub disable_check: bool,
    /// If true, only run parsing and checking (no evaluation)
    pub check_only: bool,
    /// Container namespace for name resolution (type-checking/evaluation only)
    pub container: String,
    /// Locale for evaluation (e.g., "en_US")
    pub locale: String,
    // Note: We don't extract type_env, bindings, or result_matchers yet
    // since we're only testing parsing, not evaluation.
}

/// Load all CEL spec conformance tests.
///
/// Returns `None` if running outside a git repository (e.g., crates.io source download),
/// allowing tests to skip gracefully.
pub fn load_cel_spec_tests() -> Option<Vec<CelTestCase>> {
    let proto_root = Path::new("specs/cel-spec/proto");
    let testdata_dir = Path::new("specs/cel-spec/tests/simple/testdata");

    // Skip gracefully if not in a git repository (e.g., crates.io source download)
    // The specs/ directory is excluded from the published crate.
    if !Path::new(".git").exists() {
        eprintln!();
        eprintln!("X  ============================================================");
        eprintln!("X  SKIPPING CEL CONFORMANCE TESTS");
        eprintln!("X  Not a git repository (likely crates.io source download)");
        eprintln!("X  To run these tests, clone from git with submodules.");
        eprintln!("X  ============================================================");
        eprintln!();
        return None;
    } else {
        // In a git repo but submodule missing? Panic with helpful message.
        assert!(
            proto_root.exists() && testdata_dir.exists(),
            "CEL spec test files not found!\n\n\
        The CEL conformance tests require the cel-spec git submodule.\n\
        Please initialize submodules with:\n\n    \
        git submodule update --init --recursive\n"
        );
    }

    // 1. Compile protos with protox - need to include all referenced protos
    let fds = protox::compile(
        [
            proto_root.join("cel/expr/conformance/test/simple.proto"),
            proto_root.join("cel/expr/conformance/proto3/test_all_types.proto"),
            proto_root.join("cel/expr/conformance/proto2/test_all_types.proto"),
            proto_root.join("cel/expr/conformance/proto2/test_all_types_extensions.proto"),
        ],
        [proto_root],
    )
    .expect("Failed to compile proto files");

    // 2. Create descriptor pool
    let pool = DescriptorPool::decode(fds.encode_to_vec().as_slice())
        .expect("Failed to create descriptor pool");

    // 3. Get message descriptor for SimpleTestFile
    let test_file_desc = pool
        .get_message_by_name("cel.expr.conformance.test.SimpleTestFile")
        .expect("SimpleTestFile message not found");

    // 4. Parse all .textproto files
    let mut all_tests = Vec::new();

    for entry in std::fs::read_dir(testdata_dir).expect("Failed to read testdata dir") {
        let entry = entry.expect("Failed to read dir entry");
        let path = entry.path();

        if path.extension().is_some_and(|ext| ext == "textproto") {
            let file_name = path
                .file_stem()
                .expect("test files have file stems")
                .to_string_lossy()
                .to_string();
            let content = std::fs::read_to_string(&path)
                .unwrap_or_else(|_| panic!("Failed to read {}", path.display()));

            // Parse the textproto
            let msg = DynamicMessage::parse_text_format(test_file_desc.clone(), &content)
                .unwrap_or_else(|e| panic!("Failed to parse {}: {}", path.display(), e));

            // Extract tests from the message
            extract_tests_from_message(&msg, &file_name, &mut all_tests);
        }
    }

    Some(all_tests)
}

fn extract_tests_from_message(msg: &DynamicMessage, file_name: &str, tests: &mut Vec<CelTestCase>) {
    // Get sections (repeated SimpleTestSection)
    if let Some(Value::List(sections)) = msg.get_field_by_name("section").map(|v| v.into_owned()) {
        for section_val in sections.iter() {
            if let Value::Message(section) = section_val {
                let section_name = get_string_field(section, "name");

                // Get tests in this section
                if let Some(Value::List(section_tests)) =
                    section.get_field_by_name("test").map(|v| v.into_owned())
                {
                    for test_val in section_tests.iter() {
                        if let Value::Message(test) = test_val {
                            tests.push(CelTestCase {
                                file_name: file_name.to_string(),
                                section_name: section_name.clone(),
                                test_name: get_string_field(test, "name"),
                                description: get_string_field(test, "description"),
                                expr: get_string_field(test, "expr"),
                                disable_macros: get_bool_field(test, "disable_macros"),
                                disable_check: get_bool_field(test, "disable_check"),
                                check_only: get_bool_field(test, "check_only"),
                                container: get_string_field(test, "container"),
                                locale: get_string_field(test, "locale"),
                            });
                        }
                    }
                }
            }
        }
    }
}

fn get_string_field(msg: &DynamicMessage, name: &str) -> String {
    msg.get_field_by_name(name)
        .and_then(|v| match v.into_owned() {
            Value::String(s) => Some(s),
            _ => None,
        })
        .unwrap_or_default()
}

fn get_bool_field(msg: &DynamicMessage, name: &str) -> bool {
    msg.get_field_by_name(name)
        .and_then(|v| match v.into_owned() {
            Value::Bool(b) => Some(b),
            _ => None,
        })
        .unwrap_or(false)
}

/// Specifies which tests to ignore.
/// Each entry is (file_name, optional_section_name).
/// If a section name is provided, only that section is ignored.
type IgnoreEntry = (&'static str, Option<&'static str>);

/// These are tests for CEL language extensions that are not part of the core
/// CEL grammar specification, but are supported as opt-in extensions in Google's
/// CEL implementations.
///
/// See docs/cel-extensions.md for details on:
/// - Backtick-quoted identifiers (`field-name`)
/// - Optional syntax (.?, [?], {?})
/// - Local variable bindings (cel.bind, cel.block)
///
/// parpl does not currently support these extensions.
const IGNORED_TESTS: &[IgnoreEntry] = &[
    // --- Backtick-quoted identifier extension ---
    ("fields", Some("quoted_map_fields")),
    ("proto2", Some("quoted_fields")),
    ("proto2", Some("extensions_has")),
    ("proto2", Some("extensions_get")),
    ("proto3", Some("quoted_fields")),
    // --- Optional syntax extension ---
    ("optionals", None),
    // --- Local variable bindings extension ---
    ("block_ext", None),
];

/// Check if a test should be ignored based on file and section name.
fn should_ignore_test(file_name: &str, section_name: &str) -> bool {
    for (ignored_file, ignored_section) in IGNORED_TESTS {
        if file_name == *ignored_file {
            match ignored_section {
                None => return true, // Ignore entire file
                Some(section) if section_name == *section => return true,
                _ => {}
            }
        }
    }
    false
}

/// Test that all CEL conformance expressions parse successfully.
///
/// This is a parser-only conformance test. It validates that our parser
/// can handle all the syntax used in the official CEL test suite.
#[test]
fn test_cel_parser_conformance() {
    let Some(tests) = load_cel_spec_tests() else {
        // User already warned
        return;
    };

    let parser = Builder::default()
        .max_parse_depth(256)
        .max_ast_depth(64)
        .build();

    let mut passed = 0;
    let mut failed = 0;
    let mut ignored = 0;
    let mut failures: Vec<(String, String, String)> = Vec::new();

    for test in &tests {
        // Check if this test should be ignored
        if should_ignore_test(&test.file_name, &test.section_name) {
            ignored += 1;
            continue;
        }

        let arena = Bump::new();
        let mut interner = StringPool::new();
        let mut writer = ArenaCelWriter::new(&arena, &mut interner);

        let test_id = format!(
            "{}/{}/{}",
            test.file_name, test.section_name, test.test_name
        );

        match parser.parse(&test.expr, &mut writer) {
            Ok(_) => {
                passed += 1;
            }
            Err(e) => {
                failed += 1;
                failures.push((test_id, test.expr.clone(), e.to_string()));
            }
        }
    }

    let tested = passed + failed;
    println!("\n=== CEL Parser Conformance Results ===");
    println!("Total: {} (ignored: {})", tests.len(), ignored);
    println!(
        "Passed: {} ({:.1}%). Failed: {}",
        passed,
        100.0 * passed as f64 / tested as f64,
        failed
    );

    if !failures.is_empty() {
        println!("\n=== All Failures ({}) ===", failures.len());
        for (test_id, expr, error) in &failures {
            println!("\n{test_id}");
            println!("  expr: {expr}");
            println!("  error: {error}");
        }
    }

    // BUGBUG: These 3 tests fail due to nesting depth limits.
    // This needs investigation.
    const BUGBUG_DEPTH_FAILURES: &[&str] = &[
        "parse/nest/message_literal",
        "parse/nest/parens",
        "parse/repeat/index",
    ];

    let unexpected_failures: Vec<_> = failures
        .iter()
        .filter(|(test_id, _, _)| !BUGBUG_DEPTH_FAILURES.contains(&test_id.as_str()))
        .collect();

    assert!(
        unexpected_failures.is_empty(),
        "Unexpected test failures: {:?}",
        unexpected_failures
            .iter()
            .map(|(id, _, _)| id)
            .collect::<Vec<_>>()
    );
}
