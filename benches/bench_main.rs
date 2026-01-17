#![allow(clippy::unwrap_used)]

use bumpalo::Bump;
use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;

// CEL expressions of varying complexity
const CEL_SIMPLE: &str = "1 + 2";
const CEL_ARITHMETIC: &str = "((5 * 2) + 3) / 2 - 1";
const CEL_COMPARISON: &str = "x > 10 && y < 20 || z == 0";
const CEL_FUNCTION_CALL: &str = "size(items) > 0 && items[0].name.startsWith('test')";
const CEL_TERNARY: &str = "status == 'active' ? priority * 2 : priority";
const CEL_COMPLEX: &str = r#"
    request.auth.claims.email.endsWith('@example.com') &&
    request.method in ['GET', 'POST'] &&
    size(request.headers['Authorization']) > 0
"#;

// Scheme expressions of varying complexity
const SCHEME_SIMPLE: &str = "(+ 1 2)";
const SCHEME_NESTED: &str = "(if (> (* 5 2) 8) (max 10 5 20) 0)";
const SCHEME_LAMBDA: &str = "(lambda (x y) (+ (* x x) (* y y)))";
const SCHEME_DEFINE: &str = "(define (factorial n) (if (<= n 1) 1 (* n (factorial (- n 1)))))";
const SCHEME_QUOTE: &str = "'(a b c (d e f) (g (h i)))";
const SCHEME_COMPLEX: &str = r#"
    (let ((x 10)
          (y 20))
      (cond ((> x y) 'greater)
            ((< x y) 'lesser)
            (else 'equal)))
"#;

fn bench_cel_parsing(c: &mut Criterion) {
    let mut group = c.benchmark_group("CEL Parsing");

    group.bench_function("Simple (1 + 2)", |b| {
        b.iter(|| parpl::cel::parse(black_box(CEL_SIMPLE)))
    });

    group.bench_function("Arithmetic", |b| {
        b.iter(|| parpl::cel::parse(black_box(CEL_ARITHMETIC)))
    });

    group.bench_function("Comparison", |b| {
        b.iter(|| parpl::cel::parse(black_box(CEL_COMPARISON)))
    });

    group.bench_function("Function Call", |b| {
        b.iter(|| parpl::cel::parse(black_box(CEL_FUNCTION_CALL)))
    });

    group.bench_function("Ternary", |b| {
        b.iter(|| parpl::cel::parse(black_box(CEL_TERNARY)))
    });

    group.bench_function("Complex", |b| {
        b.iter(|| parpl::cel::parse(black_box(CEL_COMPLEX)))
    });

    group.finish();
}

fn bench_scheme_parsing(c: &mut Criterion) {
    let mut group = c.benchmark_group("Scheme Parsing");

    group.bench_function("Simple (+ 1 2)", |b| {
        b.iter(|| {
            let arena = Bump::new();
            let _ = parpl::scheme::samples::scheme::read(black_box(SCHEME_SIMPLE), &arena);
        })
    });

    group.bench_function("Nested", |b| {
        b.iter(|| {
            let arena = Bump::new();
            let _ = parpl::scheme::samples::scheme::read(black_box(SCHEME_NESTED), &arena);
        })
    });

    group.bench_function("Lambda", |b| {
        b.iter(|| {
            let arena = Bump::new();
            let _ = parpl::scheme::samples::scheme::read(black_box(SCHEME_LAMBDA), &arena);
        })
    });

    group.bench_function("Define", |b| {
        b.iter(|| {
            let arena = Bump::new();
            let _ = parpl::scheme::samples::scheme::read(black_box(SCHEME_DEFINE), &arena);
        })
    });

    group.bench_function("Quote", |b| {
        b.iter(|| {
            let arena = Bump::new();
            let _ = parpl::scheme::samples::scheme::read(black_box(SCHEME_QUOTE), &arena);
        })
    });

    group.bench_function("Complex", |b| {
        b.iter(|| {
            let arena = Bump::new();
            let _ = parpl::scheme::samples::scheme::read(black_box(SCHEME_COMPLEX), &arena);
        })
    });

    group.finish();
}

criterion_group!(benches, bench_cel_parsing, bench_scheme_parsing);
criterion_main!(benches);
