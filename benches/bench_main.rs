#![allow(clippy::unwrap_used)]

use bumpalo::Bump;
use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
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
// Recursive Factorial (using inline self-application pattern) - matches rulesxp
const SCHEME_FACTORIAL: &str =
    "((lambda (f x) (f f x)) (lambda (self n) (if (<= n 1) 1 (* n (self self (- n 1))))) 10)";

// 1K sample program - exercises deep nesting, lambdas, quotes, lists
const SCHEME_1K_SAMPLE: &str = r#"((lambda (f x) (f f x))
 (lambda (self n)
   (if (<= n 1)
       1
       (* n (self self (- n 1)))))
 10)

((lambda (compose)
   (compose
    (lambda (x) (* x 2))
    (lambda (x) (+ x 1))))
 (lambda (f g)
   (lambda (x) (f (g x)))))

((lambda (fold lst init f)
   ((lambda (go)
      (go go lst init))
    (lambda (self xs acc)
      (if (null? xs)
          acc
          (self self (cdr xs) (f acc (car xs)))))))
 '(1 2 3 4 5)
 0
 (lambda (acc x) (+ acc x)))

((lambda (map lst f)
   ((lambda (go)
      (go go lst))
    (lambda (self xs)
      (if (null? xs)
          '()
          (cons (f (car xs)) (self self (cdr xs)))))))
 '(10 20 30 40 50)
 (lambda (x) (* x x)))

((lambda (filter lst pred)
   ((lambda (go)
      (go go lst))
    (lambda (self xs)
      (if (null? xs)
          '()
          (if (pred (car xs))
              (cons (car xs) (self self (cdr xs)))
              (self self (cdr xs)))))))
 '(1 2 3 4 5 6 7 8 9 10)
 (lambda (x) (> x 5)))

((lambda (quicksort)
   (quicksort quicksort '(3 1 4 1 5 9 2 6 5 3 5)))
 (lambda (self lst)
   (if (null? lst)
       '()
       ((lambda (pivot rest)
          (append
           (self self (filter (lambda (x) (< x pivot)) rest))
           (cons pivot
                 (self self (filter (lambda (x) (>= x pivot)) rest)))))
        (car lst)
        (cdr lst)))))
"#;

// Additional parpl-specific test cases
const SCHEME_LAMBDA: &str = "(lambda (x y) (+ (* x x) (* y y)))";
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
        b.iter_batched_ref(
            Bump::new,
            |arena| {
                let _ = parpl::scheme::samples::scheme::read(black_box(SCHEME_SIMPLE), arena);
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("Nested", |b| {
        b.iter_batched_ref(
            Bump::new,
            |arena| {
                let _ = parpl::scheme::samples::scheme::read(black_box(SCHEME_NESTED), arena);
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("Factorial", |b| {
        b.iter_batched_ref(
            Bump::new,
            |arena| {
                let _ = parpl::scheme::samples::scheme::read(black_box(SCHEME_FACTORIAL), arena);
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("Lambda", |b| {
        b.iter_batched_ref(
            Bump::new,
            |arena| {
                let _ = parpl::scheme::samples::scheme::read(black_box(SCHEME_LAMBDA), arena);
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("Quote", |b| {
        b.iter_batched_ref(
            Bump::new,
            |arena| {
                let _ = parpl::scheme::samples::scheme::read(black_box(SCHEME_QUOTE), arena);
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("Complex", |b| {
        b.iter_batched_ref(
            Bump::new,
            |arena| {
                let _ = parpl::scheme::samples::scheme::read(black_box(SCHEME_COMPLEX), arena);
            },
            BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_minischeme_parsing(c: &mut Criterion) {
    let mut group = c.benchmark_group("MiniScheme Parsing");

    group.bench_function("Simple (+ 1 2)", |b| {
        b.iter(|| parpl::scheme::samples::minischeme::read(black_box(SCHEME_SIMPLE)))
    });

    group.bench_function("Nested", |b| {
        b.iter(|| parpl::scheme::samples::minischeme::read(black_box(SCHEME_NESTED)))
    });

    group.bench_function("Factorial", |b| {
        b.iter(|| parpl::scheme::samples::minischeme::read(black_box(SCHEME_FACTORIAL)))
    });

    group.bench_function("1K Sample", |b| {
        b.iter(|| parpl::scheme::samples::minischeme::read(black_box(SCHEME_1K_SAMPLE)))
    });

    group.finish();
}

criterion_group!(benches, bench_cel_parsing, bench_scheme_parsing, bench_minischeme_parsing);
criterion_main!(benches);
