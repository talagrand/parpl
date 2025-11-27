# R7RS Deviations

This document describes known deviations from the R7RS specification in the
`newparser` implementation. These are intentional choices, usually made to
prioritize correctness (rejecting potentially invalid input) over completeness
(accepting all valid input).

## 1. Unicode Identifier Support (Conservative)

**Spec Reference:** R7RS §7.1.1 (Lexical structure / Identifiers)

### What R7RS Requires

The R7RS specification allows identifier characters beyond the basic ASCII set
to come from these Unicode general categories:

| Category | Description | Examples |
|----------|-------------|----------|
| Lu | Uppercase letters | A, B, Ω |
| Ll | Lowercase letters | a, b, λ |
| Lt | Titlecase letters | ǅ, ǈ |
| Lm | Modifier letters | ʰ, ˢ |
| Lo | Other letters | א, あ |
| Mn | Non-spacing marks | ◌́, ◌̃ |
| Mc | Spacing combining marks | ◌ः, ◌ा |
| Me | Enclosing marks | ◌⃝, ◌⃞ |
| Nd | Decimal digits | 0-9, ٠-٩ |
| Nl | Letter numbers | Ⅰ, ⅰ |
| No | Other numbers | ², ³, ¼ |
| Pd | Dash punctuation | ‐, – |
| Pc | Connector punctuation | _, ‿ |
| Po | Other punctuation | •, ‣ |
| Sc | Currency symbols | $, €, £ |
| Sm | Math symbols | +, −, × |
| Sk | Modifier symbols | ^, ` |
| So | Other symbols | ©, ®, ☺ |
| Co | Private use | U+E000–U+F8FF |

Additionally, the spec allows:
- U+200C (Zero-Width Non-Joiner)
- U+200D (Zero-Width Joiner)

### What Rust stdlib Provides

Rust's `char` type provides only limited Unicode classification:

| Method | Categories Covered |
|--------|-------------------|
| `is_alphabetic()` | Lu, Ll, Lt, Lm, Lo, Nl |
| `is_numeric()` | Nd, Nl, No |

### What We Cannot Detect

Without additional dependencies (e.g., `unicode-general-category` crate), we
cannot reliably detect:

- **Marks (Mn, Mc, Me)** — combining characters
- **Punctuation (Pd, Pc, Po)** — dashes, connectors, bullets
- **Symbols (Sc, Sm, Sk, So)** — currency, math, modifier symbols
- **Private Use (Co)** — private use area characters
- **Special joiners (U+200C, U+200D)** — zero-width joiners

### Our Conservative Approach

We implement a **conservative** identifier checker that:

1. ✅ Accepts characters verifiable via `is_alphabetic()` as `<initial>` or `<subsequent>`
2. ✅ Accepts ASCII special initials: `! $ % & * / : < = > ? ^ _ ~`
3. ✅ Accepts digits (`0-9`) and sign/dot characters as `<subsequent>` only
4. ❌ Rejects anything we cannot positively classify

### Consequences

| Input | R7RS | newparser | Reason |
|-------|------|-----------|--------|
| `λ` | ✅ valid | ✅ valid | Lu detected via `is_alphabetic()` |
| `α-beta` | ✅ valid | ✅ valid | Greek letters detected |
| `•item` | ✅ valid | ❌ rejected | Bullet (Po) not detectable |
| `€price` | ✅ valid | ❌ rejected | Euro sign (Sc) not detectable |
| `x⃗` | ✅ valid | ❌ rejected | Combining mark (Me) not detectable |

### Rationale

**False negatives over false positives**: The lexer will reject some valid R7RS
programs (those using symbols, marks, or private-use characters in identifiers),
but it will never accept an invalid identifier. This is consistent with the
project's philosophy of erring on the side of rejecting potentially invalid
input.

### Future Work

To achieve full R7RS Unicode compliance, add a dependency such as
`unicode-general-category` that exposes the full Unicode character category
information. This would enable proper detection of all spec-required categories.

---

## 2. Fold-Case Directive (Recognized but Ignored)

**Spec Reference:** R7RS §2.1 (Identifiers)

### Deviation

The directives `#!fold-case` and `#!no-fold-case` are recognized and validated
syntactically, but their semantics are **not implemented**. The reader remains
case-sensitive throughout.

### Consequence

Programs relying on case-folding (e.g., `(DEFINE X 1)` being equivalent to
`(define x 1)`) will not work as expected. Identifiers `FOO` and `foo` are
treated as distinct.

### Rationale

Case-folding adds complexity to the lexer state machine and interacts with
Unicode in non-trivial ways. Given the conservative Unicode handling above,
implementing full case-folding would require additional infrastructure.

---

## 3. Datum Comments (Parser-Level Handling)

**Spec Reference:** R7RS §2.2 (Whitespace and comments)

### Deviation

R7RS specifies that `#; <datum>` is intertoken space—meaning the lexer should
skip both the `#;` prefix and the following datum entirely. However, recognizing
what constitutes a `<datum>` requires a full parser; the lexer alone cannot know
where the datum ends (e.g., for nested lists or quoted forms).

### Our Approach

The lexer emits a `Token::DatumComment` when it encounters `#;`. The parser-level
`TokenStream` wrapper then consumes this token and recursively skips the following
datum, providing a clean token stream to higher-level parsing code.

This approach:
- Keeps the lexer simple and context-free
- Handles all datum forms correctly (lists, vectors, quoted forms, nested datum comments)
- Follows the spirit of R7RS (datum comments are invisible to the parser)

### Implementation

See `TokenStream` in `src/lib.rs`, which provides:
- `peek()` / `next_token()` — automatically skip datum comments
- `skip_one_datum()` — recursive datum skipper for lists, vectors, quotes, etc.
