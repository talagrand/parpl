# R7RS Deviations

This document describes design choices compared to the R7RS specification.
We choose to prioritize correctness (rejecting potentially invalid input) over completeness
(accepting all valid input).

**Unicode Identifier Support (Conservative conformance)**
Spec Reference:** R7RS §7.1.1 (Lexical structure / Identifiers)

Identifier characters **may** come from these general Unicode character categories,
but implementations are not required to support all of them (and some are clearly not permitted)
by other parts of the spec.
A good reference of a reasonable character set to support is UAX #31 (Unicode Standard) for
identifiers. Scheme generally supports more than this because of the ability to define identifiers
for e.g. math operations. We implement a conservative but conforming identifier character set that:

| Category | Description | Examples | Supported by parser |
|----------|-------------|----------|--------------------------|
| Lu | Uppercase letters | A, B, Ω | ✅ Yes (initial & subsequent, via `is_alphabetic()`) |
| Ll | Lowercase letters | a, b, λ | ✅ Yes (initial & subsequent, via `is_alphabetic()`) |
| Lt | Titlecase letters | ǅ, ǈ | ✅ Yes (initial & subsequent, via `is_alphabetic()`) |
| Lm | Modifier letters | ʰ, ˢ | ✅ Yes (initial & subsequent, via `is_alphabetic()`) |
| Lo | Other letters | א, あ | ✅ Yes (initial & subsequent, via `is_alphabetic()`) |
| Mn | Non-spacing marks | ◌́, ◌̃ | ❌ No (rejected; `is_alphabetic`/`is_numeric` do not see these) |
| Mc | Spacing combining marks | ◌ः, ◌ा | ❌ No (rejected; `is_alphabetic`/`is_numeric` do not see these) |
| Me | Enclosing marks | ◌⃝, ◌⃞ | ❌ No (rejected; `is_alphabetic`/`is_numeric` do not see these) |
| Nd | Decimal digits | 0-9, ٠-٩ | ✅ Yes (subsequent only, via `is_numeric()` / `is_alphanumeric()`) |
| Nl | Letter numbers | Ⅰ, ⅰ | ✅ Yes (initial & subsequent, via `is_alphabetic()` / `is_numeric()`) |
| No | Other numbers | ², ³, ¼ | ✅ Yes (subsequent only, via `is_numeric()` / `is_alphanumeric()`) |
| Pd | Dash punctuation | ‐, – | ❌ No (beyond ASCII `-` which is handled by the ASCII rules) |
| Pc | Connector punctuation | _, ‿ | ✅ Partially (ASCII `_` only, via ASCII special-initial and delimiter rules) |
| Po | Other punctuation | •, ‣ | ✅ Partially (a small ASCII subset such as `! ? , . ; : @` via ASCII rules; non-ASCII Po rejected) |
| Sc | Currency symbols | $, €, £ | ✅ Partially (`$` only, via ASCII special-initial; other Sc rejected) |
| Sm | Math symbols | +, −, × | ✅ Partially (ASCII `+ < = > | ~` allowed by ASCII rules; other Sm rejected) |
| Sk | Modifier symbols | ^, ` | ✅ Partially (ASCII `^` and `` ` `` via ASCII rules; other Sk rejected) |
| So | Other symbols | ©, ®, ☺ | ❌ No (symbols beyond the ASCII special initials are rejected) |
| Co | Private use | U+E000–U+F8FF | ❌ No (rejected; not seen by `is_alphabetic`/`is_numeric`) |

Additionally, the spec allows:
- U+200C (Zero-Width Non-Joiner)
- U+200D (Zero-Width Joiner)

These two format characters are explicitly permitted by both R7RS and Unicode
UAX #31 because they are needed for correct spelling in certain scripts
(e.g., Persian, Hindi). We treat them as valid *subsequent* identifier characters.


**Fold-case directives (`#!fold-case` / `#!no-fold-case`)**
These are recognized by the lexer if configuration allowing them to be supported is used
(default is true). This can be disabled for more minimalistic scenarios.

When these are supported, they are recognized as  `<intertoken space>` and do not 
produce tokens - rather the lexer applies Unicode case folding itself making this
transparent to consuming code.
We do full Unicode case folding (`unicase` crate, using CaseFolding.txt from the Unicode standard),
but without normalization (not required by R7RS standard). This is equivalent to the R7RS
`string-foldcase` method.


**Datum comments (`#; <datum>`)**
These are lexed as `Token::DatumComment`. It is the responsibility of higher-level readers to consume
these and ignore the next datum, treating them as inter-token space.
Minimalistic readers can disable support for these as well.
