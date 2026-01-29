# CEL Parser Extensions

This is a summary of existing CEL language extensions.
They are not part of the core CEL grammar, but are supported by the official
Google implementations (cel-go, cel-cpp, cel-java) as opt-in parser features.

*parpl does not currently support these extensions.*

---

## 1. Optional Syntax Extension

**Official Proposal**: [cel-spec/wiki/proposal-246](https://github.com/google/cel-spec/wiki/proposal-246)

Optional syntax introduces first-class support for optional values in CEL, allowing:
- Conditional field selection with `?.`
- Conditional indexing with `[?]`
- Conditional field/element setting with `?` prefix

### Syntax

| Syntax | Description |
|--------|-------------|
| `msg.?field` | Returns `optional.of(msg.field)` if field exists, else `optional.none()` |
| `map[?key]` | Returns `optional.of(map[key])` if key exists, else `optional.none()` |
| `list[?index]` | Returns `optional.of(list[index])` if index valid, else `optional.none()` |
| `Msg{?field: expr}` | Conditionally set field if `expr` (type `optional(T)`) has value |
| `{?key: expr}` | Conditionally set map key if `expr` has value |
| `[?a, ?b]` | Optional list elements (only include if value present) |

### Functions & Macros

- `optional.of(T) -> optional(T)` - Wrap value in optional
- `optional.none() -> optional(T)` - Create empty optional
- `optional.ofNonZeroValue(T) -> optional(T)` - None for zero/null values
- `.value() -> T` - Unwrap (error if none)
- `.hasValue() -> bool` - Test if has value
- `.or(optional(T)) -> optional(T)` - First with value (short-circuits)
- `.orValue(T) -> T` - Value or default (short-circuits)
- `.optMap(var, expr)` - Transform if present
- `.optFlatMap(var, expr)` - Transform to another optional

### Implementation Support

| Implementation | Parser Option |
|----------------|---------------|
| cel-go | `parser.EnableOptionalSyntax(true)` |
| cel-cpp | `ParserOptions.enable_optional_syntax = true` |
| cel-java | `CelOptions.enableOptionalSyntax(true)` |

All implementations default to disabled.

---

## 2. Backtick-Quoted Identifiers

Backtick-quoted identifiers allow field names with non-standard characters
(dashes, dots, spaces, slashes) to be accessed in CEL expressions. This is
useful for JSON data with unconventional field names or proto fields that
conflict with reserved words.

### Syntax

```cel
msg.`field-with-dashes`
Msg{`field.with.dots`: value}
has(a.`b/c`)
map.`in`     // Access field named "in" (reserved word)
```

### Grammar (from ANTLR)

```antlr
ESC_IDENTIFIER : '`' (LETTER | DIGIT | '_' | '.' | '-' | '/' | ' ')+ '`';
```

**Allowed characters inside backticks:**
- Letters (a-z, A-Z)
- Digits (0-9)
- Underscore, dot, dash, slash, space

**Restrictions:**
- Only for field selection (`a.\`b\``) and message creation (`Msg{\`b\`: v}`)
- Cannot be used as standalone identifiers (`` `a.b` `` at expression root is invalid)
- Cannot contain tabs, `@`, `$`, or other special characters

### Specification

**No formal CEL proposal** - this is an implementation extension.

Grammar defined in the ANTLR `.g4` files of each implementation:
- cel-go: `parser/gen/CEL.g4`
- cel-cpp: `parser/internal/Cel.g4`
- cel-java: `parser/src/main/java/dev/cel/parser/gen/CEL.g4`

### Implementation Support

| Implementation | Parser Option |
|----------------|---------------|
| cel-go | `parser.EnableIdentEscapeSyntax(true)` |
| cel-cpp | `ParserOptions.enable_quoted_identifiers = true` |
| cel-java | `CelOptions.enableQuotedIdentifierSyntax(true)` |

All implementations default to disabled.

---

## 3. Local Variable Bindings (`cel.bind` / `cel.block`)

The bindings extension provides local variable binding within expressions,
allowing intermediate values to be computed once and reused.

### Syntax

```cel
cel.bind(<varName>, <initExpr>, <resultExpr>)
```

### Examples

```cel
// Avoid recomputing expensive expression
cel.bind(a, 'hello',
  cel.bind(b, 'world', a + b + b + a))  // "helloworldworldhello"

// Avoid list allocation in comprehension
cel.bind(valid_values, [a, b, c],
  [d, e, f].exists(elem, elem in valid_values))
```

### Specification

**Documentation**: [cel-go/ext/README.md - Bindings](https://github.com/google/cel-go/blob/master/ext/README.md#bindings)

This is implemented as a **macro extension**, not a parser syntax change.
The `cel.block` variant is similar but supports multiple bindings.

### Implementation Support

| Implementation | How to Enable |
|----------------|---------------|
| cel-go | `ext.Bindings()` library |
| cel-cpp | `cel::extensions::RegisterBindingsMacros()` |
| cel-java | `CelExtensions.bindings()` library |

---

## References

- [CEL Language Definition](https://github.com/google/cel-spec/blob/master/doc/langdef.md) - Core grammar
- [Proposal 246: Optional Values](https://github.com/google/cel-spec/wiki/proposal-246) - Optional syntax spec
- [cel-go Extensions](https://github.com/google/cel-go/blob/master/ext/README.md) - Extension documentation
- [cel-go](https://github.com/google/cel-go), [cel-cpp](https://github.com/google/cel-cpp), [cel-java](https://github.com/google/cel-java) - Official implementations
