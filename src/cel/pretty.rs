// AST Pretty-Printer
//
// This module provides human-readable formatting of CEL AST nodes for debugging.
// The output is designed to be clear and easy to read, showing the structure
// of parsed expressions.

use crate::{
    cel::ast::{Expr, ExprKind, Literal},
    common::{Interner, StringPoolId},
};

/// Configuration for pretty-printing
#[derive(Debug, Clone)]
pub struct PrettyConfig {
    /// Number of spaces per indentation level
    pub indent_size: usize,
    /// Whether to show span information
    pub show_spans: bool,
}

impl Default for PrettyConfig {
    fn default() -> Self {
        Self {
            indent_size: 2,
            show_spans: false,
        }
    }
}

impl PrettyConfig {
    pub fn with_spans(mut self) -> Self {
        self.show_spans = true;
        self
    }

    pub fn with_indent(mut self, size: usize) -> Self {
        self.indent_size = size;
        self
    }
}

/// Pretty-print an expression using an interner to resolve IDs back to strings.
pub fn pretty_print<I>(expr: &Expr, interner: &I) -> String
where
    I: Interner<Id = StringPoolId> + ?Sized,
{
    let config = PrettyConfig::default();
    pretty_print_with_config(expr, &config, interner)
}

/// Pretty-print an expression with custom configuration.
pub fn pretty_print_with_config<I>(expr: &Expr, config: &PrettyConfig, interner: &I) -> String
where
    I: Interner<Id = StringPoolId> + ?Sized,
{
    let mut buf = String::new();
    print_expr(&mut buf, expr, 0, config, interner);
    buf
}

#[inline]
fn fmt_id<I>(id: &StringPoolId, interner: &I) -> String
where
    I: Interner<Id = StringPoolId> + ?Sized,
{
    interner.resolve(id).unwrap_or("<unresolved>").to_string()
}

fn print_expr<I>(buf: &mut String, expr: &Expr, indent: usize, config: &PrettyConfig, interner: &I)
where
    I: Interner<Id = StringPoolId> + ?Sized,
{
    let indent_str = " ".repeat(indent * config.indent_size);

    if config.show_spans {
        buf.push_str(&format!(
            "{}[{}..{}] ",
            indent_str, expr.span.start, expr.span.end
        ));
    } else {
        buf.push_str(&indent_str);
    }

    match &expr.kind {
        ExprKind::Ternary(cond, if_true, if_false) => {
            buf.push_str("Ternary\n");
            buf.push_str(&format!("{}  condition:\n", indent_str));
            print_expr(buf, cond, indent + 2, config, interner);
            buf.push_str(&format!("{}  if_true:\n", indent_str));
            print_expr(buf, if_true, indent + 2, config, interner);
            buf.push_str(&format!("{}  if_false:\n", indent_str));
            print_expr(buf, if_false, indent + 2, config, interner);
        }

        ExprKind::Binary(op, left, right) => {
            buf.push_str(&format!("Binary ({})\n", op));
            buf.push_str(&format!("{}  left:\n", indent_str));
            print_expr(buf, left, indent + 2, config, interner);
            buf.push_str(&format!("{}  right:\n", indent_str));
            print_expr(buf, right, indent + 2, config, interner);
        }

        ExprKind::Unary(op, expr) => {
            buf.push_str(&format!("Unary ({})\n", op));
            buf.push_str(&format!("{}  operand:\n", indent_str));
            print_expr(buf, expr, indent + 2, config, interner);
        }

        ExprKind::Member(target, field, args) => {
            let field_str = fmt_id(field, interner);
            if let Some(args) = args {
                buf.push_str(&format!("MemberCall (.{})\n", field_str));
                buf.push_str(&format!("{}  target:\n", indent_str));
                print_expr(buf, target, indent + 2, config, interner);
                buf.push_str(&format!("{}  args:\n", indent_str));
                for arg in *args {
                    print_expr(buf, arg, indent + 2, config, interner);
                }
            } else {
                buf.push_str(&format!("Member (.{})\n", field_str));
                buf.push_str(&format!("{}  target:\n", indent_str));
                print_expr(buf, target, indent + 2, config, interner);
            }
        }

        ExprKind::Index(target, index) => {
            buf.push_str("Index\n");
            buf.push_str(&format!("{}  target:\n", indent_str));
            print_expr(buf, target, indent + 2, config, interner);
            buf.push_str(&format!("{}  index:\n", indent_str));
            print_expr(buf, index, indent + 2, config, interner);
        }

        ExprKind::Call(receiver, name, args) => {
            let name_str = fmt_id(name, interner);
            if let Some(recv) = receiver {
                buf.push_str(&format!("Call (.{})\n", name_str));
                buf.push_str(&format!("{}  receiver:\n", indent_str));
                print_expr(buf, recv, indent + 2, config, interner);
            } else {
                buf.push_str(&format!("Call ({})\n", name_str));
            }
            if !args.is_empty() {
                buf.push_str(&format!("{}  args:\n", indent_str));
                for arg in *args {
                    print_expr(buf, arg, indent + 2, config, interner);
                }
            }
        }

        ExprKind::Ident(name) => {
            let name_str = fmt_id(name, interner);
            buf.push_str(&format!("Ident({})\n", name_str));
        }

        ExprKind::List(elements) => {
            buf.push_str("List\n");
            if !elements.is_empty() {
                buf.push_str(&format!("{}  elements:\n", indent_str));
                for elem in *elements {
                    print_expr(buf, elem, indent + 2, config, interner);
                }
            }
        }

        ExprKind::Map(entries) => {
            buf.push_str("Map\n");
            if !entries.is_empty() {
                buf.push_str(&format!("{}  entries:\n", indent_str));
                for (key, value) in *entries {
                    buf.push_str(&format!("{}    key:\n", indent_str));
                    print_expr(buf, key, indent + 3, config, interner);
                    buf.push_str(&format!("{}    value:\n", indent_str));
                    print_expr(buf, value, indent + 3, config, interner);
                }
            }
        }

        ExprKind::Struct(receiver, path, fields) => {
            let path_str = path
                .iter()
                .map(|id| fmt_id(id, interner))
                .collect::<Vec<_>>()
                .join(".");
            if let Some(recv) = receiver {
                buf.push_str(&format!("Struct (.{})\n", path_str));
                buf.push_str(&format!("{}  receiver:\n", indent_str));
                print_expr(buf, recv, indent + 2, config, interner);
            } else {
                buf.push_str(&format!("Struct ({})\n", path_str));
            }
            if !fields.is_empty() {
                buf.push_str(&format!("{}  fields:\n", indent_str));
                for (name, value) in *fields {
                    let field_name = fmt_id(name, interner);
                    buf.push_str(&format!("{}    {}:\n", indent_str, field_name));
                    print_expr(buf, value, indent + 3, config, interner);
                }
            }
        }

        ExprKind::Literal(lit) => {
            print_literal(buf, lit, interner);
        }
    }
}

fn print_literal<'a, I>(buf: &mut String, lit: &Literal<StringPoolId, &'a [u8]>, interner: &I)
where
    I: Interner<Id = StringPoolId> + ?Sized,
{
    match lit {
        Literal::Int(val) => buf.push_str(&format!("Literal(Int({}))\n", val)),
        Literal::UInt(val) => buf.push_str(&format!("Literal(UInt({}))\n", val)),
        Literal::Float(val) => buf.push_str(&format!("Literal(Float({}))\n", val)),
        Literal::String(id) => {
            let s = interner.resolve(id).unwrap_or("<unresolved>");
            let escaped = escape_for_display(s);
            buf.push_str(&format!("Literal(String(\"{}\"))\n", escaped));
        }
        Literal::Bytes(bytes) => {
            // Convert bytes to displayable string, escaping non-printable bytes
            let escaped = bytes
                .iter()
                .flat_map(|&b| {
                    if b.is_ascii_graphic() || b == b' ' {
                        vec![b as char]
                    } else {
                        // Show as \xHH for non-printable bytes
                        format!("\\x{:02x}", b).chars().collect::<Vec<_>>()
                    }
                })
                .collect::<String>();
            buf.push_str(&format!("Literal(Bytes(b\"{}\"))\n", escaped));
        }
        Literal::Bool(b) => buf.push_str(&format!("Literal(Bool({}))\n", b)),
        Literal::Null => buf.push_str("Literal(Null)\n"),
    }
}

/// Escape string content for display (reverse of escape processing)
fn escape_for_display(s: &str) -> String {
    s.chars()
        .flat_map(|c| match c {
            '\n' => vec!['\\', 'n'],
            '\t' => vec!['\\', 't'],
            '\r' => vec!['\\', 'r'],
            '\\' => vec!['\\', '\\'],
            '"' => vec!['\\', '"'],
            c if c.is_control() => format!("\\x{:02X}", c as u32).chars().collect(),
            c => vec![c],
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cel::{Builder, test_util::*};

    macro_rules! test_cases {
        ($($name:ident: $test:expr),* $(,)?) => {
            $(
                #[test]
                fn $name() {
                    $test
                }
            )*
        };
    }

    // ============================================================
    // Section: Pretty Printing Tests
    // ============================================================

    test_cases! {
        test_pretty_print_literal: {
            let output = parse_and_pretty("42");
            assert!(output.contains("Literal(Int(42))"));
        },

        test_pretty_print_ident_resolves: {
            let output = parse_and_pretty("foo");
            assert!(output.contains("Ident(foo)"));
        },

        test_pretty_print_string_resolves: {
            let output = parse_and_pretty("\"hi\"");
            assert!(output.contains("Literal(String(\"hi\"))"));
        },

        test_pretty_print_binary: {
            let output = parse_and_pretty("1 + 2");
            assert!(output.contains("Binary (+)"));
            assert!(output.contains("Literal(Int(1))"));
            assert!(output.contains("Literal(Int(2))"));
        },

        test_pretty_print_ternary: {
            let output = parse_and_pretty("true ? 1 : 2");
            assert!(output.contains("Ternary"));
        },

        test_pretty_print_list: {
            let output = parse_and_pretty("[1, 2, 3]");
            assert!(output.contains("List"));
            assert!(output.contains("elements:"));
        },

        test_pretty_print_nested: {
            let output = parse_and_pretty("(1 + 2) * 3");
            assert!(output.contains("Binary (*)"));
            assert!(output.contains("Binary (+)"));
        },
    }

    // ============================================================
    // Section: Configuration Tests
    // ============================================================

    test_cases! {
        test_pretty_print_with_spans: {
            Builder::default()
                .parse_scoped("42", |ctx| {
                    let config = PrettyConfig::default().with_spans();
                    let output = pretty_print_with_config(ctx.ast()?, &config, ctx);
                    assert!(output.contains("[0..2]"));
                    Ok(())
                })
                .unwrap();
        },

        test_pretty_print_custom_indent: {
            Builder::default()
                .parse_scoped("1 + 2", |ctx| {
                    let config = PrettyConfig::default().with_indent(4);
                    let output = pretty_print_with_config(ctx.ast()?, &config, ctx);
                    assert!(output.contains("Binary (+)"));
                    Ok(())
                })
                .unwrap();
        },
    }
}
