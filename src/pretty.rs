// AST Pretty-Printer
//
// This module provides human-readable formatting of CEL AST nodes for debugging.
// The output is designed to be clear and easy to read, showing the structure
// of parsed expressions.

use crate::ast::{Expr, ExprKind, Literal, QuoteStyle};
use std::fmt;

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
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_spans(mut self) -> Self {
        self.show_spans = true;
        self
    }

    pub fn with_indent(mut self, size: usize) -> Self {
        self.indent_size = size;
        self
    }
}

/// Pretty-print an expression
pub fn pretty_print(expr: &Expr) -> String {
    let config = PrettyConfig::default();
    pretty_print_with_config(expr, &config)
}

/// Pretty-print an expression with custom configuration
pub fn pretty_print_with_config(expr: &Expr, config: &PrettyConfig) -> String {
    let mut buf = String::new();
    print_expr(&mut buf, expr, 0, config);
    buf
}

fn print_expr(buf: &mut String, expr: &Expr, indent: usize, config: &PrettyConfig) {
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
            print_expr(buf, cond, indent + 2, config);
            buf.push_str(&format!("{}  if_true:\n", indent_str));
            print_expr(buf, if_true, indent + 2, config);
            buf.push_str(&format!("{}  if_false:\n", indent_str));
            print_expr(buf, if_false, indent + 2, config);
        }

        ExprKind::Binary(op, left, right) => {
            buf.push_str(&format!("Binary ({})\n", op));
            buf.push_str(&format!("{}  left:\n", indent_str));
            print_expr(buf, left, indent + 2, config);
            buf.push_str(&format!("{}  right:\n", indent_str));
            print_expr(buf, right, indent + 2, config);
        }

        ExprKind::Unary(op, expr) => {
            buf.push_str(&format!("Unary ({})\n", op));
            buf.push_str(&format!("{}  operand:\n", indent_str));
            print_expr(buf, expr, indent + 2, config);
        }

        ExprKind::Member(target, field, args) => {
            if let Some(args) = args {
                buf.push_str(&format!("MemberCall (.{})\n", field));
                buf.push_str(&format!("{}  target:\n", indent_str));
                print_expr(buf, target, indent + 2, config);
                buf.push_str(&format!("{}  args:\n", indent_str));
                for arg in args {
                    print_expr(buf, arg, indent + 2, config);
                }
            } else {
                buf.push_str(&format!("Member (.{})\n", field));
                buf.push_str(&format!("{}  target:\n", indent_str));
                print_expr(buf, target, indent + 2, config);
            }
        }

        ExprKind::Index(target, index) => {
            buf.push_str("Index\n");
            buf.push_str(&format!("{}  target:\n", indent_str));
            print_expr(buf, target, indent + 2, config);
            buf.push_str(&format!("{}  index:\n", indent_str));
            print_expr(buf, index, indent + 2, config);
        }

        ExprKind::Call(receiver, name, args) => {
            if let Some(recv) = receiver {
                buf.push_str(&format!("Call (.{})\n", name));
                buf.push_str(&format!("{}  receiver:\n", indent_str));
                print_expr(buf, recv, indent + 2, config);
            } else {
                buf.push_str(&format!("Call ({})\n", name));
            }
            if !args.is_empty() {
                buf.push_str(&format!("{}  args:\n", indent_str));
                for arg in args {
                    print_expr(buf, arg, indent + 2, config);
                }
            }
        }

        ExprKind::Ident(name) => {
            buf.push_str(&format!("Ident({})\n", name));
        }

        ExprKind::List(elements) => {
            buf.push_str("List\n");
            if !elements.is_empty() {
                buf.push_str(&format!("{}  elements:\n", indent_str));
                for elem in elements {
                    print_expr(buf, elem, indent + 2, config);
                }
            }
        }

        ExprKind::Map(entries) => {
            buf.push_str("Map\n");
            if !entries.is_empty() {
                buf.push_str(&format!("{}  entries:\n", indent_str));
                for (key, value) in entries {
                    buf.push_str(&format!("{}    key:\n", indent_str));
                    print_expr(buf, key, indent + 3, config);
                    buf.push_str(&format!("{}    value:\n", indent_str));
                    print_expr(buf, value, indent + 3, config);
                }
            }
        }

        ExprKind::Struct(receiver, path, fields) => {
            if let Some(recv) = receiver {
                buf.push_str(&format!("Struct (.{})\n", path.join(".")));
                buf.push_str(&format!("{}  receiver:\n", indent_str));
                print_expr(buf, recv, indent + 2, config);
            } else {
                buf.push_str(&format!("Struct ({})\n", path.join(".")));
            }
            if !fields.is_empty() {
                buf.push_str(&format!("{}  fields:\n", indent_str));
                for (name, value) in fields {
                    buf.push_str(&format!("{}    {}:\n", indent_str, name));
                    print_expr(buf, value, indent + 3, config);
                }
            }
        }

        ExprKind::Literal(lit) => {
            print_literal(buf, lit);
        }
    }
}

fn print_literal(buf: &mut String, lit: &Literal) {
    match lit {
        Literal::Int(s) => buf.push_str(&format!("Literal(Int({}))\n", s)),
        Literal::UInt(s) => buf.push_str(&format!("Literal(UInt({}))\n", s)),
        Literal::Float(s) => buf.push_str(&format!("Literal(Float({}))\n", s)),
        Literal::String(content, is_raw, style) => {
            let prefix = if *is_raw { "r" } else { "" };
            let quote = quote_char(*style);
            buf.push_str(&format!(
                "Literal(String({}{}{}{}))\n",
                prefix, quote, content, quote
            ));
        }
        Literal::Bytes(content, is_raw, style) => {
            let prefix = if *is_raw { "rb" } else { "b" };
            let quote = quote_char(*style);
            buf.push_str(&format!(
                "Literal(Bytes({}{}{}{}))\n",
                prefix, quote, content, quote
            ));
        }
        Literal::Bool(b) => buf.push_str(&format!("Literal(Bool({}))\n", b)),
        Literal::Null => buf.push_str("Literal(Null)\n"),
    }
}

fn quote_char(style: QuoteStyle) -> &'static str {
    match style {
        QuoteStyle::SingleQuote => "'",
        QuoteStyle::DoubleQuote => "\"",
        QuoteStyle::TripleSingleQuote => "'''",
        QuoteStyle::TripleDoubleQuote => "\"\"\"",
    }
}

// Implement Display for convenience
impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", pretty_print(self))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::build_ast;

    #[test]
    fn test_pretty_print_literal() {
        let ast = build_ast("42").unwrap();
        let output = pretty_print(&ast);
        assert!(output.contains("Literal(Int(42))"));
    }

    #[test]
    fn test_pretty_print_binary() {
        let ast = build_ast("1 + 2").unwrap();
        let output = pretty_print(&ast);
        assert!(output.contains("Binary (+)"));
        assert!(output.contains("Literal(Int(1))"));
        assert!(output.contains("Literal(Int(2))"));
    }

    #[test]
    fn test_pretty_print_ternary() {
        let ast = build_ast("true ? 1 : 2").unwrap();
        let output = pretty_print(&ast);
        assert!(output.contains("Ternary"));
        assert!(output.contains("condition:"));
        assert!(output.contains("if_true:"));
        assert!(output.contains("if_false:"));
    }

    #[test]
    fn test_pretty_print_list() {
        let ast = build_ast("[1, 2, 3]").unwrap();
        let output = pretty_print(&ast);
        assert!(output.contains("List"));
        assert!(output.contains("elements:"));
    }

    #[test]
    fn test_pretty_print_with_spans() {
        let ast = build_ast("42").unwrap();
        let config = PrettyConfig::new().with_spans();
        let output = pretty_print_with_config(&ast, &config);
        assert!(output.contains("[0..2]"));
    }

    #[test]
    fn test_pretty_print_nested() {
        let ast = build_ast("(1 + 2) * 3").unwrap();
        let output = pretty_print(&ast);
        assert!(output.contains("Binary (*)"));
        assert!(output.contains("Binary (+)"));
    }
}
