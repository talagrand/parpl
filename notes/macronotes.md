# Macro Expansion and Label Resolution Strategy

## Overview

This document outlines the strategy for handling Scheme label definitions (`#n=`) and references (`#n#`) in the context of macro expansion. The goal is to support standard Scheme semantics (including cyclic structures) while providing flexibility in how the underlying data is represented (AST vs. Graph).

## The 3-Step Pipeline

Conceptually, processing Scheme code involves three steps:

1.  **Parse:** The Reader consumes text and produces a "Raw AST". This AST contains explicit nodes for label definitions and references.
2.  **Resolve Labels:** The system establishes the graph topology, resolving references to their definitions.
3.  **Macro Expansion:** The Expander traverses the code, matching patterns and rewriting syntax.

## The Challenge

Macro expanders operate on the *structure* of the code (lists, vectors, identifiers). They should not be concerned with the serialization details of that structure (like label markers).

If an expander operates on the "Raw AST" (Phase 1 output) directly:
*   **Pattern Matching Fails:** A pattern like `(list a b)` might fail to match `#1=(list a b)` because of the intervening label node.
*   **Topology Breaks:** A macro that duplicates a syntax object (e.g., `(define-syntax dup (syntax-rules () ((_ x) (list x x))))`) might duplicate a label definition `#1=(...)`. This results in two distinct definitions of `#1=`, or a reference `#1#` being copied without its corresponding definition, breaking the intended graph structure.

Therefore, **Macro Expansion must operate on the Resolved View (Phase 2 output)**.

## Implementation Strategy: JIT Label Resolution

To support this without forcing every implementation to convert their AST into a heavy `Rc<RefCell<...>>` graph immediately, we leverage the `DatumInspector` trait and its `Child` abstraction.

We support two modes of operation for Phase 2:

### Option A: "Baked" Graph (Materialized Resolution)
The caller converts the Raw AST into a pointer-based graph (e.g., using `Rc` or an Arena).
*   **Representation:** `Rc<Node>` or `ArenaIndex`.
*   **Resolution:** Done once, eagerly.
*   **Inspector:** `DatumInspector` simply follows the pointers.

### Option B: "JIT" View (Virtual Resolution)
The caller keeps the Raw AST but wraps it in a smart "Cursor" or "View".
*   **Representation:** `Cursor<'a> { node: &'a AstNode, context: &'a LabelTable }`.
*   **Resolution:** Done lazily, on-the-fly.
*   **Inspector:**
    *   When `kind()` is called on a `LabelDef` node, the cursor transparently delegates to the inner content.
    *   When `kind()` is called on a `LabelRef` node, the cursor looks up the target in the `LabelTable` and behaves as if it *is* that target.
    *   The `Child` associated type allows the cursor to carry the `LabelTable` context down to children during traversal.

## The Role of `DatumInspector`

The `DatumInspector` trait is designed to support both options via the `Child` Generic Associated Type (GAT):

```rust
trait DatumInspector {
    // ...
    type Child<'a>: DatumInspector where Self: 'a;
    
    fn as_pair<'a>(&'a self) -> Option<(Self::Child<'a>, Self::Child<'a>)>;
    // ...
}
```

*   For **Option A**, `Child<'a>` is simply `&'a Node` (or `Rc<Node>`).
*   For **Option B**, `Child<'a>` is the `Cursor<'a>` struct described above.

## Benefits

1.  **Standards Conformance:** The macro expander sees the correct graph topology (including cycles) regardless of the underlying representation.
2.  **Caller Choice:** Embedders can choose the trade-off that suits them:
    *   **Performance/Caching:** "Bake" the graph if it will be evaluated many times.
    *   **Low Memory/Tooling:** Use the JIT view to avoid allocating a secondary graph structure, useful for one-off scripts or lightweight analysis tools.
3.  **Unified Expander:** The macro expander implementation is generic over `DatumInspector` and does not need to know which strategy is being used.
