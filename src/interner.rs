// String interner for deduplicating string allocations
//
// This module provides string interning backed by a bumpalo arena.
// Identical strings are deduplicated, saving memory and enabling
// fast equality comparisons (pointer equality).

use bumpalo::Bump;
use std::collections::HashMap;

/// String interner with deduplication
///
/// Interns strings in an arena, ensuring that identical strings
/// share the same allocation. This is useful for identifiers,
/// field names, and string literals that may appear multiple times.
pub struct StringInterner<'arena> {
    arena: &'arena Bump,
    cache: HashMap<&'arena str, &'arena str>,
}

impl<'arena> StringInterner<'arena> {
    /// Create a new string interner backed by the given arena
    pub fn new(arena: &'arena Bump) -> Self {
        Self {
            arena,
            cache: HashMap::new(),
        }
    }

    /// Intern a string, returning a reference with arena lifetime
    ///
    /// If the string has been interned before, returns the existing
    /// reference. Otherwise, allocates in the arena and caches it.
    pub fn intern(&mut self, s: &str) -> &'arena str {
        // Check cache first
        if let Some(&interned) = self.cache.get(s) {
            return interned;
        }

        // Not found - allocate in arena
        let interned = self.arena.alloc_str(s);

        // Cache using the arena reference as both key and value
        // This works because the reference is stable for the arena's lifetime
        self.cache.insert(interned, interned);

        interned
    }

    /// Clear the interning cache (arena is NOT cleared)
    ///
    /// This is useful if you want to reset interning state without
    /// clearing the arena. After calling this, previously interned
    /// strings will be re-allocated on next intern.
    pub fn clear_cache(&mut self) {
        self.cache.clear();
    }

    /// Reset the interner with a new arena reference
    ///
    /// This clears the cache and updates the arena pointer.
    /// Used when the arena has been reset or moved.
    pub fn reset_arena(&mut self, arena: &'arena Bump) {
        self.cache.clear();
        self.arena = arena;
    }

    /// Get the number of unique strings interned
    #[allow(dead_code)] // May be used for debugging/stats
    pub fn len(&self) -> usize {
        self.cache.len()
    }

    /// Check if no strings have been interned
    #[allow(dead_code)] // May be used for debugging/stats
    pub fn is_empty(&self) -> bool {
        self.cache.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
    // Section: String Interning Tests
    // ============================================================

    test_cases! {
        test_intern_deduplicates: {
            let arena = Bump::new();
            let mut interner = StringInterner::new(&arena);

            let s1 = interner.intern("hello");
            let s2 = interner.intern("hello");
            let s3 = interner.intern("world");

            // Same string should return same reference
            assert!(std::ptr::eq(s1, s2));

            // Different strings should have different references
            assert!(!std::ptr::eq(s1, s3));

            // Should have 2 unique strings
            assert_eq!(interner.len(), 2);
        },

        test_intern_different_strings: {
            let arena = Bump::new();
            let mut interner = StringInterner::new(&arena);

            let s1 = interner.intern("foo");
            let s2 = interner.intern("bar");
            let s3 = interner.intern("baz");

            assert_eq!(s1, "foo");
            assert_eq!(s2, "bar");
            assert_eq!(s3, "baz");
            assert_eq!(interner.len(), 3);
        },

        test_clear_cache: {
            let arena = Bump::new();
            let mut interner = StringInterner::new(&arena);

            let s1 = interner.intern("hello");
            assert_eq!(interner.len(), 1);

            interner.clear_cache();
            assert_eq!(interner.len(), 0);

            // After clearing, interning the same string creates new allocation
            let s2 = interner.intern("hello");
            assert_eq!(s2, "hello");
            assert_eq!(interner.len(), 1);

            // Different references (new allocation)
            assert!(!std::ptr::eq(s1, s2));
        },
    }
}
