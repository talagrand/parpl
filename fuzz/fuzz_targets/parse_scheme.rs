#![no_main]

use bumpalo::Bump;
use libfuzzer_sys::fuzz_target;
use parpl::StringPool;

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        let arena = Bump::new();
        let mut interner = StringPool::new();
        let _ = parpl::scheme::reference::arena::read(s, &arena, &mut interner);
    }
});
