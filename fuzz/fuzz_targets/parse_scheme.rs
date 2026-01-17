#![no_main]

use bumpalo::Bump;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        let arena = Bump::new();
        let _ = parpl::scheme::samples::scheme::read(s, &arena);
    }
});
