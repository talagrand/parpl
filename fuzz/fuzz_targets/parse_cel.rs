#![no_main]

use bumpalo::Bump;
use libfuzzer_sys::fuzz_target;
use parpl::{
    StringPool,
    cel::{CelParser, reference::arena::ArenaCelWriter},
};

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        let arena = Bump::new();
        let mut interner = StringPool::new();
        let mut writer = ArenaCelWriter::new(&arena, &mut interner);
        let parser = CelParser::default();
        let _ = parser.parse(s, &mut writer);
    }
});
