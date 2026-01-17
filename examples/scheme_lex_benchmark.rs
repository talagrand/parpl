use parpl::scheme::lex::lex;

fn main() {
    // A mix of tokens to exercise the lexer.
    // Note: Identifiers are not yet implemented, so we only use supported literals and punctuation.
    let source = r#"
        ; Booleans
        #t #f #true #false
        
        ; Numbers
        123 -456 3.14159 .5 1.2e3 1e-4
        #x10 #o77 #b1010
        1+2i 3-4i 1.5+2.5i
        #e1e10 #i3/4
        
        ; Strings
        "hello" "world" "escapes: \n \t \" \\" "\x41;"
        
        ; Characters
        #\a #\space #\newline #\x41
        
        ; Punctuation and structure
        ( ) #( ) #u8( ) ' ` , ,@ .
        
        ; Nested comments
        #| 
           #| nested |#
           comment 
        |#
    "#;

    // Repeat the source to make the work substantial enough to not be optimized away entirely
    // and to represent a larger codebase.
    let mut huge_source = String::new();
    // Reduced size per run, but we will run it many times
    for _ in 0..5000 {
        huge_source.push_str(source);
    }

    println!("Lexing {} bytes, 100 times...", huge_source.len());

    let start = std::time::Instant::now();
    let mut total_tokens = 0;

    for _ in 0..100 {
        let lexer = lex(&huge_source);
        for token in lexer {
            match token {
                Ok(_) => total_tokens += 1,
                Err(e) => {
                    eprintln!("Lexing error: {e:?}");
                    return;
                }
            }
        }
    }

    let duration = start.elapsed();
    let total_bytes = huge_source.len() as u64 * 100;
    let duration_secs = duration.as_secs_f64();
    let mb_per_sec = (total_bytes as f64 / 1024.0 / 1024.0) / duration_secs;

    println!("Total time: {duration:?}");
    println!("Average time per run: {:?}", duration / 100);
    println!("Total tokens processed: {total_tokens}");
    println!("Throughput: {mb_per_sec:.2} MB/s");
}
