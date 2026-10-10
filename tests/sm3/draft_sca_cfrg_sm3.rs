//! draft-sca-cfrg-sm3-02's examples: Appendix A (GB/T 32905-2016's two) and
//! Appendix B (eighteen hashes from GB/T 32918's SM2 examples).

use super::{check, unhex};

const DRAFT: &str = include_str!("../../vectors/draft-sca-cfrg-sm3/draft-sca-cfrg-sm3-02.txt");

/// The text from the heading starting `from` (at the start of a line, unlike
/// its entry in the table of contents) to the one starting `to`.
fn section(from: &str, to: &str) -> &'static str {
    let start = DRAFT.find(&format!("\n{from}")).unwrap();
    let end = start + 1 + DRAFT[start + 1..].find(&format!("\n{to}")).unwrap();
    &DRAFT[start..end]
}

/// The bytes of the lines of `text` made only of hex numbers of whole
/// bytes, leaving out prose, headings and page breaks.
fn hex_rows(text: &str) -> Vec<u8> {
    let hex: String = text
        .lines()
        .filter(|line| {
            let mut words = line.split_whitespace().peekable();
            words.peek().is_some()
                && words.all(|w| w.len() % 2 == 0 && w.bytes().all(|b| b.is_ascii_hexdigit()))
        })
        .flat_map(|line| line.split_whitespace())
        .collect();
    unhex(&hex)
}

#[test]
fn appendix_a() {
    // A.1: "abc", given in A.1.1 as "616263".
    let m = section("A.1.1.", "A.1.2.");
    let msg = unhex(m.split("as \"").nth(1).unwrap().split('"').next().unwrap());
    assert_eq!(msg, b"abc");
    check(&msg, &hex_rows(section("A.1.5.", "A.2.")));
    // A.2: 64 bytes.
    let msg = hex_rows(section("A.2.1.", "A.2.2."));
    assert_eq!(msg.len(), 64);
    check(&msg, &hex_rows(section("A.2.3.", "Appendix B.")));
}

#[test]
fn appendix_b() {
    for k in 1..=18 {
        let to = if k == 18 {
            "Appendix C.".to_string()
        } else {
            format!("B.{}.", k + 1)
        };
        let s = section(&format!("B.{k}."), &to);
        let (input, output) = s.split_once("Output:").unwrap();
        let input = hex_rows(input.split_once("Input:").unwrap().1);
        let output = hex_rows(output);
        assert_eq!(output.len(), 32, "B.{k}");
        check(&input, &output);
    }
}
