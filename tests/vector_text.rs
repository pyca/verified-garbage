//! The parsing of the vector files (`crates/verified-garbage-test-vectors`)
//! on text that no vector file has: what it rejects, and the layouts it
//! skips. (The vector tests read every file the parsers are for.)

use verified_garbage_test_vectors::{
    Record, cavp_blocks, cavp_fields, cavp_records, try_unhex, unhex, unhex_spaced,
};

#[test]
fn hex() {
    assert_eq!(unhex("00fFa5Aa"), [0x00, 0xff, 0xa5, 0xaa]);
    assert_eq!(unhex_spaced(" 01 2\n3\u{a0}45 "), [0x01, 0x23, 0x45]);
    for bad in ["0", "0g", "g0", "+f", "é0"] {
        assert_eq!(try_unhex(bad), None, "{bad}");
    }
}

#[test]
#[should_panic(expected = "not an even number of hex digits")]
fn not_hex() {
    unhex("123");
}

#[test]
fn records() {
    let r = Record::parse("A = 1\n  B = 2  \nnot a field\nA = 3");
    assert_eq!((r["A"], r.get("B"), r.get("C")), ("3", Some("2"), None));
    assert!(r.contains_key("B") && !r.contains_key("C"));

    // A field's ` = ` is the first, past any other `=`, as `split_once`'s.
    for line in [
        "a=b = c = d",
        "=a = b",
        "a =b = c",
        "a = ",
        "a =",
        "a=",
        " = a",
        "a  =  b",
    ] {
        let field = Record::parse(line).fields.first().copied();
        assert_eq!(field, line.trim().split_once(" = "), "{line:?}");
    }

    let text = "# c\n[L = 1]\nCOUNT = 0\nX = 1\n\nY = 2\n\nCOUNT = 1\n";
    let records = cavp_records(text);
    assert_eq!(records.len(), 2);
    assert_eq!((records[0]["X"], records[1]["COUNT"]), ("1", "1"));

    let fields = cavp_fields("# c\n\n[L = 1]\n A = 1 \nB = 2\n");
    assert_eq!(fields, [("A", "1"), ("B", "2")]);
}

#[test]
#[should_panic(expected = "no field \"C\"")]
fn missing_field() {
    let _ = Record::parse("A = 1")["C"];
}

#[test]
#[should_panic(expected = "not a `key = value` line")]
fn not_a_field() {
    cavp_fields("A = 1\nB\n");
}

#[test]
fn blocks() {
    // Only blocks whose first line is a `Count`: a line of spaces does not
    // end a block, and `Count` must be the whole key.
    let text = "[K = 1]\n\nCountry = 0\nX = 1\n\n  \nCount = 0\n \nX =\nFAIL\n\nCount = 1\nX = 2";
    let blocks = cavp_blocks(text, "Count");
    assert_eq!(blocks.len(), 2);
    assert_eq!((blocks[0].0["X"], &blocks[0].1[..]), ("", &["FAIL"][..]));
    assert_eq!((blocks[1].0["X"], blocks[1].1.len()), ("2", 0));

    for line in ["a=b = c", "=a =b", "a=", "a =", " =", "a = b =c"] {
        let text = format!("Count = 0\n{line}");
        let (record, bare) = &cavp_blocks(&text, "Count")[0];
        let field = line.trim().split_once(" =").map(|(k, v)| (k, v.trim()));
        assert_eq!(record.fields.get(1).copied(), field, "{line:?}");
        assert_eq!(bare.len(), usize::from(field.is_none()));
    }
}
