//! Parsing the text of the test vector files: hex, and the `key = value`
//! records of NIST's CAVP response files and the files written like them.
//!
//! The tests are built unoptimized, where reading the vectors could cost
//! more than checking them: parsing CAVP's 17 MB of AES-GCM files was about
//! nine tenths of that test's time. This crate is the tests' (a
//! dev-dependency), and Cargo.toml optimizes it in test builds, as it does
//! `serde_json`. Only the parsing of the largest files is here: what reads a
//! small file's own layout stays with its test.
//!
//! Every function panics on text that is not what it reads, as the tests
//! did: a malformed file fails its test.

use std::ops::Index;

/// What [`DIGITS`] holds for a byte that is not a hex digit.
const NOT_HEX: u8 = 0xff;
const _: () = assert!(NOT_HEX > 15);

/// Each byte's value as a hex digit, or [`NOT_HEX`]. Built in the static's
/// initializer, not by a `const fn`: the compiler runs it, and a function
/// that only it runs is a function the tests never run, to the coverage.
static DIGITS: [u8; 256] = {
    let mut table = [NOT_HEX; 256];
    let mut i = 0;
    while i < 10 {
        table[b'0' as usize + i] = i as u8;
        i += 1;
    }
    let mut i = 0;
    while i < 6 {
        table[b'a' as usize + i] = 10 + i as u8;
        table[b'A' as usize + i] = 10 + i as u8;
        i += 1;
    }
    table
};

/// The bytes written in hex in `s`, two digits each, either case; `None`
/// if it is anything else.
pub fn try_unhex(s: &str) -> Option<Vec<u8>> {
    let s = s.as_bytes();
    if !s.len().is_multiple_of(2) {
        return None;
    }
    // Every digit's bits, ORed: above 15 if any was not a digit. Checked
    // once, after the loop, which then has no branch but its own.
    let mut digits = 0;
    let mut bytes = Vec::with_capacity(s.len() / 2);
    // No remainder: the length is even.
    let (pairs, _) = s.as_chunks::<2>();
    for pair in pairs {
        let (hi, lo) = (DIGITS[pair[0] as usize], DIGITS[pair[1] as usize]);
        digits |= hi | lo;
        bytes.push(hi << 4 | lo);
    }
    (digits <= 15).then_some(bytes)
}

/// [`try_unhex`], which must succeed.
pub fn unhex(s: &str) -> Vec<u8> {
    try_unhex(s).unwrap_or_else(|| not_hex(s))
}

/// [`unhex`] of `text` without its whitespace.
pub fn unhex_spaced(text: &str) -> Vec<u8> {
    let hex: String = text.split_whitespace().collect();
    unhex(&hex)
}

#[cold]
fn not_hex(s: &str) -> ! {
    panic!("not an even number of hex digits: {s:?}")
}

/// The `key = value` fields of a record, in order. A key given twice has
/// its last value.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Record<'a> {
    pub fields: Vec<(&'a str, &'a str)>,
}

impl<'a> Record<'a> {
    /// The `key = value` lines of `text`, trimmed; other lines are skipped.
    pub fn parse(text: &'a str) -> Self {
        let mut record = Record::default();
        for line in text.lines() {
            record.push_line(line);
        }
        record
    }

    /// Adds `line`, trimmed, if it is a `key = value` line.
    fn push_line(&mut self, line: &'a str) {
        self.fields.extend(split_field(line.trim(), true));
    }

    /// The value of `key`, if the record has it.
    pub fn get(&self, key: &str) -> Option<&'a str> {
        let field = self.fields.iter().rev().find(|(k, _)| *k == key);
        field.map(|&(_, v)| v)
    }

    /// Whether the record has the field `key`.
    pub fn contains_key(&self, key: &str) -> bool {
        self.get(key).is_some()
    }
}

impl<'a> Index<&str> for Record<'a> {
    type Output = &'a str;

    /// The value of `key`; panics if the record does not have it.
    fn index(&self, key: &str) -> &&'a str {
        let field = self.fields.iter().rev().find(|(k, _)| *k == key);
        &field.unwrap_or_else(|| no_field(key)).1
    }
}

#[cold]
fn no_field(key: &str) -> ! {
    panic!("no field {key:?}")
}

/// The records of a CAVP response file that have a `COUNT`: the `key =
/// value` lines up to each empty line (lines that are neither, such as
/// section headers, are skipped).
pub fn cavp_records(text: &str) -> Vec<Record<'_>> {
    let mut records = Vec::new();
    let mut record = Record::default();
    for line in text.lines().chain([""]) {
        if line.is_empty() {
            let record = std::mem::take(&mut record);
            if record.contains_key("COUNT") {
                records.push(record);
            }
        } else {
            record.push_line(line);
        }
    }
    records
}

/// The `key = value` lines of a CAVP response file, trimmed, in order,
/// without the comments, blank lines and `[L = ...]` section headers; panics
/// on any other line.
pub fn cavp_fields(text: &str) -> Vec<(&str, &str)> {
    let mut fields = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if !(line.is_empty() || line.starts_with('#') || line.starts_with('[')) {
            let field = split_field(line, true);
            fields.push(field.unwrap_or_else(|| not_field(line)));
        }
    }
    fields
}

#[cold]
fn not_field(line: &str) -> ! {
    panic!("not a `key = value` line: {line:?}")
}

/// The records of a CAVP response file that begin with a `first = …` line
/// (blocks of lines between empty lines, as the GCM files have), each as its
/// fields, trimmed (`key =` has an empty value), and the lines that are not
/// fields, such as GCM's `FAIL`.
pub fn cavp_blocks<'a>(text: &'a str, first: &str) -> Vec<(Record<'a>, Vec<&'a str>)> {
    let mut blocks = Vec::new();
    // The block being read, if it is a record.
    let mut block: Option<(Record, Vec<&str>)> = None;
    // Whether the next nonblank line begins a block.
    let mut start = true;
    for line in text.lines() {
        if line.is_empty() {
            blocks.extend(block.take());
            start = true;
            continue;
        }
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        if std::mem::take(&mut start)
            && line
                .strip_prefix(first)
                .is_some_and(|l| l.starts_with(" = "))
        {
            block = Some(Default::default());
        }
        if let Some((record, bare)) = block.as_mut() {
            match split_field(line, false) {
                Some((key, value)) => record.fields.push((key, value.trim())),
                None => bare.push(line),
            }
        }
    }
    blocks.extend(block);
    blocks
}

/// `line.split_once(" = ")`, or with `spaced` false `line.split_once(" =")`,
/// by looking for each `=` rather than with `str`'s general search for a
/// pattern of several characters, which is slower on lines this short.
fn split_field(line: &str, spaced: bool) -> Option<(&str, &str)> {
    let bytes = line.as_bytes();
    // The first `=` with a space before it (and after it, if `spaced`).
    let mut from = 0;
    while let Some(i) = bytes[from..].iter().position(|&b| b == b'=') {
        let i = from + i;
        let after = bytes.get(i + 1).copied();
        if i > 0 && bytes[i - 1] == b' ' && (!spaced || after == Some(b' ')) {
            let value = if spaced { i + 2 } else { i + 1 };
            return Some((&line[..i - 1], &line[value..]));
        }
        from = i + 1;
    }
    None
}
