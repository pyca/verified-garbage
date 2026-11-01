//! Loading and validating Wycheproof test vector files.
//!
//! A test vector file is loaded as a [`TestFile`], parameterized by the
//! algorithm-specific fields of its test groups (`P`) and of its tests
//! (`T`). Algorithm tests declare structs for those fields (with
//! `json_struct!`) and iterate over its tests ([`TestFile::par_tests`]);
//! loading checks that the file is internally consistent, so a test can
//! never silently run on fewer vectors than the file contains.
//!
//! The file is parsed by one copy of the code for every algorithm, into a
//! JSON value (`crate::json`), and only reading `P` and `T` from it is
//! compiled for each.

// Each algorithm test module uses a different subset of the harness. A
// function only some architectures' tests call is built only for those (as
// RSA's are, `ci/check_arch_gates.py`), so that each architecture runs every
// line it builds.
#![allow(dead_code)]

use std::collections::{BTreeMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use serde_json::Value;

use crate::json::{self, FromJson};

/// The environment variable pointing at a checkout of
/// <https://github.com/C2SP/wycheproof>. A relative path is relative to the
/// crate root.
pub const ROOT_VAR: &str = "WYCHEPROOF_ROOT";

/// The directory containing the Wycheproof test vectors, or `None` if
/// `WYCHEPROOF_ROOT` is not set (the tests are then skipped).
pub fn vectors_dir() -> Option<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join(std::env::var_os(ROOT_VAR)?);
    let dir = root.join("testvectors_v1");
    assert!(dir.is_dir());
    Some(dir)
}

/// Every test vector file, sorted by name; `None` if the vectors are not
/// available. For the RSA tests.
#[cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]
pub fn all_files() -> Option<Vec<String>> {
    let mut names: Vec<String> = std::fs::read_dir(vectors_dir()?)
        .expect("reading the Wycheproof directory")
        .map(|e| e.unwrap().file_name().into_string().unwrap())
        .filter(|n| n.ends_with(".json"))
        .collect();
    names.sort();
    Some(names)
}

/// Set (by CI) when the tests run under an emulator on a host without
/// AVX512_IFMA. The emulator then runs the private-key operation's IFMA code
/// for 3072- and 4096-bit keys some thirty times slower than the ADX code,
/// and the RSA tests take tens of minutes.
pub const HOST_WITHOUT_IFMA_VAR: &str = "VG_TEST_HOST_WITHOUT_IFMA";

/// Whether to test RSA keys of `bits` bits: every size, but on a CPU with
/// AVX512_IFMA emulated on a host without it ([`HOST_WITHOUT_IFMA_VAR`]),
/// where PSS signing alone tests the 3072- and 4096-bit keys (each of the
/// other tests calls the same IFMA code with them). CI's IFMA vector group
/// uses `rsa_pss::rsa_pss_large_keys`; the full signing suite uses
/// [`rsa_bits_signed`]. A CPU with AVX512_IFMA tests them all.
#[cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]
pub fn rsa_bits_tested(bits: usize) -> bool {
    #[cfg(target_arch = "x86_64")]
    let ifma = std::arch::is_x86_feature_detected!("avx512ifma");
    #[cfg(not(target_arch = "x86_64"))]
    let ifma = false;
    !(bits == 3072 || bits == 4096) || !ifma || std::env::var_os(HOST_WITHOUT_IFMA_VAR).is_none()
}

/// Whether `rsa_pss::rsa_pss_sign_test` signs with RSA keys of `bits` bits:
/// those [`rsa_bits_tested`] tests, and every size in the configuration
/// without `VG_CPU_FEATURES` (`src/cpu.rs`), which an emulated CPU's lines
/// in CI run once. Its other configurations call the same IFMA code with
/// the 3072- and 4096-bit keys, emulated some thirty times slower than the
/// ADX code, each for minutes of CI's time.
#[cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]
pub fn rsa_bits_signed(bits: usize) -> bool {
    rsa_bits_tested(bits) || std::env::var_os("VG_CPU_FEATURES").is_none_or(|v| v.is_empty())
}

/// Whether to test the RSA key with the modulus `n` (as [`rsa_bits_tested`]).
#[cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]
pub fn rsa_key_tested(n: &[u8]) -> bool {
    let n = crate::bytes::trim_zeros(n);
    rsa_bits_tested(n.len() * 8 - n.first().map_or(0, |b| b.leading_zeros() as usize))
}

/// Whether to test the RSA vector file `name`, whose name gives its keys'
/// size, if it has one size (`rsa_oaep_3072_…`; as [`rsa_bits_tested`]).
#[cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]
pub fn rsa_file_tested(name: &str) -> bool {
    name.split('_')
        .all(|part| part.parse().map_or(true, rsa_bits_tested))
}

/// Skip the calling test (by returning early) if the vectors are not available.
#[macro_export]
macro_rules! require_vectors {
    () => {
        if $crate::wycheproof::harness::vectors_dir().is_none() {
            eprintln!(
                "skipping: set {} to a checkout of https://github.com/C2SP/wycheproof",
                $crate::wycheproof::harness::ROOT_VAR
            );
            return;
        }
    };
}

/// The expected outcome of a test.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expectation {
    /// The operation must succeed with the given result.
    Valid,
    /// The operation must fail (or the result must be rejected).
    Invalid,
    /// Either outcome is allowed; the test's `flags` say why.
    Acceptable,
}

impl FromJson for Expectation {
    fn from_json(v: &Value, key: &str) -> Self {
        match v.as_str() {
            Some("valid") => Expectation::Valid,
            Some("invalid") => Expectation::Invalid,
            Some("acceptable") => Expectation::Acceptable,
            _ => panic!("{key}: expected a test result, found {v}"),
        }
    }
}

/// Every test result is read (and anything else refused, below): so that
/// every architecture runs every arm, whichever results its vector files
/// have.
#[test]
fn expectation_from_json() {
    let read = |json: &str| Expectation::from_json(&json.parse().unwrap(), "result");
    assert_eq!(read(r#""valid""#), Expectation::Valid);
    assert_eq!(read(r#""invalid""#), Expectation::Invalid);
    assert_eq!(read(r#""acceptable""#), Expectation::Acceptable);
}

#[test]
#[should_panic(expected = "result: expected a test result, found 1")]
fn expectation_from_json_refuses() {
    Expectation::from_json(&Value::from(1), "result");
}

crate::json_struct! {
    /// A note describing a test flag.
    #[derive(Debug, Clone)]
    pub struct Note {
        /// The class of bug the flagged tests look for.
        #[json(rename = "bugType")]
        pub bug_type: Option<String>,
        /// A description of the flag.
        pub description: Option<String>,
    }
}

/// One test.
#[derive(Debug, Clone)]
pub struct Test<T> {
    /// The test's id, unique within the file.
    pub tc_id: u64,
    pub comment: String,
    /// Usually keys into [`TestFile::notes`].
    pub flags: Vec<String>,
    pub result: Expectation,
    /// The algorithm-specific fields, read from the test's object (whose
    /// other keys `T` ignores).
    pub case: T,
}

impl<T: FromJson> FromJson for Test<T> {
    fn from_json(v: &Value, key: &str) -> Self {
        let o = json::object(v, key);
        Test {
            tc_id: json::field(o, "tcId"),
            comment: json::field_or_default(o, "comment"),
            flags: json::field_or_default(o, "flags"),
            result: json::field(o, "result"),
            case: T::from_json(v, key),
        }
    }
}

/// A group of tests sharing parameters (key, sizes, …).
#[derive(Debug, Clone)]
pub struct TestGroup<P, T> {
    /// The algorithm-specific group fields, read from the group's object
    /// (whose `tests` `P` ignores).
    pub params: P,
    pub tests: Vec<Test<T>>,
}

impl<P: FromJson, T: FromJson> FromJson for TestGroup<P, T> {
    fn from_json(v: &Value, key: &str) -> Self {
        let tests = json::field(json::object(v, key), "tests");
        TestGroup {
            params: P::from_json(v, key),
            tests,
        }
    }
}

crate::json_struct! {
    /// A test vector file.
    #[derive(Debug, Clone)]
    pub struct TestFile<P, T> {
        pub algorithm: Option<String>,
        pub schema: String,
        #[json(rename = "numberOfTests")]
        pub number_of_tests: usize,
        #[json(default)]
        pub notes: BTreeMap<String, Note>,
        #[json(rename = "testGroups")]
        pub test_groups: Vec<TestGroup<P, T>>,
    }
}

/// The algorithm-specific fields of a file whose test reads none of them
/// (the compressed points' only look at the file structure), which must be
/// an object.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
pub struct Fields;

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
impl FromJson for Fields {
    fn from_json(v: &Value, key: &str) -> Self {
        json::object(v, key);
        Fields
    }
}

/// Bytes, written in hex in the test vector files.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Hex(pub Vec<u8>);

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
impl FromJson for Hex {
    fn from_json(v: &Value, key: &str) -> Self {
        let s = v.as_str();
        let s = s.unwrap_or_else(|| panic!("{key}: expected a string, found {v}"));
        let byte = |i| u8::from_str_radix(&s[i..i + 2], 16);
        let byte = |i| byte(i).unwrap_or_else(|e| panic!("{key}: {s}: {e}"));
        Hex((0..s.len()).step_by(2).map(byte).collect())
    }
}

impl<P, T> TestFile<P, T> {
    /// Calls `f` on every test, with its group, as [`par_each`] does.
    #[cfg(any(
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "x86",
        all(target_arch = "powerpc64", target_endian = "little"),
        target_arch = "riscv64"
    ))]
    pub fn par_tests(&self, f: impl Fn(&TestGroup<P, T>, &Test<T>) + Sync)
    where
        P: Sync,
        T: Sync,
    {
        let groups = &self.test_groups;
        par_group_tests(groups.len(), &|g| groups[g].tests.len(), &|g, t| {
            f(&groups[g], &groups[g].tests[t])
        });
    }

    /// Calls `f` on every test, with its group and what `setup` made of the
    /// group (e.g. its key, made once for all its tests), as [`par_each`]
    /// does.
    #[cfg(all(
        any(
            target_arch = "x86_64",
            target_arch = "x86",
            target_arch = "aarch64",
            target_arch = "arm",
            target_arch = "powerpc64"
        ),
        feature = "alloc"
    ))]
    pub fn par_tests_with<S: Sync>(
        &self,
        setup: impl Fn(&TestGroup<P, T>) -> S,
        f: impl Fn(&TestGroup<P, T>, &S, &Test<T>) + Sync,
    ) where
        P: Sync,
        T: Sync,
    {
        let groups = &self.test_groups;
        let made: Vec<S> = groups.iter().map(setup).collect();
        par_group_tests(groups.len(), &|g| groups[g].tests.len(), &|g, t| {
            f(&groups[g], &made[g], &groups[g].tests[t])
        });
    }
}

/// Calls `f` on every one of `items`, on as many threads as the machine
/// runs at once, each taking the next item no thread has taken yet: so that
/// one file's vectors keep every core busy, rather than one core while the
/// other tests have finished. A failed check panics in its thread, which
/// prints its message, and the test fails once every thread has stopped.
/// For the RSA and compressed point tests.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "powerpc64",
    target_arch = "riscv64"
))]
pub fn par_each<I: Sync>(items: &[I], f: impl Fn(&I) + Sync) {
    par_indices(items.len(), &|i| f(&items[i]));
}

/// Calls `f` on the index of every group (below `groups`) and of each of its
/// `tests(group)` tests, as [`par_each`] does; not generic, as
/// [`par_indices`].
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
fn par_group_tests(
    groups: usize,
    tests: &dyn Fn(usize) -> usize,
    f: &(dyn Fn(usize, usize) + Sync),
) {
    let mut all: Vec<(usize, usize)> = Vec::new();
    for g in 0..groups {
        for t in 0..tests(g) {
            all.push((g, t));
        }
    }
    par_indices(all.len(), &|i| f(all[i].0, all[i].1));
}

/// Calls `f` on every index below `n`, as [`par_each`] does; not generic,
/// so that the threads' code is compiled once rather than for every caller.
fn par_indices(n: usize, f: &(dyn Fn(usize) + Sync)) {
    let workers = std::thread::available_parallelism().map_or(1, |n| n.get());
    let next = AtomicUsize::new(0);
    std::thread::scope(|s| {
        for _ in 0..workers.min(n) {
            s.spawn(|| {
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    if i >= n {
                        break;
                    }
                    f(i);
                }
            });
        }
    });
}

/// A number of vectors, counted by the threads of [`par_each`].
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
#[derive(Default)]
pub struct Count(AtomicUsize);

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
impl Count {
    /// Counts one more.
    pub fn add(&self) {
        self.add_n(1);
    }

    /// Counts `n` more.
    pub fn add_n(&self, n: usize) {
        self.0.fetch_add(n, Ordering::Relaxed);
    }

    /// The number counted.
    pub fn get(&self) -> usize {
        self.0.load(Ordering::Relaxed)
    }
}

/// Parse a test vector file and check that it is internally consistent:
/// the number of tests matches `numberOfTests` and test ids are unique.
/// (Not every flag is described in `notes` upstream, so that is not checked.)
pub fn parse<P: FromJson, T: FromJson>(name: &str, json: &str) -> TestFile<P, T> {
    let file: TestFile<P, T> = json::parse(name, json);
    let mut ids = Vec::new();
    for group in &file.test_groups {
        for test in &group.tests {
            ids.push(test.tc_id);
        }
    }
    check(name, &ids, file.number_of_tests);
    file
}

/// Checks that the test ids `ids` of the file `name` are unique and that
/// there are `number_of_tests` of them; not generic, as [`par_indices`].
fn check(name: &str, ids: &[u64], number_of_tests: usize) {
    let mut seen = HashSet::new();
    for id in ids {
        assert!(seen.insert(id), "{name}: duplicate tcId {id}");
    }
    assert_eq!(ids.len(), number_of_tests, "{name}: numberOfTests");
}

/// Load and validate the test vector file `name` (e.g. `"aes_gcm_test.json"`).
/// Tests calling this must start with `require_vectors!()`.
pub fn load<P: FromJson, T: FromJson>(name: &str) -> TestFile<P, T> {
    parse(name, &read(name))
}

/// The contents of the test vector file `name`.
fn read(name: &str) -> String {
    let path = vectors_dir()
        .expect("Wycheproof vectors not available; use require_vectors!()")
        .join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("reading {}: {e}", path.display()))
}
