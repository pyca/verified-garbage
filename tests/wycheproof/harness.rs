//! Loading and validating Wycheproof test vector files.
//!
//! A test vector file is loaded as a [`TestFile`], parameterized by the
//! algorithm-specific fields of its test groups (`P`) and of its tests
//! (`T`). Algorithm tests declare structs for those fields and iterate over
//! [`TestFile::tests`]; loading checks that the file is internally
//! consistent, so a test can never silently run on fewer vectors than the
//! file contains.

// Each algorithm test module uses a different subset of the harness. A
// function only some architectures' tests call is built only for those (as
// RSA's are, `ci/check_arch_gates.py`), so that each architecture runs every
// line it builds.
#![allow(dead_code)]

use std::collections::{BTreeMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::json::{self, FromJson, Value};

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
    let n = &n[n.iter().take_while(|&&b| b == 0).count()..];
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
    fn from_json(v: &Value) -> Self {
        let name = String::from_json(v);
        [
            ("valid", Expectation::Valid),
            ("invalid", Expectation::Invalid),
            ("acceptable", Expectation::Acceptable),
        ]
        .into_iter()
        .find_map(|(n, e)| (n == name).then_some(e))
        .unwrap_or_else(|| panic!("unknown result {name:?}"))
    }
}

crate::json_struct! {
    /// A note describing a test flag.
    #[derive(Debug, Clone)]
    pub struct Note {
        /// The class of bug the flagged tests look for.
        pub bug_type: Option<String> = "bugType",
        /// A description of the flag.
        pub description: Option<String> = "description",
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
    /// The algorithm-specific fields, read from the test's object too.
    pub case: T,
}

impl<T: FromJson> FromJson for Test<T> {
    fn from_json(v: &Value) -> Self {
        let o = json::object(v);
        Test {
            tc_id: json::field(o, "tcId"),
            comment: json::field_or_default(o, "comment"),
            flags: json::field_or_default(o, "flags"),
            result: json::field(o, "result"),
            case: T::from_json(v),
        }
    }
}

/// A group of tests sharing parameters (key, sizes, …).
#[derive(Debug, Clone)]
pub struct TestGroup<P, T> {
    /// The algorithm-specific group fields, read from the group's object
    /// too.
    pub params: P,
    pub tests: Vec<Test<T>>,
}

impl<P: FromJson, T: FromJson> FromJson for TestGroup<P, T> {
    fn from_json(v: &Value) -> Self {
        TestGroup {
            params: P::from_json(v),
            tests: json::field(json::object(v), "tests"),
        }
    }
}

/// A test vector file.
#[derive(Debug, Clone)]
pub struct TestFile<P, T> {
    pub algorithm: Option<String>,
    pub schema: String,
    pub number_of_tests: usize,
    pub notes: BTreeMap<String, Note>,
    pub test_groups: Vec<TestGroup<P, T>>,
}

impl<P: FromJson, T: FromJson> FromJson for TestFile<P, T> {
    fn from_json(v: &Value) -> Self {
        let o = json::object(v);
        TestFile {
            algorithm: json::field(o, "algorithm"),
            schema: json::field(o, "schema"),
            number_of_tests: json::field(o, "numberOfTests"),
            notes: json::field_or_default(o, "notes"),
            test_groups: json::field(o, "testGroups"),
        }
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
    fn from_json(v: &Value) -> Self {
        let s = String::from_json(v);
        let bytes = (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
            .collect::<Result<Vec<u8>, _>>()
            .unwrap_or_else(|e| panic!("{s:?}: {e}"));
        Hex(bytes)
    }
}

/// Fields a test does not read (the compressed points' group and test
/// fields): only checked to be an object.
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
    fn from_json(v: &Value) -> Self {
        json::object(v);
        Fields
    }
}

impl<P, T> TestFile<P, T> {
    /// Every test, with its group.
    pub fn tests(&self) -> impl Iterator<Item = (&TestGroup<P, T>, &Test<T>)> {
        self.test_groups
            .iter()
            .flat_map(|g| g.tests.iter().map(move |t| (g, t)))
    }

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
        let tests: Vec<_> = self.tests().collect();
        par_each(&tests, |&(g, t)| f(g, t));
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
        let made: Vec<S> = self.test_groups.iter().map(setup).collect();
        let tests: Vec<_> = self
            .test_groups
            .iter()
            .zip(&made)
            .flat_map(|(g, s)| g.tests.iter().map(move |t| (g, s, t)))
            .collect();
        par_each(&tests, |&(g, s, t)| f(g, s, t));
    }
}

/// Calls `f` on every one of `items`, on as many threads as the machine
/// runs at once, each taking the next item no thread has taken yet: so that
/// one file's vectors keep every core busy, rather than one core while the
/// other tests have finished. A failed check panics in its thread, which
/// prints its message, and the test fails once every thread has stopped.
pub fn par_each<I: Sync>(items: &[I], f: impl Fn(&I) + Sync) {
    let workers = std::thread::available_parallelism().map_or(1, |n| n.get());
    let next = AtomicUsize::new(0);
    std::thread::scope(|s| {
        for _ in 0..workers.min(items.len()) {
            s.spawn(|| {
                while let Some(item) = items.get(next.fetch_add(1, Ordering::Relaxed)) {
                    f(item);
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
pub fn parse<P: FromJson, T: FromJson>(name: &str, text: &str) -> TestFile<P, T> {
    let file: TestFile<P, T> = json::from_str(name, text);
    let mut ids = HashSet::new();
    let mut count = 0;
    for (_, t) in file.tests() {
        count += 1;
        assert!(ids.insert(t.tc_id), "{name}: duplicate tcId {}", t.tc_id);
    }
    assert_eq!(count, file.number_of_tests, "{name}: numberOfTests");
    file
}

/// Load and validate the test vector file `name` (e.g. `"aes_gcm_test.json"`).
/// Tests calling this must start with `require_vectors!()`.
pub fn load<P: FromJson, T: FromJson>(name: &str) -> TestFile<P, T> {
    let path = vectors_dir()
        .expect("Wycheproof vectors not available; use require_vectors!()")
        .join(name);
    let json = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("reading {}: {e}", path.display()));
    parse(name, &json)
}
