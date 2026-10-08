#!/usr/bin/env python3
"""The tests each line of CI's `rust-cpu-features` runs, named explicitly.

A line of a CPU's `runs` is `<VG_CPU_FEATURES> | <groups>` (see ci.yml):
`all` for every test, or the names of groups in `GROUPS`, each the tests of
one primitive, or of what is built on it, whose implementation the CPU's
features choose. A group names its tests by their paths in the library's
unit tests (`lib`) and in the test binary `tests/main.rs` (`tests`): a path
selects the test of that name and every test in the module of that name,
and nothing else, so a test runs on a line only if a group of it names the
test or a module around it. A new test of a primitive that varies by CPU
feature goes into the group of each line that should run it.

Each line runs every test its groups select, by exact name, in the one
binary or both that hold them. A group that selects no test on a line's CPU
fails the line, and a path that selects no test on any CPU of the matrix
fails CI: a typo, a renamed test or a moved one never makes a line run less
than it says. A path may select nothing on the CPUs whose `runs` use its
group, until the code it tests is built for them: `ecdsa`'s unit tests are
x86-64's for now, and run on the other CPUs' `ecdsa` lines when they are
built there too.

  cpu_tests.py select BINARY LIB TESTS GROUP...
      the tests of the groups in BINARY (`lib` or `tests`), one per line,
      of the tests listed (`--list --format terse`) in the files LIB and
      TESTS
  cpu_tests.py record CPU RUNS LIB TESTS
      as JSON: the groups the CPU's `runs` use and the tests it has, for
      `check`
  cpu_tests.py check RECORD...
      fails if a path of a group selects no test on any CPU, or if a group
      is not used on any CPU
  cpu_tests.py lint WORKFLOW
      fails if a line of a `runs` in WORKFLOW names a group that is not in
      `GROUPS`
"""

import json
import re
import sys

BINARIES = ("lib", "tests")

GROUPS = {
    "aes_cbc": {
        "lib": ["aes_cbc"],
        "tests": ["cavp::aes_cbc", "wycheproof::aes_cbc"],
    },
    "aes_ccm": {
        "lib": ["aes_ccm"],
        "tests": ["cavp::aes_ccm", "wycheproof::aes_ccm"],
    },
    "aes_ecb": {
        "lib": ["aes_ecb"],
        "tests": ["cavp::aes_ecb"],
    },
    "aes_gcm": {
        "lib": ["aes_gcm", "aes_gcm_siv"],
        "tests": ["cavp::aes_gcm", "wycheproof::aes_gcm", "wycheproof::aes_gcm_siv"],
    },
    "aes_gcm_siv": {
        "lib": ["aes_gcm_siv"],
        "tests": ["wycheproof::aes_gcm_siv"],
    },
    "aes_ocb": {
        "lib": ["aes_ocb"],
        "tests": ["rfc7253::aes_ocb_iterative", "rfc7253::aes_ocb_sample_results"],
    },
    "aes_ofb": {
        "lib": ["aes_ofb"],
        "tests": ["cavp::aes_ofb"],
    },
    "aes_cfb": {
        "lib": ["aes_cfb"],
        "tests": ["cavp::aes_cfb"],
    },
    "aes_cfb8": {
        "lib": ["aes_cfb8"],
        "tests": ["cavp::aes_cfb8"],
    },
    "aes_siv": {
        "lib": ["aes_siv"],
        "tests": ["wycheproof::aes_siv"],
    },
    "argon2": {
        "lib": ["argon2", "argon2_compress_tests", "argon2_hprime_tests"],
        "tests": [],
    },
    "blake2": {
        "lib": [
            "argon2_hprime_tests::hprime_matches_blake2b_composition",
            "hashes::blake2",
            "hashes::blake2b",
            "hashes::blake2s",
        ],
        "tests": ["blake2_kat::blake2b", "blake2_kat::blake2s", "rfc7693::blake2b", "rfc7693::blake2s"],
    },
    "chacha20": {
        "lib": ["chacha20", "chacha20poly1305"],
        "tests": [
            "rfc8439::chacha20",
            "rfc8439::chacha20poly1305",
            "wycheproof::chacha20",
            "wycheproof::chacha20poly1305",
        ],
    },
    "cmac": {
        "lib": ["cmac"],
        "tests": [
            "cavp::cmac_aes",
            "cavp::cmac_triple_des",
            "wycheproof::aes_siv::aead_aes_siv_cmac",
            "wycheproof::aes_siv::aes_siv_cmac",
            "wycheproof::cmac_aes",
        ],
    },
    "cpu": {
        "lib": ["cpu"],
        "tests": [],
    },
    "ecdsa": {
        "lib": ["ecdsa"],
        "tests": [
            "cavp::ecdsa_p256",
            "wycheproof::ecdsa_p224",
            "wycheproof::ecdsa_p256",
            "wycheproof::ecdsa_p384",
            "wycheproof::ecdsa_p521",
        ],
    },
    "ed25519": {
        "lib": ["ed25519"],
        "tests": ["rfc8032::ed25519_vectors", "wycheproof::ed25519"],
    },
    "ed448": {
        "lib": [],
        "tests": ["rfc8032::ed448", "wycheproof::ed448"],
    },
    "message_boundaries_and_unaligned_inputs": {
        "lib": [],
        "tests": [
            "rfc8032::ed448::message_boundaries_and_unaligned_inputs",
            "rfc8032::message_boundaries_and_unaligned_inputs",
        ],
    },
    "mldsa": {
        "lib": ["mldsa_common"],
        "tests": [
            "acvp::mldsa44",
            "acvp::mldsa65",
            "acvp::mldsa87",
            "wycheproof::mldsa44",
            "wycheproof::mldsa65",
            "wycheproof::mldsa87",
        ],
    },
    "mlkem": {
        "lib": ["mlkem_common"],
        "tests": ["acvp::mlkem1024", "acvp::mlkem768", "wycheproof::mlkem1024", "wycheproof::mlkem768"],
    },
    "p224_sha": {
        "lib": [],
        "tests": ["rfc6979::p224::p224_sha224"],
    },
    "p256": {
        "lib": ["ec::p256", "ecdsa::p256"],
        "tests": [
            "cavp::ecdh_p256",
            "cavp::ecdsa_p256",
            "rfc6979::p256",
            "wycheproof::ecdh_p256",
            "wycheproof::ecdsa_p256",
        ],
    },
    "p256_sha": {
        "lib": [],
        "tests": ["rfc6979::p256::p256_sha256", "rfc6979::p256::p256_sha384"],
    },
    "p521": {
        "lib": ["ec::p521", "ecdsa::p521"],
        "tests": [
            "cavp::ecdh_p521",
            "rfc6979::p521",
            "wycheproof::ecdh_p521",
            "wycheproof::ecdsa_p521::ecdsa_secp521r1_sha512_p1363_test",
        ],
    },
    "p384": {
        "lib": ["ec::p384", "ecdsa::p384"],
        "tests": [
            "cavp::ecdh_p384",
            "rfc6979::p384",
            "wycheproof::ecdh_p384",
            "wycheproof::ecdsa_p384::ecdsa_secp384r1_sha384_p1363_test",
        ],
    },
    "p384_sha": {
        "lib": [],
        "tests": ["rfc6979::p384::p384_sha384"],
    },
    "poly1305": {
        "lib": ["chacha20poly1305", "poly1305"],
        "tests": [
            "rfc8439::chacha20::rfc8439_chacha20_poly1305_key_generation",
            "rfc8439::chacha20poly1305",
            "rfc8439::poly1305",
            "wycheproof::chacha20::chacha20_poly1305_ciphertexts",
            "wycheproof::chacha20poly1305",
        ],
    },
    "rfc9106": {
        "lib": [],
        "tests": ["rfc9106::rfc9106_vectors", "rfc9106::rfc9106_verify_keyed"],
    },
    "rsa": {
        "lib": ["rsa", "rsa_keygen", "rsa_oaep", "rsa_pkcs1_enc", "rsa_pkcs1_sig", "rsa_pss"],
        "tests": [
            "cavp::rsa",
            "rsa_guidance::rsa_pkcs1_appendix_b",
            "rsa_guidance::rsa_pkcs1_bad_keys",
            "rsa_guidance::rsa_pkcs1_lengths",
            "wycheproof::rsa",
            "wycheproof::rsa_keygen",
            "wycheproof::rsa_keys",
            "wycheproof::rsa_oaep",
            "wycheproof::rsa_pkcs1_enc",
            "wycheproof::rsa_pkcs1_sig",
            "wycheproof::rsa_pss",
            "wycheproof::rsa_public",
        ],
    },
    "rsa_oaep": {
        "lib": ["rsa_oaep"],
        "tests": ["wycheproof::rsa::rsa_oaep_test", "wycheproof::rsa_oaep"],
    },
    "rsa_pkcs1": {
        "lib": ["rsa_pkcs1_enc", "rsa_pkcs1_sig"],
        "tests": [
            "rsa_guidance::rsa_pkcs1_appendix_b",
            "rsa_guidance::rsa_pkcs1_bad_keys",
            "rsa_guidance::rsa_pkcs1_lengths",
            "wycheproof::rsa::rsa_pkcs1_test",
            "wycheproof::rsa_pkcs1_enc",
            "wycheproof::rsa_pkcs1_sig",
        ],
    },
    "rsa_pss": {
        "lib": ["rsa_pss"],
        "tests": ["wycheproof::rsa_pss"],
    },
    "scrypt": {
        "lib": ["scrypt"],
        "tests": [],
    },
    "sha1": {
        "lib": ["hashes::sha1", "hmac::sha1", "pbkdf2::sha1", "rsa_pss::sha1"],
        "tests": ["cavp::sha1", "pbkdf2::sha1", "wycheproof::hmac_sha1", "wycheproof::pbkdf2_sha1"],
    },
    "sha224": {
        "lib": ["hashes::sha224", "hmac::sha224", "pbkdf2::sha224", "rsa_pss::sha224"],
        "tests": [
            "cavp::sha224",
            "pbkdf2::sha224",
            "rfc6979::p224::p224_sha224",
            "wycheproof::ecdsa_p224::ecdsa_secp224r1_sha224_p1363_test",
            "wycheproof::hmac_sha224",
            "wycheproof::pbkdf2_sha224",
        ],
    },
    "sha256": {
        "lib": ["hashes::sha256", "hmac::sha256", "pbkdf2::sha256", "rsa_pss::sha256"],
        "tests": [
            "cavp::sha256",
            "pbkdf2::sha256",
            "rfc6979::p256::p256_sha256",
            "wycheproof::ecdsa_p256::ecdsa_secp256r1_sha256_p1363_test",
            "wycheproof::hmac_sha256",
            "wycheproof::pbkdf2_sha256",
        ],
    },
    "sha3": {
        "lib": ["hashes::sha3", "hashes::sha384", "hmac::sha384", "pbkdf2::sha384", "rsa_pss::sha384"],
        "tests": [
            "cavp::sha3",
            "cavp::sha384",
            "pbkdf2::sha384",
            "rfc6979::p256::p256_sha384",
            "rfc6979::p384::p384_sha384",
            "wycheproof::ecdsa_p384::ecdsa_secp384r1_sha384_p1363_test",
            "wycheproof::hmac_sha384",
            "wycheproof::pbkdf2_sha384",
        ],
    },
    "sha384": {
        "lib": ["hashes::sha384", "hmac::sha384", "pbkdf2::sha384", "rsa_pss::sha384"],
        "tests": [
            "cavp::sha384",
            "pbkdf2::sha384",
            "rfc6979::p256::p256_sha384",
            "rfc6979::p384::p384_sha384",
            "wycheproof::ecdsa_p384::ecdsa_secp384r1_sha384_p1363_test",
            "wycheproof::hmac_sha384",
            "wycheproof::pbkdf2_sha384",
        ],
    },
    "sha512": {
        "lib": [
            "hashes::sha512",
            "hashes::sha512_224",
            "hashes::sha512_256",
            "hmac::sha512",
            "hmac::sha512_224",
            "hmac::sha512_256",
            "pbkdf2::sha512",
            "pbkdf2::sha512_224",
            "pbkdf2::sha512_256",
            "rsa_pss::sha512",
            "rsa_pss::sha512_224",
            "rsa_pss::sha512_256",
        ],
        "tests": [
            "cavp::sha512",
            "cavp::sha512_224",
            "cavp::sha512_256",
            "pbkdf2::sha512",
            "pbkdf2::sha512_224",
            "pbkdf2::sha512_256",
            "rfc6979::p521::p521_sha512",
            "wycheproof::ecdsa_p521::ecdsa_secp521r1_sha512_p1363_test",
            "wycheproof::hmac_sha512",
            "wycheproof::hmac_sha512_224",
            "wycheproof::hmac_sha512_256",
            "wycheproof::pbkdf2_sha512",
        ],
    },
    "shake": {
        "lib": [
            "hashes::sha3::tests::shake_absorb_boundaries",
            "hashes::sha3::tests::shake_incremental",
            "hashes::sha3::tests::shake_reader",
        ],
        "tests": ["cavp::sha3::shake128", "cavp::sha3::shake256"],
    },
    "signing_with_aliased_read_only_inputs": {
        "lib": [],
        "tests": [
            "rfc8032::ed448::signing_with_aliased_read_only_inputs",
            "rfc8032::signing_with_aliased_read_only_inputs",
        ],
    },
    "triple_des_ecb": {
        "lib": ["triple_des_ecb"],
        "tests": ["cavp::triple_des_ecb"],
    },
    "x25519": {
        "lib": ["x25519"],
        "tests": ["rfc7748::x25519_vectors", "wycheproof::x25519"],
    },
    "x448": {
        "lib": ["x448"],
        "tests": ["rfc7748::x448", "wycheproof::x448"],
    },
    "zeroize": {
        "lib": ["zeroize"],
        "tests": [],
    },
}

PATH = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(::[A-Za-z_][A-Za-z0-9_]*)*")


def selects(path, test):
    """Whether `path` selects the test named `test`."""
    return test == path or test.startswith(path + "::")


def parse_list(text):
    """The names of the tests of a `--list --format terse` output."""
    return [line[: -len(": test")] for line in text.splitlines() if line.endswith(": test")]


def groups_of(tests):
    """The groups of a line's tests (`all` is not a group)."""
    names = tests.split()
    unknown = [n for n in names if n not in GROUPS]
    if unknown:
        raise SystemExit(f"not a group of ci/cpu_tests.py: {', '.join(unknown)}")
    return names


def select(binary, listed, names):
    """Of `listed` (binary to test names), the tests the groups `names`
    select in `binary`; a group that selects no test in either is an
    error."""
    for name in names:
        if not any(selects(p, t) for b in BINARIES for p in GROUPS[name][b] for t in listed[b]):
            raise SystemExit(f"group {name} selects no test on this CPU")
    paths = [p for name in names for p in GROUPS[name][binary]]
    return [t for t in listed[binary] if any(selects(p, t) for p in paths)]


def runs_groups(runs):
    """The groups the lines of `runs` use."""
    out = set()
    for raw in runs.splitlines():
        _, _, tests = raw.partition("|")
        if tests.split() and tests.split() != ["all"]:
            out.update(groups_of(tests))
    return sorted(out)


def check(records):
    """The errors of the records of every CPU."""
    used = {name for r in records for name in r["groups"]}
    errors = [f"group {name} is used by no CPU's runs" for name in GROUPS if name not in used]
    for name, group in GROUPS.items():
        for b in BINARIES:
            for p in group[b]:
                if not any(selects(p, t) for r in records for t in r["tests"][b]):
                    errors.append(f"group {name}: {b} path {p} selects no test on any CPU")
    return errors


def lint(workflow):
    """The errors of the `runs` of the workflow's text."""
    errors = []
    for name, group in GROUPS.items():
        for b in BINARIES:
            errors += [f"group {name}: {b} path {p!r} is not a path" for p in group[b]
                       if not PATH.fullmatch(p)]
    block = workflow.split("\n  rust-cpu-features:\n", 1)[1].split("\n  cpu-features-times-save:", 1)[0]
    for line in re.findall(r"^ +[a-z0-9,_-]+ \| (.*)$", block, re.M):
        names = line.split()
        if names != ["all"]:
            errors += [f"{n}: not a group of ci/cpu_tests.py" for n in names if n not in GROUPS]
    return errors


def read(path):
    with open(path) as f:
        return f.read()


def main(argv):
    if argv[:1] == ["select"] and len(argv) >= 5 and argv[1] in BINARIES:
        listed = {"lib": parse_list(read(argv[2])), "tests": parse_list(read(argv[3]))}
        for t in select(argv[1], listed, argv[4:]):
            print(t)
    elif argv[:1] == ["record"] and len(argv) == 5:
        tests = {"lib": parse_list(read(argv[3])), "tests": parse_list(read(argv[4]))}
        cpu = " ".join(argv[1].split())
        print(json.dumps({"cpu": cpu, "groups": runs_groups(argv[2]), "tests": tests}))
    elif argv[:1] in (["check"], ["lint"]) and len(argv) >= 2:
        if argv[0] == "check":
            errors = check([json.loads(read(p)) for p in argv[1:]])
        else:
            errors = lint(read(argv[1]))
        for e in errors:
            print(e, file=sys.stderr)
        if errors:
            raise SystemExit(1)
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
