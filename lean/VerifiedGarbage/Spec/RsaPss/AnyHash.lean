module

public import VerifiedGarbage.Spec.RsaPss.Precomputed
public import VerifiedGarbage.Spec.HashFns

/-!
# RSASSA-PSS with the hash functions as arguments: the contracts, on every target

**Trusted** (as every file in `Spec/`). The functions of
`Spec/RsaPss/Contract.lean` and `Spec/RsaPss/Precomputed.lean`, but with
the hash function `H` (the digest's) and MGF1's hash function `G` passed as
arguments rather than fixed by the function's name: each as the number
`HashId.mgf1` gives it, one of `hashIds` (MD5, SHA-1 and the SHA-2
functions), a public `usize` (`hash`, `mgf1_hash`), and a table of its
streaming functions (`hash_fns`, `mgf1_fns`: `HashFns.tableOf`), which the
function calls, in the module `rsa_pss`:

* `vg_rsa_pss_sign`: `signContract H G`;
* `vg_rsa_pss_verify_precomputed`: `verifyPrecomputedContract H G`;

each with the digest a slice of `hLen` octets rather than an array (and,
in `vg_rsa_pss_verify_precomputed`, `any_salt_len` before `salt_len`, so
that on AArch64 the one narrow argument on the stack is its first). That
`hash` and `mgf1_hash` are in `hashIds`, and that the digest is `H`'s `hLen`
octets, are preconditions, as is that the tables hold their streaming
functions. The hash functions and their tables (the addresses of the
functions) are public (arguments marked so, and the tables' words, `leak`),
and may affect timing; nothing else changes.
-/

@[expose] public section

namespace VG.Spec.RsaPss

open Mgf1 (Hash)
open Rsa (bytesAt lenValid writtenOutcome exponentDoc)

/-- The numbers (`HashId.mgf1`) of the hash functions these functions take,
both as the digest's and as MGF1's: MD5, SHA-1, SHA-224, SHA-256, SHA-384,
SHA-512, SHA-512/224 and SHA-512/256. -/
def hashIds : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]

/-- The documentation's list of the hash functions' numbers. -/
def hashIdsDoc : String :=
  s!"`hash` names the digest's hash function and `mgf1_hash` MGF1's: 0 MD5, {HashId.sha12Doc}; \
    `hash_fns` and `mgf1_fns` point to tables of their streaming functions, which it calls \
    (`VG.Spec.HashFns`)"

/-- The `# Safety` items on the hash functions. -/
def hashSafety : List String :=
  ["`hash` and `mgf1_hash` must each be one of 0..=7.",
    HashFns.tableSafety "hash_fns" "hash", HashFns.tableSafety "mgf1_fns" "mgf1_hash",
    "`digest_len` must be the length of `hash`'s values: 16 for MD5, 20 for SHA-1, 28 for \
      SHA-224 and SHA-512/224, 32 for SHA-256 and SHA-512/256, 48 for SHA-384, 64 for \
      SHA-512."]

/-! ## `vg_rsa_pss_sign` -/

/-- `vg_rsa_pss_sign(out: *mut u8, out_len: usize, n: *const u8,
n_len: usize, e: *const u8, e_len: usize, p: *const u8, p_len: usize,
q: *const u8, q_len: usize, dp: *const u8, dp_len: usize, dq: *const u8,
dq_len: usize, qinv: *const u8, qinv_len: usize, digest: *const u8,
digest_len: usize, salt: *const u8, salt_len: usize, scratch: *mut u64,
scratch_len: usize, hash: usize, mgf1_hash: usize, hash_fns: *const [u64; 3],
mgf1_fns: *const [u64; 3]) -> u32`. -/
def signAnySig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("p", .slice false .u8 "p_len"),
    ("q", .slice false .u8 "q_len"), ("dp", .slice false .u8 "dp_len"),
    ("dq", .slice false .u8 "dq_len"), ("qinv", .slice false .u8 "qinv_len"),
    ("digest", .slice false .u8 "digest_len"), ("salt", .slice false .u8 "salt_len"),
    ("scratch", .slice true .u64 "scratch_len"), ("hash", .int .usize true),
    ("mgf1_hash", .int .usize true), ("hash_fns", .array false .u64 3),
    ("mgf1_fns", .array false .u64 3)]
  ret := some .u32

/-- `signContract H G`, for the hash functions `H` and `G` that `hash` and
`mgf1_hash` name (`hashIds`), with the digest `digest_len = hLen` octets.
Constant time but for the public key and the hash functions. -/
def signAnyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  signAnySig.contract A
    (pre := fun _out outLen _n nLen _e eLen _p pLen _q qLen _dp dpLen _dq dqLen _qinv qinvLen
        _digest digestLen _salt _saltLen _scratch scratchLen hash mgf1Hash _hashFns _mgf1Fns _ =>
      hash.toNat ∈ hashIds ∧ mgf1Hash.toNat ∈ hashIds ∧
        (∀ H, HashId.mgf1 hash.toNat = some H → digestLen.toNat = H.len) ∧
        lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun out _outLen n nLen e eLen p pLen q qLen dp _dpLen dq _dqLen qinv _qinvLen
        digest digestLen salt saltLen _scratch _scratchLen hash mgf1Hash _hashFns _mgf1Fns m m' r =>
      ∀ H G, HashId.mgf1 hash.toNat = some H → HashId.mgf1 mgf1Hash.toNat = some G →
        writtenOutcome m' out nLen.toNat r
          (sign H G (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m p pLen.toNat)
            (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat) (bytesAt m dq qLen.toNat)
            (bytesAt m qinv pLen.toNat) (bytesAt m digest digestLen.toNat)
            (bytesAt m salt saltLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _p _pLen _q _qLen _dp _dpLen _dq _dqLen _qinv
        _qinvLen _digest _digestLen _salt _saltLen _scratch _scratchLen _hash _mgf1Hash hashFns mgf1Fns m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        HashFns.tableWords m hashFns ++ HashFns.tableWords m mgf1Fns)
    (fns := some fun _out _outLen _n _nLen _e _eLen _p _pLen _q _qLen _dp _dpLen _dq _dqLen _qinv
        _qinvLen _digest _digestLen _salt _saltLen _scratch _scratchLen hash mgf1Hash hashFns mgf1Fns m
        meets =>
      HashFns.tableOf hash.toNat m hashFns meets ∧ HashFns.tableOf mgf1Hash.toNat m mgf1Fns meets)

/-- `vg_rsa_pss_sign` on every target. -/
def signAnyApi : Api where
  module := "rsa_pss"
  name := "vg_rsa_pss_sign"
  sig := signAnySig
  writeArgs := true
  contracts := some fun A stack => signAnyContract A stack
  summary := s!"RSASSA-PSS signature generation (RFC 8017 §8.1.1) with the hash function \
    `hash` names and MGF1 with the one `mgf1_hash` names, of a digest, with the private key \
    `(p, q, dP, dQ, qInv)` checked against the public exponent as `vg_rsa_private_checked` \
    checks it. With the modulus `n` (`n_len` bytes, most significant first, odd, from 512 \
    to 8192 bits, its first byte not zero) and {exponentDoc}, encodes the digest `digest` \
    (`hLen` bytes, the length of `hash`'s values) with the salt `salt` (EMSA-PSS, RFC 8017 \
    §9.1.1) and computes RSASP1 of the encoding: if it passes the check against `e`, writes \
    the signature (`n_len` bytes, most significant first) to `out` and returns 1. Writes \
    zeros and returns 0 if the salt does not fit (`salt_len` more than \
    `⌈(bits of n - 1) / 8⌉ - hLen - 2`), or the key is refused as `vg_rsa_private_checked` \
    refuses it; writes zeros and returns 2 (an internal error) if the result fails the \
    check against `e`, which it does for no digest if `vg_rsa_check_key` accepts the key \
    and `p` and `q` are prime. The salt must be fresh random bytes for each signature (or \
    empty). {hashIdsDoc}.\n\n\
    Contract: `VG.Spec.RsaPss.signAnyContract`. Constant time but for the public key: timing \
    may depend on the pointers, the lengths, `hash`, `mgf1_hash` and the contents of `n`, \
    `e`, `hash_fns` and `mgf1_fns`, not on the private key, the digest or the salt."
  safety := hashSafety ++ ["`n_len` must be in 64..=1024.", "`out_len` must be `n_len`.",
    "`e_len` must be in 1..=`n_len`.", "`p_len` and `q_len` must be in 1..`n_len`.",
    "`dp_len` and `qinv_len` must be `p_len`, and `dq_len` must be `q_len`."] ++
    scratchSafety

/-! ## `vg_rsa_pss_verify_precomputed` -/

/-- `vg_rsa_pss_verify_precomputed(n: *const u8, n_len: usize, e: *const u8,
e_len: usize, digest: *const u8, digest_len: usize, sig: *const u8,
sig_len: usize, any_salt_len: u32, salt_len: usize, scratch: *mut u64,
scratch_len: usize, pre: *const u64, pre_len: usize, hash: usize,
mgf1_hash: usize, hash_fns: *const [u64; 3], mgf1_fns: *const [u64; 3]) -> u32`. -/
def verifyAnySig : Sig where
  params := [("n", .slice false .u8 "n_len"), ("e", .slice false .u8 "e_len"),
    ("digest", .slice false .u8 "digest_len"), ("sig", .slice false .u8 "sig_len"),
    ("any_salt_len", .int .u32 true), ("salt_len", .int .usize true),
    ("scratch", .slice true .u64 "scratch_len"), ("pre", .slice false .u64 "pre_len"),
    ("hash", .int .usize true), ("mgf1_hash", .int .usize true),
    ("hash_fns", .array false .u64 3), ("mgf1_fns", .array false .u64 3)]
  ret := some .u32

/-- `verifyPrecomputedContract H G`, for the hash functions `H` and `G` that
`hash` and `mgf1_hash` name (`hashIds`), with the digest `digest_len = hLen`
octets. -/
def verifyAnyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  verifyAnySig.contract A
    (pre := fun _n nLen _e eLen _digest digestLen _sig sigLen _anySaltLen _saltLen _scratch
        scratchLen _pre preLen hash mgf1Hash _hashFns _mgf1Fns _ =>
      hash.toNat ∈ hashIds ∧ mgf1Hash.toNat ∈ hashIds ∧
        (∀ H, HashId.mgf1 hash.toNat = some H → digestLen.toNat = H.len) ∧
        lenValid nLen.toNat ∧ 1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        sigLen.toNat = nLen.toNat ∧ publicScratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Rsa.precomputedWords nLen.toNat)
    (post := fun n nLen e eLen digest digestLen sig _sigLen anySaltLen saltLen _scratch
        _scratchLen pre preLen hash mgf1Hash _hashFns _mgf1Fns m _m' r =>
      ∀ H G, HashId.mgf1 hash.toNat = some H → HashId.mgf1 mgf1Hash.toNat = some G →
        Rsa.publicPrecompute (bytesAt m n nLen.toNat) = some (Rsa.wordsAt m pre preLen.toNat) →
          r = if verify H G (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat)
              (bytesAt m digest digestLen.toNat) (bytesAt m sig nLen.toNat)
              (expectedSaltLen saltLen anySaltLen) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun n nLen e eLen _digest _digestLen _sig _sigLen _anySaltLen _saltLen _scratch
        _scratchLen pre preLen _hash _mgf1Hash hashFns mgf1Fns m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        (Rsa.wordsAt m pre preLen.toNat).map (·.toNat) ++ HashFns.tableWords m hashFns ++
        HashFns.tableWords m mgf1Fns)
    (fns := some fun _n _nLen _e _eLen _digest _digestLen _sig _sigLen _anySaltLen _saltLen _scratch
        _scratchLen _pre _preLen hash mgf1Hash hashFns mgf1Fns m meets =>
      HashFns.tableOf hash.toNat m hashFns meets ∧ HashFns.tableOf mgf1Hash.toNat m mgf1Fns meets)

/-- `vg_rsa_pss_verify_precomputed` on every target. -/
def verifyAnyApi : Api where
  module := "rsa_pss"
  name := "vg_rsa_pss_verify_precomputed"
  sig := verifyAnySig
  writeArgs := true
  contracts := some fun A stack => verifyAnyContract A stack
  summary := s!"RSASSA-PSS signature verification (RFC 8017 §8.1.2) with the hash function \
    `hash` names and MGF1 with the one `mgf1_hash` names, of a signature of a digest. With \
    the modulus `n` (`n_len` bytes, most significant first, odd, from 512 to 8192 bits, its \
    first byte not zero) and {exponentDoc}, returns 1 if `sig` (`n_len` bytes, most \
    significant first) is an RSASSA-PSS signature of the digest `digest` (`hLen` bytes, the \
    length of `hash`'s values) with a salt of `salt_len` bytes, or of any length if \
    `any_salt_len` is not zero (BoringSSL's `RSA_PSS_SALTLEN_AUTO`); and 0 if it is not, or \
    if `n` is not such a modulus, `e` is not such a number, or `sig` is not below `n`. \
    {hashIdsDoc}.\n\n\
    It also takes `pre`, the `pre_len` words written by `vg_rsa_public_precompute` for `n` \
    (returning 1). With those values, it returns exactly the result specified above. If \
    `pre` does not hold those values, the result is unspecified; memory safety and the \
    timing guarantee still apply.\n\n\
    Contract: `VG.Spec.RsaPss.verifyAnyContract`. Constant time but for the public key: \
    timing may depend on the pointers, the lengths, `salt_len`, `any_salt_len`, `hash`, \
    `mgf1_hash` and the contents of `n`, `e`, `pre`, `hash_fns` and `mgf1_fns`, not on the \
    digest, the signature or \
    anything computed from them but the result."
  safety := hashSafety ++ ["`n_len` must be in 64..=1024.", "`sig_len` must be `n_len`.",
    "`e_len` must be in 1..=`n_len`."] ++ publicScratchSafety ++
    ["`pre_len` must be `2 * ⌈n_len / 8⌉`.",
      "For the result to be signature verification's, `pre` must hold what \
        `vg_rsa_public_precompute` wrote for `n` (returning 1)."]

end VG.Spec.RsaPss
