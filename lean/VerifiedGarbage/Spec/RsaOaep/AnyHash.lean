module

public import VerifiedGarbage.Spec.RsaOaep.Precomputed
public import VerifiedGarbage.Spec.HashFns

/-!
# RSAES-OAEP with the hash functions as arguments: the contracts, on every target

**Trusted** (as every file in `Spec/`). The functions of
`Spec/RsaOaep/Contract.lean` and `Spec/RsaOaep/Precomputed.lean`, but with
the hash function `H` (the label's) and MGF1's hash function `G` passed as
arguments rather than fixed by the function's name: each as the number
`HashId.mgf1` gives it, one of `hashIds` (SHA-1 and the SHA-2 functions), a
public `usize` (`hash`, `mgf1_hash`), and a table of its streaming functions
(`hash_fns`, `mgf1_fns`: `HashFns.tableOf`), which the function calls, in the
module `rsa_oaep`:

* `vg_rsa_oaep_encrypt_precomputed`: `encryptPrecomputedContract H G`,
  with the seed a slice of `hLen` octets rather than an array;
* `vg_rsa_oaep_decrypt`: `decryptContract H G`.

That `hash` and `mgf1_hash` are in `hashIds`, that the tables hold their
streaming functions, and that the seed is `H`'s `hLen` octets, are
preconditions. The hash functions and their tables (the addresses of the
functions) are public (arguments marked so, and the tables' words, `leak`),
and may affect timing; nothing else changes.
-/

@[expose] public section

namespace VG.Spec.RsaOaep

open Mgf1 (Hash)
open Rsa (bytesAt lenValid written exponentDoc)
open RsaPss (scratchWords scratchSafety publicScratchWords publicScratchSafety)

/-- The numbers (`HashId.mgf1`) of the hash functions these functions take,
both as the label's and as MGF1's: SHA-1, SHA-224, SHA-256, SHA-384,
SHA-512, SHA-512/224 and SHA-512/256. -/
def hashIds : List Nat := [1, 2, 3, 4, 5, 6, 7]

/-- The documentation's list of the hash functions' numbers. -/
def hashIdsDoc : String :=
  s!"`hash` names the label's hash function and `mgf1_hash` MGF1's: {HashId.sha12Doc}; \
    `hash_fns` and `mgf1_fns` point to tables of their streaming functions, which it calls \
    (`VG.Spec.HashFns`)"

/-! ## `vg_rsa_oaep_encrypt_precomputed` -/

/-- `vg_rsa_oaep_encrypt_precomputed(out: *mut u8, out_len: usize,
n: *const u8, n_len: usize, e: *const u8, e_len: usize, label: *const u8,
label_len: usize, msg: *const u8, msg_len: usize, seed: *const u8,
seed_len: usize, scratch: *mut u64, scratch_len: usize, pre: *const u64,
pre_len: usize, hash: usize, mgf1_hash: usize, hash_fns: *const [u64; 3],
mgf1_fns: *const [u64; 3]) -> u32`. -/
def encryptAnySig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("label", .slice false .u8 "label_len"),
    ("msg", .slice false .u8 "msg_len"), ("seed", .slice false .u8 "seed_len"),
    ("scratch", .slice true .u64 "scratch_len"), ("pre", .slice false .u64 "pre_len"),
    ("hash", .int .usize true), ("mgf1_hash", .int .usize true),
    ("hash_fns", .array false .u64 3), ("mgf1_fns", .array false .u64 3)]
  ret := some .u32

/-- `encryptPrecomputedContract H G`, for the hash functions `H` and `G`
that `hash` and `mgf1_hash` name (`hashIds`), with the seed `seed_len = hLen`
octets. Constant time but for the public key, its precomputed values, the
hash functions and the lengths. -/
def encryptAnyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptAnySig.contract A
    (pre := fun _out outLen _n nLen _e eLen _label _labelLen _msg _msgLen _seed seedLen _scratch
        scratchLen _pre preLen hash mgf1Hash _hashFns _mgf1Fns _ =>
      hash.toNat ∈ hashIds ∧ mgf1Hash.toNat ∈ hashIds ∧
        (∀ H, HashId.mgf1 hash.toNat = some H → seedLen.toNat = H.len) ∧
        lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ 1 ≤ eLen.toNat ∧
        eLen.toNat ≤ nLen.toNat ∧ publicScratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Rsa.precomputedWords nLen.toNat)
    (post := fun out _outLen n nLen e eLen label labelLen msg msgLen seed seedLen _scratch
        _scratchLen pre preLen hash mgf1Hash _hashFns _mgf1Fns m m' r =>
      ∀ H G, HashId.mgf1 hash.toNat = some H → HashId.mgf1 mgf1Hash.toNat = some G →
        Rsa.publicPrecompute (bytesAt m n nLen.toNat) = some (Rsa.wordsAt m pre preLen.toNat) →
          written m' out nLen.toNat r
            (encrypt H G (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat)
              (bytesAt m label labelLen.toNat) (bytesAt m msg msgLen.toNat)
              (bytesAt m seed seedLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _label _labelLen _msg _msgLen _seed _seedLen
        _scratch _scratchLen pre preLen _hash _mgf1Hash hashFns mgf1Fns m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        (Rsa.wordsAt m pre preLen.toNat).map (·.toNat) ++ HashFns.tableWords m hashFns ++
        HashFns.tableWords m mgf1Fns)
    (fns := some fun _out _outLen _n _nLen _e _eLen _label _labelLen _msg _msgLen _seed _seedLen
        _scratch _scratchLen _pre _preLen hash mgf1Hash hashFns mgf1Fns m meets =>
      HashFns.tableOf hash.toNat m hashFns meets ∧ HashFns.tableOf mgf1Hash.toNat m mgf1Fns meets)

/-- `vg_rsa_oaep_encrypt_precomputed` on every target. -/
def encryptAnyApi : Api where
  module := "rsa_oaep"
  name := "vg_rsa_oaep_encrypt_precomputed"
  sig := encryptAnySig
  writeArgs := true
  contracts := some fun A stack => encryptAnyContract A stack
  summary := s!"RSAES-OAEP encryption (RFC 8017 §7.1.1) with the hash function `hash` names \
    and MGF1 with the one `mgf1_hash` names. With the modulus `n` (`n_len` bytes, most \
    significant first, odd, from 512 to 8192 bits, its first byte not zero) and the public \
    exponent `e` (`e_len` bytes, most significant first), writes the encryption of the \
    message `msg` with the label `label` and the seed `seed` (`hLen` bytes, the length of \
    `hash`'s values) (`n_len` bytes, most significant first) to `out` and returns 1; or \
    writes zeros and returns 0 if `n` is not such a modulus or the message is longer than \
    `n_len - 2 hLen - 2` bytes. The seed must be fresh random bytes for each encryption. \
    {hashIdsDoc}.\n\n\
    It also takes `pre`, the `pre_len` words written by `vg_rsa_public_precompute` for `n` \
    (returning 1). With those values, it writes and returns exactly what is specified above. \
    If `pre` does not hold those values, what it writes and returns is unspecified; memory \
    safety and the timing guarantee still apply.\n\n\
    Contract: `VG.Spec.RsaOaep.encryptAnyContract`. Constant time but for the public key: \
    timing may depend on the pointers, the lengths, `hash`, `mgf1_hash` and the contents of \
    `n`, `e`, `pre`, `hash_fns` and `mgf1_fns`, not on the message, the label or the seed."
  safety := ["`hash` and `mgf1_hash` must each be one of 1..=7.",
    HashFns.tableSafety "hash_fns" "hash", HashFns.tableSafety "mgf1_fns" "mgf1_hash",
    HashId.lenSafety "seed_len" "hash",
    "`n_len` must be in 64..=1024.", "`out_len` must be `n_len`.",
    "`e_len` must be in 1..=`n_len`."] ++ publicScratchSafety ++
    ["`pre_len` must be `2 * ⌈n_len / 8⌉`.",
      "For the result to be encryption's, `pre` must hold what \
        `vg_rsa_public_precompute` wrote for `n` (returning 1)."]

/-! ## `vg_rsa_oaep_decrypt` -/

/-- `vg_rsa_oaep_decrypt(out: *mut u8, out_len: usize,
msg_len: *mut [u64; 1], n: *const u8, n_len: usize, e: *const u8,
e_len: usize, p: *const u8, p_len: usize, q: *const u8, q_len: usize,
dp: *const u8, dp_len: usize, dq: *const u8, dq_len: usize,
qinv: *const u8, qinv_len: usize, label: *const u8, label_len: usize,
ct: *const u8, ct_len: usize, scratch: *mut u64, scratch_len: usize,
hash: usize, mgf1_hash: usize, hash_fns: *const [u64; 3],
mgf1_fns: *const [u64; 3]) -> u32`. -/
def decryptAnySig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("msg_len", .array true .u64 1),
    ("n", .slice false .u8 "n_len"), ("e", .slice false .u8 "e_len"),
    ("p", .slice false .u8 "p_len"), ("q", .slice false .u8 "q_len"),
    ("dp", .slice false .u8 "dp_len"), ("dq", .slice false .u8 "dq_len"),
    ("qinv", .slice false .u8 "qinv_len"), ("label", .slice false .u8 "label_len"),
    ("ct", .slice false .u8 "ct_len"), ("scratch", .slice true .u64 "scratch_len"),
    ("hash", .int .usize true), ("mgf1_hash", .int .usize true),
    ("hash_fns", .array false .u64 3), ("mgf1_fns", .array false .u64 3)]
  ret := some .u32

/-- `decryptContract H G`, for the hash functions `H` and `G` that `hash`
and `mgf1_hash` name (`hashIds`). Constant time but for the public key and
the hash functions. -/
def decryptAnyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decryptAnySig.contract A
    (pre := fun _out outLen _msgLen _n nLen _e eLen _p pLen _q qLen _dp dpLen _dq dqLen _qinv
        qinvLen _label _labelLen _ct ctLen _scratch scratchLen hash mgf1Hash _hashFns _mgf1Fns _ =>
      hash.toNat ∈ hashIds ∧ mgf1Hash.toNat ∈ hashIds ∧
        lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ ctLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun out _outLen msgLen n nLen e eLen p pLen q qLen dp _dpLen dq _dqLen qinv
        _qinvLen label labelLen ct _ctLen _scratch _scratchLen hash mgf1Hash _hashFns _mgf1Fns m m' r =>
      ∀ H G, HashId.mgf1 hash.toNat = some H → HashId.mgf1 mgf1Hash.toNat = some G →
        writtenDecrypt m' out msgLen nLen.toNat r
          (decrypt H G (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m p pLen.toNat)
            (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat) (bytesAt m dq qLen.toNat)
            (bytesAt m qinv pLen.toNat) (bytesAt m label labelLen.toNat)
            (bytesAt m ct nLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _msgLen n nLen e eLen _p _pLen _q _qLen _dp _dpLen _dq
        _dqLen _qinv _qinvLen _label _labelLen _ct _ctLen _scratch _scratchLen _hash _mgf1Hash hashFns
        mgf1Fns m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        HashFns.tableWords m hashFns ++ HashFns.tableWords m mgf1Fns)
    (fns := some fun _out _outLen _msgLen _n _nLen _e _eLen _p _pLen _q _qLen _dp _dpLen _dq _dqLen
        _qinv _qinvLen _label _labelLen _ct _ctLen _scratch _scratchLen hash mgf1Hash hashFns mgf1Fns
        m meets =>
      HashFns.tableOf hash.toNat m hashFns meets ∧ HashFns.tableOf mgf1Hash.toNat m mgf1Fns meets)

/-- `vg_rsa_oaep_decrypt` on every target. -/
def decryptAnyApi : Api where
  module := "rsa_oaep"
  name := "vg_rsa_oaep_decrypt"
  sig := decryptAnySig
  writeArgs := true
  contracts := some fun A stack => decryptAnyContract A stack
  summary := s!"RSAES-OAEP decryption (RFC 8017 §7.1.2) with the hash function `hash` names \
    and MGF1 with the one `mgf1_hash` names, with the private key `(p, q, dP, dQ, qInv)` \
    checked against the public exponent as `vg_rsa_private_checked` checks it. With the \
    modulus `n` (`n_len` bytes, most significant first, odd, from 512 to 8192 bits, its \
    first byte not zero) and {exponentDoc}, decrypts the ciphertext `ct` (`n_len` bytes, \
    most significant first) with the label `label`: if RSADP's result passes the check \
    against `e` and is a valid EME-OAEP encoding, writes the message to the start of `out`, \
    zeros after it, and its length to `*msg_len`, and returns 1. Otherwise writes zeros to \
    `out` and `*msg_len` and returns 0 for every failure of the key, the ciphertext (not \
    below `n`) or its decoding, which are not told apart; or 2 (an internal error) if \
    RSADP's result fails the check against `e`, which it does for no ciphertext if \
    `vg_rsa_check_key` accepts the key and `p` and `q` are prime. {hashIdsDoc}.\n\n\
    Contract: `VG.Spec.RsaOaep.decryptAnyContract`. Constant time but for the public key: \
    timing may depend on the pointers, the lengths, `hash`, `mgf1_hash` and the contents of \
    `n`, `e`, `hash_fns` and `mgf1_fns`, not on the private key, the label, the ciphertext, \
    whether its decoding is valid or the message's length."
  safety := ["`hash` and `mgf1_hash` must each be one of 1..=7.",
    HashFns.tableSafety "hash_fns" "hash", HashFns.tableSafety "mgf1_fns" "mgf1_hash",
    "`n_len` must be in 64..=1024.", "`out_len` and `ct_len` must be `n_len`.",
    "`e_len` must be in 1..=`n_len`.", "`p_len` and `q_len` must be in 1..`n_len`.",
    "`dp_len` and `qinv_len` must be `p_len`, and `dq_len` must be `q_len`."] ++
    scratchSafety

end VG.Spec.RsaOaep
