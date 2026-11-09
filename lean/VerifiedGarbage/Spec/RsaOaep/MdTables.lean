module

public import VerifiedGarbage.Spec.RsaOaep.Tables
public import VerifiedGarbage.Spec.MdHashTable

/-!
# RSAES-OAEP with both of its hash functions given as tables of `MdHash`

**Trusted** (as every file in `Spec/`). The functions of
`Spec/RsaOaep/Tables.lean`, `vg_rsa_oaep_encrypt_precomputed` and
`vg_rsa_oaep_decrypt`, with the same contracts but for the tables they take:
`hash` and `mgf1` are tables of the interface `MdHash`
(`Spec/MdHashTable.lean`), naming `H` and `G` by `MdHashTable.hashAt`,
rather than of `Hash`. So the tables of `MdHash`, which the other functions
taking hash functions as tables take, serve RSAES-OAEP too, and the
interface `Hash` can go once nothing implements those of
`Spec/RsaOaep/Tables.lean`.
-/

@[expose] public section

namespace VG.Spec.RsaOaep

open Mgf1 (Hash)
open Rsa (bytesAt lenValid written exponentDoc)
open RsaPss (scratchWords scratchSafety publicScratchWords)

/-- The seed's length is that of the hash function the table at `hash`
names, if it names one. -/
def seedLenMdOk {w : Nat} (ptrBits : Nat) (m : Mem) (hash : Addr) (seedLen : BitVec w) : Prop :=
  ∀ H, MdHashTable.hashAt ptrBits m hash = some H → seedLen.toNat = H.len

/-! ## `vg_rsa_oaep_encrypt_precomputed` -/

/-- The parameters of encryption: `(out: *mut u8, out_len: usize,
n: *const u8, n_len: usize, e: *const u8, e_len: usize, label: *const u8,
label_len: usize, msg: *const u8, msg_len: usize, seed: *const u8,
seed_len: usize, scratch: *mut u64, scratch_len: usize, pre: *const u64,
pre_len: usize, hash: *const [usize; 11], mgf1: *const [usize; 11]) -> u32`,
with `pre` the modulus' precomputed `u64` words and `hash` and `mgf1` tables
of `MdHash`. -/
def encryptMdTablesSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("label", .slice false .u8 "label_len"),
    ("msg", .slice false .u8 "msg_len"), ("seed", .slice false .u8 "seed_len"),
    ("scratch", .slice true .u64 "scratch_len"), ("pre", .slice false .u64 "pre_len"),
    ("hash", MdHashTable.param), ("mgf1", MdHashTable.param)]
  ret := some .u32

/-- RSAES-OAEP-ENCRYPT with the hash function `H` the table `hash` names
and MGF1 with `G`, the one `mgf1` names. -/
def encryptMdTablesContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptMdTablesSig.contract A
    (pre := fun _out outLen _n nLen _e eLen _label _labelLen _msg _msgLen _seed seedLen _scratch
        scratchLen _pre preLen hash _mgf1 m =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ 1 ≤ eLen.toNat ∧
        eLen.toNat ≤ nLen.toNat ∧ publicScratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Rsa.precomputedWords nLen.toNat ∧ seedLenMdOk A.ptrBits m hash seedLen)
    (post := fun out _outLen n nLen e eLen label labelLen msg msgLen seed _seedLen _scratch
        _scratchLen pre preLen hash mgf1 m m' r =>
      ∀ H G, MdHashTable.hashAt A.ptrBits m hash = some H →
        MdHashTable.hashAt A.ptrBits m mgf1 = some G →
        Rsa.publicPrecompute (bytesAt m n nLen.toNat) = some (Rsa.wordsAt m pre preLen.toNat) →
          written m' out nLen.toNat r
            (encrypt H G (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat)
              (bytesAt m label labelLen.toNat) (bytesAt m msg msgLen.toNat)
              (bytesAt m seed H.len)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _label _labelLen _msg _msgLen _seed _seedLen
        _scratch _scratchLen pre preLen _hash _mgf1 m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        (Rsa.wordsAt m pre preLen.toNat).map (·.toNat))

/-- `vg_rsa_oaep_encrypt_precomputed` on every target. -/
def encryptMdTablesApi : Api where
  module := "rsa_oaep"
  name := "vg_rsa_oaep_encrypt_precomputed"
  sig := encryptMdTablesSig
  writeArgs := true
  contracts := some fun A stack => encryptMdTablesContract A stack
  summary := "RSAES-OAEP encryption (RFC 8017 §7.1.1) with the hash function of the table \
    `hash` and MGF1 with that of the table `mgf1`. With the modulus `n` (`n_len` bytes, most \
    significant first, odd, from 512 to 8192 bits, its first byte not zero), the public \
    exponent `e` (`e_len` bytes, most significant first) and `pre`, the `pre_len` words \
    written by `vg_rsa_public_precompute` for `n` (returning 1), writes the encryption of the \
    message `msg` with the label `label` and the `seed_len`-byte seed `seed` (`n_len` bytes, \
    most significant first) to `out` and returns 1; or writes zeros and returns 0 if `n` is \
    not such a modulus or the message is longer than `n_len - 2 seed_len - 2` bytes. The seed \
    must be fresh random bytes for each encryption. If `pre` does not hold those values, what \
    it writes and returns is unspecified; memory safety and the timing guarantee still \
    apply.\n\n\
    Contract: `VG.Spec.RsaOaep.encryptMdTablesContract`. Constant time but for the public key: \
    timing may depend on the pointers, the lengths, the contents of `n`, `e` and `pre`, and \
    which tables `hash` and `mgf1` are, not on the message, the label or the seed."
  safety := encryptSafety ++
    ["`seed_len` must be the digest length of the hash function `hash` names.",
      "`pre_len` must be `2 * ⌈n_len / 8⌉`.",
      "For the result to be encryption's, `pre` must hold what \
        `vg_rsa_public_precompute` wrote for `n` (returning 1).", hashSafety, mgf1Safety]

/-! ## `vg_rsa_oaep_decrypt` -/

/-- The parameters of decryption (`decryptSig`), then `hash` and `mgf1`,
tables of `MdHash`. -/
def decryptMdTablesSig : Sig where
  params := decryptSig.params ++ [("hash", MdHashTable.param), ("mgf1", MdHashTable.param)]
  ret := some .u32

/-- RSAES-OAEP-DECRYPT with the hash function `H` the table `hash` names
and MGF1 with `G`, the one `mgf1` names. -/
def decryptMdTablesContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decryptMdTablesSig.contract A
    (pre := fun _out outLen _msgLen _n nLen _e eLen _p pLen _q qLen _dp dpLen _dq dqLen _qinv
        qinvLen _label _labelLen _ct ctLen _scratch scratchLen _hash _mgf1 _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ ctLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun out _outLen msgLen n nLen e eLen p pLen q qLen dp _dpLen dq _dqLen qinv
        _qinvLen label labelLen ct _ctLen _scratch _scratchLen hash mgf1 m m' r =>
      ∀ H G, MdHashTable.hashAt A.ptrBits m hash = some H →
        MdHashTable.hashAt A.ptrBits m mgf1 = some G →
        writtenDecrypt m' out msgLen nLen.toNat r
          (decrypt H G (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat)
            (bytesAt m p pLen.toNat) (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat)
            (bytesAt m dq qLen.toNat) (bytesAt m qinv pLen.toNat)
            (bytesAt m label labelLen.toNat) (bytesAt m ct nLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _msgLen n nLen e eLen _p _pLen _q _qLen _dp _dpLen _dq
        _dqLen _qinv _qinvLen _label _labelLen _ct _ctLen _scratch _scratchLen _hash _mgf1 m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat))

/-- `vg_rsa_oaep_decrypt` on every target. -/
def decryptMdTablesApi : Api where
  module := "rsa_oaep"
  name := "vg_rsa_oaep_decrypt"
  sig := decryptMdTablesSig
  writeArgs := true
  contracts := some fun A stack => decryptMdTablesContract A stack
  summary := "RSAES-OAEP decryption (RFC 8017 §7.1.2) with the hash function of the table \
    `hash` and MGF1 with that of the table `mgf1`, with the private key \
    `(p, q, dP, dQ, qInv)` checked against the public exponent as `vg_rsa_private_checked` \
    checks it. With the modulus `n` (`n_len` bytes, most significant first, odd, from 512 to \
    8192 bits, its first byte not zero) and " ++ exponentDoc ++ ", decrypts the ciphertext \
    `ct` (`n_len` bytes, most significant first) with the label `label`: if RSADP's result \
    passes the check against `e` and is a valid EME-OAEP encoding, writes the message to the \
    start of `out`, zeros after it, and its length to `*msg_len`, and returns 1. Otherwise \
    writes zeros to `out` and `*msg_len` and returns 0 for every failure of the key, the \
    ciphertext (not below `n`) or its decoding, which are not told apart; or 2 (an internal \
    error) if RSADP's result fails the check against `e`, which it does for no ciphertext if \
    `vg_rsa_check_key` accepts the key and `p` and `q` are prime.\n\n\
    Contract: `VG.Spec.RsaOaep.decryptMdTablesContract`. Constant time but for the public key: \
    timing may depend on the pointers, the lengths, the contents of `n` and `e`, and which \
    tables `hash` and `mgf1` are, not on the private key, the label, the ciphertext, whether \
    its decoding is valid or the message's length."
  safety := ["`n_len` must be in 64..=1024.", "`out_len` and `ct_len` must be `n_len`.",
    "`e_len` must be in 1..=`n_len`.", "`p_len` and `q_len` must be in 1..`n_len`.",
    "`dp_len` and `qinv_len` must be `p_len`, and `dq_len` must be `q_len`."] ++
    scratchSafety ++ [hashSafety, mgf1Safety]

end VG.Spec.RsaOaep
