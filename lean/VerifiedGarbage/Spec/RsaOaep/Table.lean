module

public import VerifiedGarbage.Spec.RsaOaep.Precomputed
public import VerifiedGarbage.Spec.HashTable

/-!
# RSAES-OAEP, with MGF1's hash function given as a table

**Trusted** (as every file in `Spec/`). For the hash function `H` (any of
`Mgf1.hashes`), in the module `rsa_oaep_<H>_mgf1`, each with a last
parameter `mgf1`, a table of the interface `Hash` (`Spec/HashTable.lean`),
and MGF1 with the hash function `G` it names (`HashTable.hashAt`):

* `vg_rsa_oaep_<H>_mgf1_encrypt_precomputed`: `RSAES-OAEP-ENCRYPT` of a
  message with a label and a seed (`RsaOaep.encrypt H G`), given the
  modulus' `Rsa.publicPrecompute` values `pre`;
* `vg_rsa_oaep_<H>_mgf1_decrypt`: `RSAES-OAEP-DECRYPT` of a ciphertext with
  a label, with the private key checked against the public exponent
  (`RsaOaep.decrypt H G`).

So one function serves every MGF1 hash function, with every implementation
of it, rather than a function for each.

Numbers are as in `Spec/Rsa/Contract.lean`: slices of octets, most
significant first, with the modulus `n` of `n_len` octets, from 64 to 1024,
and `e` of at most `n_len`; the private key is as `vg_rsa_private_checked`
takes it. The seed is `hLen` octets, an array. These are preconditions, on
the public lengths; everything about the values is checked. Encryption
returns 1 and writes the ciphertext, or returns 0 and writes zeros; with a
`pre` that does not hold the values for `n`, what it writes and returns is
unspecified, as in `Rsa.publicPrecomputedCheckedContract`. Decryption
returns 1 and writes the message, padded with zeros to `n_len` octets, and
its length; or writes zeros and returns 0, the single error for every
failure of the key, the ciphertext or its decoding, or 2 (the internal
error: RSADP's result failed its check against `e`).

The signature determines memory validity, separation and that the pointers
and lengths (among them the message's and the label's) are public, through
`Sig.contract`; which table `mgf1` is, is public too (`Abi.withTables`),
and the table's own memory is read-only. The public key, `n` and `e`, and
`pre` are public, and may affect timing (`leak`). Nothing else is: the
message, the label, the seed, the private key, the ciphertext and
everything computed from them, among them whether the decoding is valid,
where the message starts and its length: only the returned value says
whether decryption succeeded, and the message and its length are its
output.

`scratch` is working space of at least `RsaPss.publicScratchWords n_len`
`u64`s when encrypting and `RsaPss.scratchWords n_len` when decrypting,
whose contents on return are unspecified. `stack` is the number of bytes
below the stack pointer that an implementation's calls and frames use. The
functions may overwrite their arguments passed in memory, where the calling
convention allows it (`writeArgs`).
-/

@[expose] public section

namespace VG.Spec.RsaOaep

open Mgf1 (Hash)
open Rsa (bytesAt lenValid written exponentDoc)
open RsaPss (scratchWords scratchSafety publicScratchWords)

variable (H : Hash)

/-- The `# Safety` item of `mgf1`, but for what the emitter adds (which
tables it may be, `Rust.fnTablesDoc`). -/
def mgf1Safety : String :=
  "`mgf1` names MGF1's hash function: the one of `VG.Spec.Mgf1.hashes` at the index in its \
    first word of data (the hash functions' tables of this crate, `fn_tables`, say which they \
    name)."

/-! ## `vg_rsa_oaep_<H>_mgf1_encrypt_precomputed` -/

/-- `encryptPrecomputedSig` with a last parameter `mgf1: *const [usize; 5]`,
a table of `Hash`. -/
def encryptTableSig : Sig where
  params := (encryptPrecomputedSig H).params ++ [("mgf1", HashTable.param)]
  ret := some .u32

/-- `RSAES-OAEP-ENCRYPT` of the message with the label and the seed, with the
public key `(n, e)` and MGF1 over the hash function `mgf1` names, when `pre`
holds the values for `n`. Constant time but for the public key, its
precomputed values, the lengths and which table `mgf1` is. -/
def encryptTableContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (encryptTableSig H).contract A
    (pre := fun _out outLen _n nLen _e eLen _label _labelLen _msg _msgLen _seed _scratch
        scratchLen _pre preLen _mgf1 _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ 1 ≤ eLen.toNat ∧
        eLen.toNat ≤ nLen.toNat ∧ publicScratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Rsa.precomputedWords nLen.toNat)
    (post := fun out _outLen n nLen e eLen label labelLen msg msgLen seed _scratch _scratchLen
        pre preLen mgf1 m m' r =>
      ∀ G, HashTable.hashAt A.ptrBits m mgf1 = some G →
      Rsa.publicPrecompute (bytesAt m n nLen.toNat) = some (Rsa.wordsAt m pre preLen.toNat) →
        written m' out nLen.toNat r
          (encrypt H G (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat)
            (bytesAt m label labelLen.toNat) (bytesAt m msg msgLen.toNat) (bytesAt m seed H.len)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _label _labelLen _msg _msgLen _seed _scratch
        _scratchLen pre preLen _mgf1 m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        (Rsa.wordsAt m pre preLen.toNat).map (·.toNat))

/-- `vg_rsa_oaep_<H>_mgf1_encrypt_precomputed` on every target. -/
def encryptTableApi : Api where
  module := s!"rsa_oaep_{H.rust}_mgf1"
  name := s!"vg_rsa_oaep_{H.rust}_mgf1_encrypt_precomputed"
  sig := encryptTableSig H
  writeArgs := true
  contracts := some fun A stack => encryptTableContract H A stack
  summary := s!"RSAES-OAEP encryption (RFC 8017 §7.1.1) with {H.name} and MGF1 with the hash \
    function of the table `mgf1`. With the modulus `n` (`n_len` bytes, most significant first, \
    odd, from 512 to 8192 bits, its first byte not zero), the public exponent `e` (`e_len` \
    bytes, most significant first) and `pre`, the `pre_len` words written by \
    `vg_rsa_public_precompute` for `n` (returning 1), writes the encryption of the message \
    `msg` with the label `label` and the {H.len}-byte seed `*seed` (`n_len` bytes, most \
    significant first) to `out` and returns 1; or writes zeros and returns 0 if `n` is not \
    such a modulus or the message is longer than `n_len - {2 * H.len + 2}` bytes. The seed \
    must be fresh random bytes for each encryption. If `pre` does not hold those values, what \
    it writes and returns is unspecified; memory safety and the timing guarantee still \
    apply.\n\n\
    Contract: `VG.Spec.RsaOaep.encryptTableContract` of `VG.Spec.Mgf1.{H.lean}`. Constant time \
    but for the public key: timing may depend on the pointers, the lengths, the contents of \
    `n`, `e` and `pre`, and which table `mgf1` is, not on the message, the label or the seed."
  safety := encryptSafety ++
    ["`pre_len` must be `2 * ⌈n_len / 8⌉`.",
      "For the result to be encryption's, `pre` must hold what \
        `vg_rsa_public_precompute` wrote for `n` (returning 1).", mgf1Safety]

/-! ## `vg_rsa_oaep_<H>_mgf1_decrypt` -/

/-- `decryptSig` with a last parameter `mgf1: *const [usize; 5]`, a table of
`Hash`. -/
def decryptTableSig : Sig where
  params := decryptSig.params ++ [("mgf1", HashTable.param)]
  ret := some .u32

/-- `RSAES-OAEP-DECRYPT` of the ciphertext with the label, with the private
key `(p, q, dP, dQ, qInv)` of the modulus `n` checked against the public
exponent `e`, and MGF1 over the hash function `mgf1` names. Constant time
but for the public key, the lengths and which table `mgf1` is. -/
def decryptTableContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decryptTableSig.contract A
    (pre := fun _out outLen _msgLen _n nLen _e eLen _p pLen _q qLen _dp dpLen _dq dqLen _qinv
        qinvLen _label _labelLen _ct ctLen _scratch scratchLen _mgf1 _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ ctLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun out _outLen msgLen n nLen e eLen p pLen q qLen dp _dpLen dq _dqLen qinv
        _qinvLen label labelLen ct _ctLen _scratch _scratchLen mgf1 m m' r =>
      ∀ G, HashTable.hashAt A.ptrBits m mgf1 = some G →
      writtenDecrypt m' out msgLen nLen.toNat r
        (decrypt H G (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m p pLen.toNat)
          (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat) (bytesAt m dq qLen.toNat)
          (bytesAt m qinv pLen.toNat) (bytesAt m label labelLen.toNat)
          (bytesAt m ct nLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _msgLen n nLen e eLen _p _pLen _q _qLen _dp _dpLen _dq
        _dqLen _qinv _qinvLen _label _labelLen _ct _ctLen _scratch _scratchLen _mgf1 m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat))

/-- `vg_rsa_oaep_<H>_mgf1_decrypt` on every target. -/
def decryptTableApi : Api where
  module := s!"rsa_oaep_{H.rust}_mgf1"
  name := s!"vg_rsa_oaep_{H.rust}_mgf1_decrypt"
  sig := decryptTableSig
  writeArgs := true
  contracts := some fun A stack => decryptTableContract H A stack
  summary := s!"RSAES-OAEP decryption (RFC 8017 §7.1.2) with {H.name} and MGF1 with the hash \
    function of the table `mgf1`, with the private key `(p, q, dP, dQ, qInv)` checked \
    against the public exponent as `vg_rsa_private_checked` checks it. With the modulus `n` \
    (`n_len` bytes, most significant first, odd, from 512 to 8192 bits, its first byte not \
    zero) and {exponentDoc}, decrypts the ciphertext `ct` (`n_len` bytes, most significant \
    first) with the label `label`: if RSADP's result passes the check against `e` and is a \
    valid EME-OAEP encoding, writes the message to the start of `out`, zeros after it, and \
    its length to `*msg_len`, and returns 1. Otherwise writes zeros to `out` and `*msg_len` \
    and returns 0 for every failure of the key, the ciphertext (not below `n`) or its \
    decoding, which are not told apart; or 2 (an internal error) if RSADP's result fails the \
    check against `e`, which it does for no ciphertext if `vg_rsa_check_key` accepts the key \
    and `p` and `q` are prime.\n\n\
    Contract: `VG.Spec.RsaOaep.decryptTableContract` of `VG.Spec.Mgf1.{H.lean}`. Constant \
    time but for the public key: timing may depend on the pointers, the lengths, the \
    contents of `n` and `e`, and which table `mgf1` is, not on the private key, the label, \
    the ciphertext, whether its decoding is valid or the message's length."
  safety := ["`n_len` must be in 64..=1024.", "`out_len` and `ct_len` must be `n_len`.",
    "`e_len` must be in 1..=`n_len`.", "`p_len` and `q_len` must be in 1..`n_len`.",
    "`dp_len` and `qinv_len` must be `p_len`, and `dq_len` must be `q_len`."] ++
    scratchSafety ++ [mgf1Safety]

end VG.Spec.RsaOaep
