import VerifiedGarbage.Spec.RsaOaep
import VerifiedGarbage.Spec.RsaPss.Contract

/-!
# RSAES-OAEP: the contracts, on every target

**Trusted** (as every file in `Spec/`). For the hash function `H` and MGF1
with the hash function `G` (any two of `Mgf1.hashes`), in the module
`rsa_oaep_<H>_mgf1_<G>`:

* `vg_rsa_oaep_<H>_mgf1_<G>_encrypt`: `RSAES-OAEP-ENCRYPT` of a message with
  a label and a seed (`RsaOaep.encrypt`);
* `vg_rsa_oaep_<H>_mgf1_<G>_decrypt`: `RSAES-OAEP-DECRYPT` of a ciphertext
  with a label, with the private key checked against the public exponent
  (`RsaOaep.decrypt`).

Numbers are as in `Spec/Rsa/Contract.lean`: slices of octets, most
significant first, with the modulus `n` of `n_len` octets, from 64 to 1024,
and `e` of at most `n_len`; the private key is as `vg_rsa_private_checked`
takes it. The seed is `hLen` octets, an array. These are preconditions, on
the public lengths; everything about the values is checked. Encryption
returns 1 and writes the ciphertext, or returns 0 and writes zeros.
Decryption returns 1 and writes the message, padded with zeros to `n_len`
octets, and its length; or writes zeros and returns 0, the single error for
every failure of the key, the ciphertext or its decoding, or 2 (the internal
error: RSADP's result failed its check against `e`).

The signature determines memory validity, separation and that the pointers
and lengths (among them the message's and the label's) are public, through
`Sig.contract`. The public key, `n` and `e`, is public too, and may affect
timing (`leak`). Nothing else is: the message, the label, the seed, the
private key, the ciphertext and everything computed from them, among them
whether the decoding is valid, where the message starts and its length:
only the returned value says whether decryption succeeded, and the message
and its length are its output.

`scratch` is working space of at least `RsaPss.scratchWords n_len` `u64`s,
whose contents on return are unspecified. `stack` is the number of bytes
below the stack pointer that an implementation's calls and frames use. The
functions may overwrite their arguments passed in memory, where the calling
convention allows it (`writeArgs`).
-/

namespace VG.Spec.RsaOaep

open Mgf1 (Hash)
open Rsa (bytesAt lenValid written exponentDoc Outcome)
open RsaPss (scratchWords scratchSafety)

variable (H G : Hash)

/-! ## `vg_rsa_oaep_<H>_mgf1_<G>_encrypt` -/

/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt(out: *mut u8, out_len: usize,
n: *const u8, n_len: usize, e: *const u8, e_len: usize, label: *const u8,
label_len: usize, msg: *const u8, msg_len: usize, seed: *const [u8; hLen],
scratch: *mut u64, scratch_len: usize) -> u32`. -/
def encryptSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("label", .slice false .u8 "label_len"),
    ("msg", .slice false .u8 "msg_len"), ("seed", .array false .u8 H.len),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- `RSAES-OAEP-ENCRYPT` of the message with the label and the seed, with the
public key `(n, e)` (`encrypt`). Constant time but for the public key and
the lengths. -/
def encryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (encryptSig H).contract A
    (pre := fun _out outLen _n nLen _e eLen _label _labelLen _msg _msgLen _seed _scratch
        scratchLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ 1 ≤ eLen.toNat ∧
        eLen.toNat ≤ nLen.toNat ∧ scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun out _outLen n nLen e eLen label labelLen msg msgLen seed _scratch _scratchLen
        m m' r =>
      written m' out nLen.toNat r
        (encrypt H G (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat)
          (bytesAt m label labelLen.toNat) (bytesAt m msg msgLen.toNat) (bytesAt m seed H.len)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _label _labelLen _msg _msgLen _seed _scratch
        _scratchLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat))

/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt` on every target. -/
def encryptApi : Api where
  module := s!"rsa_oaep_{H.rust}_mgf1_{G.rust}"
  name := s!"vg_rsa_oaep_{H.rust}_mgf1_{G.rust}_encrypt"
  sig := encryptSig H
  writeArgs := true
  contracts := some fun A stack => encryptContract H G A stack
  summary := s!"RSAES-OAEP encryption (RFC 8017 §7.1.1) with {H.name} and MGF1 with {G.name}. \
    With the modulus `n` (`n_len` bytes, most significant first, odd, from 512 to 8192 bits, \
    its first byte not zero) and the public exponent `e` (`e_len` bytes, most significant \
    first), writes the encryption of the message `msg` with the label `label` and the \
    {H.len}-byte seed `*seed` (`n_len` bytes, most significant first) to `out` and returns 1; \
    or writes zeros and returns 0 if `n` is not such a modulus or the message is longer than \
    `n_len - {2 * H.len + 2}` bytes. The seed must be fresh random bytes for each encryption.\n\n\
    Contract: `VG.Spec.RsaOaep.encryptContract` of `VG.Spec.Mgf1.{H.lean}` and \
    `VG.Spec.Mgf1.{G.lean}`. Constant time but for the public key: timing may depend on the \
    pointers, the lengths and the contents of `n` and `e`, not on the message, the label or \
    the seed."
  safety := ["`n_len` must be in 64..=1024.", "`out_len` must be `n_len`.",
    "`e_len` must be in 1..=`n_len`."] ++ scratchSafety

/-! ## `vg_rsa_oaep_<H>_mgf1_<G>_decrypt` -/

/-- What decryption with the outcome `o` writes to the `nLen` octets at `out`
and the length at `len`, and returns: 1, the message padded with zeros to
`nLen` octets and its length; or 0 (the single error) or 2 (the internal
error), zeros and the length 0. -/
def writtenDecrypt (m' : Mem) (out len : Addr) (nLen : Nat) (r : BitVec 32) : Outcome → Prop
  | .ok msg => r = 1 ∧ bytesAt m' out nLen = msg ++ zeros (nLen - msg.length) ∧
      m'.readW len 64 = BitVec.ofNat 64 msg.length
  | .invalid => r = 0 ∧ bytesAt m' out nLen = zeros nLen ∧ m'.readW len 64 = 0
  | .fault => r = 2 ∧ bytesAt m' out nLen = zeros nLen ∧ m'.readW len 64 = 0

/-- `vg_rsa_oaep_<H>_mgf1_<G>_decrypt(out: *mut u8, out_len: usize,
msg_len: *mut [u64; 1], n: *const u8, n_len: usize, e: *const u8,
e_len: usize, p: *const u8, p_len: usize, q: *const u8, q_len: usize,
dp: *const u8, dp_len: usize, dq: *const u8, dq_len: usize,
qinv: *const u8, qinv_len: usize, label: *const u8, label_len: usize,
ct: *const u8, ct_len: usize, scratch: *mut u64, scratch_len: usize)
-> u32`. -/
def decryptSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("msg_len", .array true .u64 1),
    ("n", .slice false .u8 "n_len"), ("e", .slice false .u8 "e_len"),
    ("p", .slice false .u8 "p_len"), ("q", .slice false .u8 "q_len"),
    ("dp", .slice false .u8 "dp_len"), ("dq", .slice false .u8 "dq_len"),
    ("qinv", .slice false .u8 "qinv_len"), ("label", .slice false .u8 "label_len"),
    ("ct", .slice false .u8 "ct_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- `RSAES-OAEP-DECRYPT` of the ciphertext with the label, with the private
key `(p, q, dP, dQ, qInv)` of the modulus `n` checked against the public
exponent `e` (`decrypt`). Constant time but for the public key. -/
def decryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decryptSig.contract A
    (pre := fun _out outLen _msgLen _n nLen _e eLen _p pLen _q qLen _dp dpLen _dq dqLen _qinv
        qinvLen _label _labelLen _ct ctLen _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ ctLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun out _outLen msgLen n nLen e eLen p pLen q qLen dp _dpLen dq _dqLen qinv
        _qinvLen label labelLen ct _ctLen _scratch _scratchLen m m' r =>
      writtenDecrypt m' out msgLen nLen.toNat r
        (decrypt H G (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m p pLen.toNat)
          (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat) (bytesAt m dq qLen.toNat)
          (bytesAt m qinv pLen.toNat) (bytesAt m label labelLen.toNat)
          (bytesAt m ct nLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _msgLen n nLen e eLen _p _pLen _q _qLen _dp _dpLen _dq
        _dqLen _qinv _qinvLen _label _labelLen _ct _ctLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat))

/-- `vg_rsa_oaep_<H>_mgf1_<G>_decrypt` on every target. -/
def decryptApi : Api where
  module := s!"rsa_oaep_{H.rust}_mgf1_{G.rust}"
  name := s!"vg_rsa_oaep_{H.rust}_mgf1_{G.rust}_decrypt"
  sig := decryptSig
  writeArgs := true
  contracts := some fun A stack => decryptContract H G A stack
  summary := s!"RSAES-OAEP decryption (RFC 8017 §7.1.2) with {H.name} and MGF1 with {G.name}, \
    with the private key `(p, q, dP, dQ, qInv)` checked against the public exponent as \
    `vg_rsa_private_checked` checks it. With the modulus `n` (`n_len` bytes, most \
    significant first, odd, from 512 to 8192 bits, its first byte not zero) and \
    {exponentDoc}, decrypts the ciphertext `ct` (`n_len` bytes, most significant first) with \
    the label `label`: if RSADP's result passes the check against `e` and is a valid \
    EME-OAEP encoding, writes the message to the start of `out`, zeros after it, and its \
    length to `*msg_len`, and returns 1. Otherwise writes zeros to `out` and `*msg_len` and \
    returns 0 for every failure of the key, the ciphertext (not below `n`) or its decoding, \
    which are not told apart; or 2 (an internal error) if RSADP's result fails the check \
    against `e`, which it does for no ciphertext if `vg_rsa_check_key` accepts the key and \
    `p` and `q` are prime.\n\n\
    Contract: `VG.Spec.RsaOaep.decryptContract` of `VG.Spec.Mgf1.{H.lean}` and \
    `VG.Spec.Mgf1.{G.lean}`. Constant time but for the public key: timing may depend on the \
    pointers, the lengths and the contents of `n` and `e`, not on the private key, the \
    label, the ciphertext, whether its decoding is valid or the message's length."
  safety := ["`n_len` must be in 64..=1024.", "`out_len` and `ct_len` must be `n_len`.",
    "`e_len` must be in 1..=`n_len`.", "`p_len` and `q_len` must be in 1..`n_len`.",
    "`dp_len` and `qinv_len` must be `p_len`, and `dq_len` must be `q_len`."] ++
    scratchSafety

end VG.Spec.RsaOaep
