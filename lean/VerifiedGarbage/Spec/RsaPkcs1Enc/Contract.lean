module

public import VerifiedGarbage.Spec.RsaPkcs1Enc
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.Artifact

/-!
# RSAES-PKCS1-v1_5 with implicit rejection: the contracts, on every target

**Trusted** (as every file in `Spec/`). In the module `rsa_pkcs1_enc`:

* `vg_rsa_pkcs1_encrypt`: RSAES-PKCS1-V1_5-ENCRYPT (`RsaPkcs1Enc.encrypt`),
  with the padding string drawn by the caller;
* `vg_rsa_pkcs1_decrypt`: RSAES-PKCS1-V1_5-DECRYPT with implicit rejection
  (`RsaPkcs1Enc.decrypt`), with RSADP checked against `e`
  (`Rsa.privateChecked`).

Every number is a slice of octets, most significant first, with a length of
its own, as in `Spec/Rsa/Contract.lean`: the modulus `n` is `n_len` octets,
from 64 to 1024, and so is the ciphertext; `e` is at most `n_len` octets.
These are preconditions, on the public lengths, and so are the lengths of
the message and the padding string; everything about the values is checked:
the function returns 1 and writes its result, or returns 0 (or 2, for the
internal error of `Rsa.privateChecked`) and writes zeros.

The signature determines memory validity, separation and that the pointers
and lengths are public, through `Sig.contract`. The public key, `n` and `e`,
is public too, and may affect timing (`leak`). The message and the padding
string are secret, and so is every part of a private key and the
ciphertext. Nothing else may affect timing: in decryption, whether the
padding is valid, the length of the message `L`, the alternative length
`AL` and which of the two messages is returned are secret, so the memory
an implementation reads does not depend on them, and it reads both the
encoded message `EM` and the alternative message `AM` whichever it returns
(draft-irtf-cfrg-rsa-guidance-10 §7.2 step 5). The return value depends on
secrets (whether the padding string has a zero octet; whether the
ciphertext is below `n`, the key is consistent and RSADP passes its check).

`scratch` is working space of at least `16 n_len` `u64`s, whose contents on
return are unspecified. `stack` is the number of bytes below the stack
pointer that an implementation's calls and frames use. The functions may
overwrite their arguments passed in memory, where the calling convention
allows it (`writeArgs`).
-/

@[expose] public section

namespace VG.Spec.RsaPkcs1Enc

open Rsa (bytesAt wordsAt lenValid scratchWords written scratchSafety exponentDoc Outcome)

/-! ## `vg_rsa_pkcs1_encrypt` -/

/-- `vg_rsa_pkcs1_encrypt(out: *mut u8, out_len: usize, n: *const u8,
n_len: usize, e: *const u8, e_len: usize, msg: *const u8, msg_len: usize,
ps: *const u8, ps_len: usize, scratch: *mut u64, scratch_len: usize) -> u32`. -/
def encryptSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("msg", .slice false .u8 "msg_len"),
    ("ps", .slice false .u8 "ps_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- RSAES-PKCS1-V1_5-ENCRYPT of the message with the public key `(n, e)` and
the padding string `ps` (`encrypt`), for a message of at most `n_len - 11`
octets and a padding string of `n_len - msg_len - 3`. Constant time but for
the public key. -/
def encryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptSig.contract A
    (pre := fun _out outLen _n nLen _e eLen _msg msgLen _ps psLen _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ 1 ≤ eLen.toNat ∧
        eLen.toNat ≤ nLen.toNat ∧ msgLen.toNat + 11 ≤ nLen.toNat ∧
        psLen.toNat = nLen.toNat - msgLen.toNat - 3 ∧ scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun out _outLen n nLen e eLen msg msgLen ps psLen _scratch _scratchLen m m' r =>
      written m' out nLen.toNat r
        (encrypt (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m msg msgLen.toNat)
          (bytesAt m ps psLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _msg _msgLen _ps _psLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat))

def encryptApi : Api where
  module := "rsa_pkcs1_enc"
  name := "vg_rsa_pkcs1_encrypt"
  sig := encryptSig
  writeArgs := true
  contracts := some fun A stack => encryptContract A stack
  summary := s!"RSAES-PKCS1-v1_5 encryption: RSAES-PKCS1-V1_5-ENCRYPT (RFC 8017 §7.2.1), with \
    the padding string given by the caller. With the modulus `n` (`n_len` bytes, most \
    significant first, odd, from 512 to 8192 bits, its first byte not zero) and \
    {exponentDoc}, encrypts the encoded message \
    `0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M`, for the message `M` (`msg_len` bytes) and the padding \
    string `PS` (`ps_len` bytes), with RSAEP, writes the ciphertext (`n_len` bytes, most \
    significant first) to `out` and returns 1; or writes zeros and returns 0 if `n` or `e` is \
    not such a number or `PS` has a zero byte. RFC 8017 requires `PS` to be pseudo-randomly \
    generated nonzero bytes, freshly for every encryption.\n\n\
    Contract: `VG.Spec.RsaPkcs1Enc.encryptContract`. Constant time but for the public key: \
    timing may depend on the pointers, the lengths and the contents of `n` and `e`, not on \
    the message or the padding string."
  safety := ["`n_len` must be in 64..=1024.", "`out_len` must be `n_len`.",
    "`e_len` must be in 1..=`n_len`.", "`msg_len + 11` must be at most `n_len`.",
    "`ps_len` must be `n_len - msg_len - 3`."] ++ scratchSafety

/-! ## `vg_rsa_pkcs1_decrypt` -/

/-- The postcondition of decryption, with the outcome `o`, for the `nLen`
octets at `out` and the word at `msgLen`: for a message `M`, return 1, `M`
at the end of `out` after zeros, and its length at `msgLen`; for an error,
return 0 (`invalid`) or 2 (`fault`), zeros and a length of 0. -/
def writtenMsg (m' : Mem) (out msgLen : Addr) (nLen : Nat) (r : BitVec 32) : Outcome → Prop
  | .ok M => r = 1 ∧ bytesAt m' out nLen = List.replicate (nLen - M.length) 0 ++ M ∧
      wordsAt m' msgLen 1 = [BitVec.ofNat 64 M.length]
  | .invalid => r = 0 ∧ bytesAt m' out nLen = List.replicate nLen 0 ∧ wordsAt m' msgLen 1 = [0]
  | .fault => r = 2 ∧ bytesAt m' out nLen = List.replicate nLen 0 ∧ wordsAt m' msgLen 1 = [0]

/-- `vg_rsa_pkcs1_decrypt(out: *mut u8, out_len: usize, msg_len: *mut [u64; 1],
n: *const u8, n_len: usize, e: *const u8, e_len: usize, d: *const u8,
d_len: usize, input: *const u8, input_len: usize, p: *const u8, p_len: usize,
q: *const u8, q_len: usize, dp: *const u8, dp_len: usize, dq: *const u8,
dq_len: usize, qinv: *const u8, qinv_len: usize, scratch: *mut u64,
scratch_len: usize) -> u32`. -/
def decryptSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("msg_len", .array true .u64 1),
    ("n", .slice false .u8 "n_len"), ("e", .slice false .u8 "e_len"),
    ("d", .slice false .u8 "d_len"), ("input", .slice false .u8 "input_len"),
    ("p", .slice false .u8 "p_len"), ("q", .slice false .u8 "q_len"),
    ("dp", .slice false .u8 "dp_len"), ("dq", .slice false .u8 "dq_len"),
    ("qinv", .slice false .u8 "qinv_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- RSAES-PKCS1-V1_5-DECRYPT with implicit rejection of the ciphertext
`input` with the private key `(n, e, d, p, q, dP, dQ, qInv)` (`decrypt`).
Constant time but for the public key: in particular, not the validity of
the padding, the message length, the alternative length or which message is
returned. -/
def decryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decryptSig.contract A
    (pre := fun _out outLen _msgLen _n nLen _e eLen _d dLen _input inputLen _p pLen _q qLen _dp
        dpLen _dq dqLen _qinv qinvLen _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ inputLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧ 1 ≤ dLen.toNat ∧ dLen.toNat ≤ nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun out _outLen msgLen n nLen e eLen d dLen input _inputLen p pLen q qLen dp _dpLen
        dq _dqLen qinv _qinvLen _scratch _scratchLen m m' r =>
      writtenMsg m' out msgLen nLen.toNat r
        (decrypt (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m d dLen.toNat)
          (bytesAt m p pLen.toNat) (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat)
          (bytesAt m dq qLen.toNat) (bytesAt m qinv pLen.toNat) (bytesAt m input nLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _msgLen n nLen e eLen _d _dLen _input _inputLen _p _pLen _q
        _qLen _dp _dpLen _dq _dqLen _qinv _qinvLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat))

def decryptApi : Api where
  module := "rsa_pkcs1_enc"
  name := "vg_rsa_pkcs1_decrypt"
  sig := decryptSig
  writeArgs := true
  contracts := some fun A stack => decryptContract A stack
  summary := s!"RSAES-PKCS1-v1_5 decryption with implicit rejection: RSAES-PKCS1-V1_5-DECRYPT \
    (RFC 8017 §7.2.2) as draft-irtf-cfrg-rsa-guidance-10 §7.2 implements it, with the \
    private key `(n, e, d, p, q, dP, dQ, qInv)`. With the modulus `n` (`n_len` bytes, most \
    significant first, odd, from 512 to 8192 bits, its first byte not zero) and \
    {exponentDoc}, computes the encoded message `EM` of the ciphertext `input` (`n_len` \
    bytes, most significant first) with RSADP as `vg_rsa_private_checked` does. If its \
    padding is valid (`0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M`, `PS` at least 8 nonzero bytes), the \
    message is `M`; otherwise it is a message derived from `d` and the ciphertext (the \
    draft's §7.1 PRF keyed with HMAC-SHA-256 of the ciphertext under the SHA-256 digest of \
    `d`), of at most `n_len - 11` bytes, which is the same every time the same key \
    decrypts the same ciphertext. Writes the message at the end of `out` (`n_len` bytes), \
    after zeros, and its length to `*msg_len`, and returns 1. Writes zeros to both and \
    returns 0 if `n` or `e` is not such a number, the ciphertext is not below `n`, \
    `p q ≠ n`, or `qInv ≥ p`; and returns 2 (an internal error) if RSADP's result fails its \
    check against `e`, which is the case for no ciphertext if `vg_rsa_check_key` accepts \
    the key and `p` and `q` are prime. An invalid padding is never an error. `d` is used \
    as given, never recomputed. `p`, `dp` and `qinv` are `p_len` bytes, `q` and `dq` are \
    `q_len` bytes, and `d` is `d_len` bytes, all most significant first.\n\n\
    Contract: `VG.Spec.RsaPkcs1Enc.decryptContract`. Constant time but for the public key: \
    timing may depend on the pointers, the lengths and the contents of `n` and `e`, not on \
    the ciphertext, the private key, the validity of the padding, the length of the \
    message or which message is returned."
  safety := ["`n_len` must be in 64..=1024.", "`out_len` and `input_len` must be `n_len`.",
    "`e_len` and `d_len` must be in 1..=`n_len`.", "`p_len` and `q_len` must be in 1..`n_len`.",
    "`dp_len` and `qinv_len` must be `p_len`, and `dq_len` must be `q_len`."] ++
    scratchSafety

end VG.Spec.RsaPkcs1Enc
