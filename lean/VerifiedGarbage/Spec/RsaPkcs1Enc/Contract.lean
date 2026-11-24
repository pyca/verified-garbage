module

public import VerifiedGarbage.Spec.RsaPkcs1Enc
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute

/-!
# RSAES-PKCS1-v1_5 with implicit rejection: the decryption contract, on every target

**Trusted** (as every file in `Spec/`). In the module `rsa_pkcs1_enc`,
`vg_rsa_pkcs1_decrypt_precomputed_front`: RSAES-PKCS1-V1_5-DECRYPT with
implicit rejection (`RsaPkcs1Enc.decrypt`), with RSADP checked against `e`
(`Rsa.privateChecked`), given the key's precomputed values
(`Rsa.privatePrecompute`, `Spec/Rsa/PrivatePrecompute.lean`). It writes the
message at the start of `out`, zeros after it, so that its caller can
shorten the buffer to the message without moving it (and leaving a copy of
it outside the message). Encryption, `vg_rsa_pkcs1_encrypt_random`, is in
`Spec/RsaPkcs1Enc/Random.lean`; the arguments it shares with decryption are
as here.

Every number is a slice of octets, most significant first, with a length of
its own, as in `Spec/Rsa/Contract.lean`: the modulus `n` is `n_len` octets,
from 64 to 1024, and so is the ciphertext; `e` is at most `n_len` octets.
These are preconditions, on the public lengths, and so are the lengths of
the message and the padding string; everything about the values is checked:
the function returns 1 and writes its result, or returns 0 (or 2, for the
internal error of `Rsa.privateChecked`) and writes zeros.

The signature determines memory validity, separation and that the pointers
and lengths are public, through `Sig.contract`. The public key, `n` and `e`,
is public too, and may affect timing (`leak`), and so are the modulus'
precomputed values (`Rsa.privatePrecomputedLeak`). The message and the
padding string are secret, and so is every part of a private key and the
ciphertext. Nothing else may affect timing: in decryption, whether the
padding is valid, the length of the message `L`, the alternative length
`AL` and which of the two messages is returned are secret, so the memory
an implementation reads does not depend on them, and it reads both the
encoded message `EM` and the alternative message `AM` whichever it returns
(draft-irtf-cfrg-rsa-guidance-10 §7.2 step 5). The return value depends on
secrets (whether the padding string has a zero octet; whether the
ciphertext is below `n`, the key is consistent and RSADP passes its check).

`scratch` is working space of at least `8 ⌈n_len / 8⌉ + 48` `u64`s
(`Rsa.publicScratchWords`, the public-key operation's) when encrypting and
`16 n_len + 32` when decrypting, whose contents on return are unspecified. `stack` is the number of bytes below the stack
pointer that an implementation's calls and frames use. The functions may
overwrite their arguments passed in memory, where the calling convention
allows it (`writeArgs`).
-/
@[expose] public section

namespace VG.Spec.RsaPkcs1Enc

open Rsa (bytesAt wordsAt lenValid scratchWords publicScratchWords written scratchSafety
  publicScratchSafety exponentDoc Outcome)

/-! ## `vg_rsa_pkcs1_decrypt_precomputed_front` -/

/-- The postcondition of decryption, with the outcome `o`, for the `nLen`
octets at `out` and the word at `msgLen`: for a message `M`, return 1, `M`
at the start of `out` and zeros after it, and its length at `msgLen`; for an
error, return 0 (`invalid`) or 2 (`fault`), zeros and a length of 0. -/
def writtenMsgFront (m' : Mem) (out msgLen : Addr) (nLen : Nat) (r : BitVec 32) :
    Outcome → Prop
  | .ok M => r = 1 ∧ bytesAt m' out nLen = M ++ List.replicate (nLen - M.length) 0 ∧
      wordsAt m' msgLen 1 = [BitVec.ofNat 64 M.length]
  | .invalid => r = 0 ∧ bytesAt m' out nLen = List.replicate nLen 0 ∧ wordsAt m' msgLen 1 = [0]
  | .fault => r = 2 ∧ bytesAt m' out nLen = List.replicate nLen 0 ∧ wordsAt m' msgLen 1 = [0]

/-- `vg_rsa_pkcs1_decrypt_precomputed_front(out: *mut u8, out_len: usize,
msg_len: *mut [u64; 1], n: *const u8, n_len: usize, e: *const u8,
e_len: usize, d: *const u8, d_len: usize, input: *const u8,
input_len: usize, p: *const u8, p_len: usize, q: *const u8, q_len: usize,
dp: *const u8, dp_len: usize, dq: *const u8, dq_len: usize,
qinv: *const u8, qinv_len: usize, scratch: *mut u64, scratch_len: usize,
pre: *const u64, pre_len: usize) -> u32`. -/
def decryptPrecomputedFrontSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("msg_len", .array true .u64 1),
    ("n", .slice false .u8 "n_len"), ("e", .slice false .u8 "e_len"),
    ("d", .slice false .u8 "d_len"), ("input", .slice false .u8 "input_len"),
    ("p", .slice false .u8 "p_len"), ("q", .slice false .u8 "q_len"),
    ("dp", .slice false .u8 "dp_len"), ("dq", .slice false .u8 "dq_len"),
    ("qinv", .slice false .u8 "qinv_len"), ("scratch", .slice true .u64 "scratch_len"),
    ("pre", .slice false .u64 "pre_len")]
  ret := some .u32

/-- RSAES-PKCS1-V1_5-DECRYPT with implicit rejection of the ciphertext
`input` with the private key `(n, e, d, p, q, dP, dQ, qInv)` (`decrypt`),
given `pre` holding the key's precomputed values (`Rsa.privatePrecompute`),
with the message at the start of `out` (`writtenMsgFront`). Constant time
but for the public key and the modulus' precomputed values: in particular,
not the validity of the padding, the message length, the alternative length
or which message is returned. -/
def decryptPrecomputedFrontContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decryptPrecomputedFrontSig.contract A
    (pre := fun _out outLen _msgLen n nLen _e eLen _d dLen _input inputLen p pLen q qLen _dp
        dpLen _dq dqLen _qinv qinvLen _scratch scratchLen pre preLen m =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ inputLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧ 1 ≤ dLen.toNat ∧ dLen.toNat ≤ nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Rsa.privatePrecomputedWords nLen.toNat pLen.toNat qLen.toNat ∧
        Rsa.privatePrecompute (bytesAt m n nLen.toNat) (bytesAt m p pLen.toNat)
          (bytesAt m q qLen.toNat) = some (Rsa.wordsAt m pre preLen.toNat))
    (post := fun out _outLen msgLen n nLen e eLen d dLen input _inputLen p pLen q qLen dp _dpLen
        dq _dqLen qinv _qinvLen _scratch _scratchLen _pre _preLen m m' r =>
      writtenMsgFront m' out msgLen nLen.toNat r
        (decrypt (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m d dLen.toNat)
          (bytesAt m p pLen.toNat) (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat)
          (bytesAt m dq qLen.toNat) (bytesAt m qinv pLen.toNat) (bytesAt m input nLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _msgLen n nLen e eLen _d _dLen _input _inputLen _p _pLen _q
        _qLen _dp _dpLen _dq _dqLen _qinv _qinvLen _scratch _scratchLen pre _preLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        Rsa.privatePrecomputedLeak m pre nLen.toNat)

def decryptPrecomputedFrontApi : Api where
  module := "rsa_pkcs1_enc"
  name := "vg_rsa_pkcs1_decrypt_precomputed_front"
  sig := decryptPrecomputedFrontSig
  writeArgs := true
  contracts := some fun A stack => decryptPrecomputedFrontContract A stack
  summary := "RSAES-PKCS1-V1_5-DECRYPT (RFC 8017 §7.2.2) with implicit rejection \
    (draft-irtf-cfrg-rsa-guidance), of the ciphertext `input` with the private key `(n, e, \
    d, p, q, dp, dq, qinv)`, RSADP checked against `e`: returns 1 and writes the message, or \
    for an invalid padding the alternative message, at the start of `out` and zeros after \
    it, so that the caller can shorten `out` to the message's length without moving it, and \
    its length to `*msg_len`; or writes zeros to `out` and `*msg_len` and returns 0 if the \
    ciphertext is not below `n` or the key is refused, or 2 if RSADP fails its check \
    against `e`. " ++
    Rsa.privatePrecomputedDoc ++ ".\n\n\
    Contract: `VG.Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract`. Constant time but for \
    the public key: timing may depend on the pointers, the lengths, the contents of `n` and \
    `e` and the first `2 * ⌈n_len / 8⌉` words of `pre` (the modulus' values), not on the \
    ciphertext, the private key, the rest of `pre`, the validity of the padding, the length \
    of the message or which message is returned."
  safety := ["`n_len` must be in 64..=1024.", "`out_len` and `input_len` must be `n_len`.",
    "`e_len` and `d_len` must be in 1..=`n_len`.", "`p_len` and `q_len` must be in 1..`n_len`.",
    "`dp_len` and `qinv_len` must be `p_len`, and `dq_len` must be `q_len`."] ++
    scratchSafety ++ Rsa.privatePrecomputedSafety

end VG.Spec.RsaPkcs1Enc
