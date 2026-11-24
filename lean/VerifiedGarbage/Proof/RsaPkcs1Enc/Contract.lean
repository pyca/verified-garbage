module

public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract

/-!
# RSAES-PKCS1-v1_5: the contracts of its internal functions

Not trusted: the contracts of functions that only verified code calls, and
that the proofs of their callers compose. Only the callers' contracts, in
`Spec/RsaPkcs1Enc/Contract.lean` and `Spec/RsaPkcs1Enc/Random.lean`, are
trusted.

`vg_rsa_pkcs1_decrypt_precomputed_body` (`decryptPrecomputedBodyContract`):
the code that `vg_rsa_pkcs1_decrypt_precomputed`
(`Spec.RsaPkcs1Enc.decryptPrecomputedBodyContract`) calls, before its cleanup.
It computes the same decryption, with the same arguments, but writes the
message at the end of `out`, after zeros (`writtenMsgEnd`), which the caller
moves to the start. Its proofs go through that of `vg_rsa_pkcs1_decrypt`
(`decryptContract`), the same without the precomputed values, which some
targets' proofs state on the way. The arguments are as in
`Spec/RsaPkcs1Enc/Contract.lean`.

`vg_rsa_pkcs1_encrypt_precomputed` (`encryptPrecomputedContract`), which
`vg_rsa_pkcs1_encrypt_random` (`Spec.RsaPkcs1Enc.encryptRandomContract`)
calls: RSAES-PKCS1-V1_5-ENCRYPT
(`Spec.RsaPkcs1Enc.encrypt`) with the padding string given by the caller,
and the modulus also given by the values `vg_rsa_public_precompute` computed
(`Rsa.publicPrecompute`), so that it can call
`vg_rsa_public_precomputed_checked`. The ciphertext and result are
encryption's when `pre` holds the values for `n`; otherwise they are
unspecified, but memory safety and the timing guarantee still hold. The
arguments are as in `Spec/RsaPkcs1Enc/Contract.lean`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc

open VG.Spec.RsaPkcs1Enc
open VG.Spec.Rsa (bytesAt wordsAt lenValid scratchWords publicScratchWords written Outcome)

/-! ## `vg_rsa_pkcs1_decrypt` -/

/-- The postcondition of decryption, with the outcome `o`, for the `nLen`
octets at `out` and the word at `msgLen`: for a message `M`, return 1, `M`
at the end of `out` after zeros, and its length at `msgLen`; for an error,
return 0 (`invalid`) or 2 (`fault`), zeros and a length of 0. -/
def writtenMsgEnd (m' : Mem) (out msgLen : Addr) (nLen : Nat) (r : BitVec 32) : Outcome → Prop
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
      writtenMsgEnd m' out msgLen nLen.toNat r
        (decrypt (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m d dLen.toNat)
          (bytesAt m p pLen.toNat) (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat)
          (bytesAt m dq qLen.toNat) (bytesAt m qinv pLen.toNat) (bytesAt m input nLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _msgLen n nLen e eLen _d _dLen _input _inputLen _p _pLen _q
        _qLen _dp _dpLen _dq _dqLen _qinv _qinvLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat))

/-! ## `vg_rsa_pkcs1_decrypt_precomputed_body` -/

/-- The parameters of `vg_rsa_pkcs1_decrypt`, then the key's precomputed
values `pre: *const u64, pre_len: usize`. -/
def decryptPrecomputedBodySig : Sig where
  params := decryptSig.params ++ [("pre", .slice false .u64 "pre_len")]
  ret := some .u32

/-- `decryptContract`, given the key's precomputed values `pre`
(`Spec.Rsa.privatePrecompute`): what `vg_rsa_pkcs1_decrypt` computes, given `pre`
holding them. -/
def decryptPrecomputedBodyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decryptPrecomputedBodySig.contract A
    (pre := fun _out outLen _msgLen n nLen _e eLen _d dLen _input inputLen p pLen q qLen _dp
        dpLen _dq dqLen _qinv qinvLen _scratch scratchLen pre preLen m =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ inputLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧ 1 ≤ dLen.toNat ∧ dLen.toNat ≤ nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Spec.Rsa.privatePrecomputedWords nLen.toNat pLen.toNat qLen.toNat ∧
        Spec.Rsa.privatePrecompute (bytesAt m n nLen.toNat) (bytesAt m p pLen.toNat)
          (bytesAt m q qLen.toNat) = some (Spec.Rsa.wordsAt m pre preLen.toNat))
    (post := fun out _outLen msgLen n nLen e eLen d dLen input _inputLen p pLen q qLen dp _dpLen
        dq _dqLen qinv _qinvLen _scratch _scratchLen _pre _preLen m m' r =>
      writtenMsgEnd m' out msgLen nLen.toNat r
        (decrypt (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m d dLen.toNat)
          (bytesAt m p pLen.toNat) (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat)
          (bytesAt m dq qLen.toNat) (bytesAt m qinv pLen.toNat) (bytesAt m input nLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _msgLen n nLen e eLen _d _dLen _input _inputLen _p _pLen _q
        _qLen _dp _dpLen _dq _dqLen _qinv _qinvLen _scratch _scratchLen pre _preLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        Spec.Rsa.privatePrecomputedLeak m pre nLen.toNat)

/-! ## `vg_rsa_pkcs1_encrypt_precomputed` -/

/-- `vg_rsa_pkcs1_encrypt_precomputed(out: *mut u8, out_len: usize,
n: *const u8, n_len: usize, e: *const u8, e_len: usize, msg: *const u8,
msg_len: usize, ps: *const u8, ps_len: usize, scratch: *mut u64,
scratch_len: usize, pre: *const u64, pre_len: usize) -> u32`. -/
def encryptPrecomputedSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("msg", .slice false .u8 "msg_len"),
    ("ps", .slice false .u8 "ps_len"), ("scratch", .slice true .u64 "scratch_len"),
    ("pre", .slice false .u64 "pre_len")]
  ret := some .u32

/-- RSAES-PKCS1-V1_5-ENCRYPT of the message with the public key `(n, e)` and
the padding string `ps` (`encrypt`), for a message of at most `n_len - 11`
octets and a padding string of `n_len - msg_len - 3`, if `pre` holds the
precomputed values of `n`. Constant time but for the public key and its
precomputed values. -/
def encryptPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptPrecomputedSig.contract A
    (pre := fun _out outLen _n nLen _e eLen _msg msgLen _ps psLen _scratch scratchLen _pre preLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ 1 ≤ eLen.toNat ∧
        eLen.toNat ≤ nLen.toNat ∧ msgLen.toNat + 11 ≤ nLen.toNat ∧
        psLen.toNat = nLen.toNat - msgLen.toNat - 3 ∧ publicScratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Spec.Rsa.precomputedWords nLen.toNat)
    (post := fun out _outLen n nLen e eLen msg msgLen ps psLen _scratch _scratchLen pre preLen m m' r =>
      Spec.Rsa.publicPrecompute (bytesAt m n nLen.toNat) = some (Spec.Rsa.wordsAt m pre preLen.toNat) →
        written m' out nLen.toNat r
          (encrypt (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m msg msgLen.toNat)
            (bytesAt m ps psLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _msg _msgLen _ps _psLen _scratch _scratchLen pre preLen
        m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        (Spec.Rsa.wordsAt m pre preLen.toNat).map (·.toNat))

end VG.Proof.RsaPkcs1Enc
