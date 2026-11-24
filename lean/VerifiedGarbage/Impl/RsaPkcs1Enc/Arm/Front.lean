module

public import VerifiedGarbage.Impl.RsaOaep.Arm
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# RSAES-PKCS1-v1_5 decryption with the message first, on ARMv7

`vg_rsa_pkcs1_decrypt_precomputed` takes the arguments of
`vg_rsa_pkcs1_decrypt_precomputed_body` and calls it (`body`, by its name) with
them, in the frames of RSAES-OAEP's functions (`Impl/RsaOaep/Arm.lean`,
`Impl.RsaPkcs1Sig.Arm.wrap` with a frame of `frameBytes`, 128 bytes): the
four argument registers loaded back from the push, and the 21 stack
arguments copied to the bottom of the frame (`setup`), where the callee
finds them. `out`, `k` and `msg_len` stay in the push, and `scratch` above
it, which the callee does not write.

That function writes the message `M` at the end of `out`, after `k - L`
zeros (`L` its length, at `*msg_len`), or zeros and a length of 0. After
the call its result waits in RSAES-OAEP's slot `sRes`, `scratch` in `sS`
(`after`, the stack arguments being free again), and the first
`oBuf + 2048` bytes of `scratch`, whose contents on return are unspecified,
hold a buffer of 2048 bytes at `oBuf`: cleared (`clrBuf`), `out`'s `k`
bytes copied to it (`inSet`), shifted left by `s = k - *msg_len` bytes in
eleven passes (`shift`), pass `j` moving each of its first 1024 bytes `2^j`
bytes under the mask of bit `j` of `s` (RSAES-OAEP's `passOne`;
`s ≤ k ≤ 1024 < 2^11`), and its first `k` bytes copied back to `out`
(RSAES-OAEP's `outSet`): `M`, then zeros. `*msg_len` is left as the call
wrote it, and the result is the call's. No address or branch depends on
`s`, which is secret: only masks do.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.Arm.Front

open VG.Arm
open VG.Impl.RsaPkcs1Sig.Arm (wrap)
open VG.Impl.RsaPss.Arm (seqs mw sp0 st ld copyArg arg frameBytes sS sA sD sPc)
open VG.Impl.RsaOaep.Arm (sRes clrBuf passOne outSet)

/-- The callee's 21 stack arguments (our arguments 4 … 24) to the bottom of
the frame, then its four register arguments (ours) back from the push. -/
def setup : List Instr :=
  [sp0] ++ copyArg 4 0 ++ copyArg 5 1 ++ copyArg 6 2 ++ copyArg 7 3 ++ copyArg 8 4 ++ copyArg 9 5 ++
    copyArg 10 6 ++ copyArg 11 7 ++ copyArg 12 8 ++ copyArg 13 9 ++ copyArg 14 10 ++ copyArg 15 11 ++
    copyArg 16 12 ++ copyArg 17 13 ++ copyArg 18 14 ++ copyArg 19 15 ++ copyArg 20 16 ++ copyArg 21 17 ++
    copyArg 22 18 ++ copyArg 23 19 ++ copyArg 24 20 ++ [ld .r0 (arg 0), ld .r1 (arg 1), ld .r2 (arg 2), ld .r3 (arg 3)]

/-- The call's result to `sRes`, and `scratch` (argument 21) to `sS`. -/
def after : List Instr := [sp0, st .r0 sRes, ld .r0 (arg 21), st .r0 sS]

/-- `out`'s `k` bytes to the buffer, for `copyBytes`. -/
def inSet : List Instr := sp0 :: (VG.Impl.RsaPss.Arm.atS .r0 VG.Impl.RsaOaep.Arm.oBuf ++ [ld .r1 (arg 0), ld .lr (arg 4)])

/-- `msg_len` (argument 2) to `r1`. -/
def mlArg : List Instr := [sp0, ld .r1 (arg 2)]

/-- `*msg_len`'s low word to `r1`. -/
def mlLoad : List Instr := [.ldr .r1 .r1 0]

/-- The shift's distance `k - *msg_len` to `sA`, its first pass's to `sD`,
and its eleven passes to `sPc`. -/
def shInit : List Instr :=
  [sp0, ld .r0 (arg 4), .dp .sub .r0 .r0 (.reg .r1), st .r0 sA, mw .r0 1, st .r0 sD, mw .r0 11, st .r0 sPc]

/-- The buffer shifted left by `k - *msg_len` bytes, in eleven passes. -/
def shift : Prog isa := seqs [.block mlArg, .block mlLoad, .block shInit, .loop passOne .ne]

/-- The call's result back to `r0`. -/
def ret : List Instr := [sp0, ld .r0 sRes]

/-- After the call: the message moved to the start of `out`. -/
def tail : Prog isa :=
  seqs [.block clrBuf, Bignum.Arm.maskBytes, .block inSet, Bignum.Arm.copyBytes, shift, .block outSet,
    Bignum.Arm.copyBytes, .block ret]

/-- The inner frame's body, calling `vg_rsa_pkcs1_decrypt_precomputed_body`
(`callee`) by `name`. -/
def body (name : String) (callee : Prog isa) : Prog isa :=
  seqs [.block setup, .call name callee, .block after, tail]

/-- `vg_rsa_pkcs1_decrypt_precomputed`, calling `callee` by `name`. -/
def code (name : String) (callee : Prog isa) : Prog isa := wrap frameBytes (body name callee)

end VG.Impl.RsaPkcs1Enc.Arm.Front

namespace VG.Impl.RsaPkcs1Enc.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `Spec.RsaPkcs1Enc.decryptPrecomputedApi`'s function as emitted,
calling `vg_rsa_pkcs1_decrypt_precomputed_body`'s code `callee` by `name`, then
its cleanup: the 3824 bytes of stack its push (56), its frame (128) and the
callee (3640) use zeroed. -/
def decryptPrecomputed (name : String) (callee : Prog isa) : Prog isa :=
  scrubAll 32 3824 (Front.code name callee)

end VG.Impl.RsaPkcs1Enc.Arm.Fn
