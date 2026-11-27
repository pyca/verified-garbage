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
hold a buffer at `oBuf` of `2k` bytes (`k ≤ 1024`): its bytes `k … 2k - 1`
cleared (`clrHi`), `out`'s `k` bytes copied to its first `k` (`inSet`),
shifted left by `s = k - *msg_len` bytes in `bitLength(k)` passes (`shift`),
pass `j` moving each of its first `k` bytes `2^j` bytes under the mask of
bit `j` of `s` (`passOne`, RSAES-OAEP's pass over `k` bytes; `s ≤ k <
2^bitLength(k)`, and pass `j` reads below `k + 2^j ≤ 2k`), and its first `k`
bytes copied back to `out` (RSAES-OAEP's `outSet`): `M`, then zeros. The
passes are counted by `k >> j` in `sPc`, the last being the one after which
it is 0. `*msg_len` is left as the call wrote it, and the result is the
call's. No address, loop count or branch depends on `s`, which is secret,
only on `k`: only masks depend on `s`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.Arm.Front

open VG.Arm
open VG.Impl.RsaPkcs1Sig.Arm (wrap)
open VG.Impl.RsaPss.Arm (seqs mw sp0 st ld atS copyArg arg frameBytes sS sA sD sPc countLoop passBody)
open VG.Impl.RsaOaep.Arm (sRes oBuf outSet)

/-- The callee's 21 stack arguments (our arguments 4 … 24) to the bottom of
the frame, then its four register arguments (ours) back from the push. -/
def setup : List Instr :=
  [sp0] ++ copyArg 4 0 ++ copyArg 5 1 ++ copyArg 6 2 ++ copyArg 7 3 ++ copyArg 8 4 ++ copyArg 9 5 ++
    copyArg 10 6 ++ copyArg 11 7 ++ copyArg 12 8 ++ copyArg 13 9 ++ copyArg 14 10 ++ copyArg 15 11 ++
    copyArg 16 12 ++ copyArg 17 13 ++ copyArg 18 14 ++ copyArg 19 15 ++ copyArg 20 16 ++ copyArg 21 17 ++
    copyArg 22 18 ++ copyArg 23 19 ++ copyArg 24 20 ++ [ld .r0 (arg 0), ld .r1 (arg 1), ld .r2 (arg 2), ld .r3 (arg 3)]

/-- The call's result to `sRes`, and `scratch` (argument 21) to `sS`. -/
def after : List Instr := [sp0, st .r0 sRes, ld .r0 (arg 21), st .r0 sS]

/-- The buffer's bytes `k … 2k - 1` (`r0`, `lr = k`) cleared, with the mask
0 (`r2`), for `maskBytes`. -/
def clrHi : List Instr := sp0 :: (atS .r0 oBuf ++ [ld .lr (arg 4), .dp .add .r0 .r0 (.reg .lr), mw .r2 0])

/-- `out`'s `k` bytes to the buffer, for `copyBytes`. -/
def inSet : List Instr := sp0 :: (atS .r0 oBuf ++ [ld .r1 (arg 0), ld .lr (arg 4)])

/-- `msg_len` (argument 2) to `r1`. -/
def mlArg : List Instr := [sp0, ld .r1 (arg 2)]

/-- `*msg_len`'s low word to `r1`. -/
def mlLoad : List Instr := [.ldr .r1 .r1 0]

/-- `k` to `sPc`, which counts the passes, the shift's distance
`k - *msg_len` to `sA`, and its first pass's to `sD`. -/
def shInit : List Instr :=
  [sp0, ld .r0 (arg 4), st .r0 sPc, .dp .sub .r0 .r0 (.reg .r1), st .r0 sA, mw .r0 1, st .r0 sD]

/-- A pass's registers: the buffer (`r0`), the byte `d` after it (`r1`), its
first `k` bytes (`lr`) and the mask of bit 0 of the distance left (`r2`). -/
def passSet : List Instr :=
  sp0 :: (atS .r0 oBuf ++ [ld .r1 sD, .dp .add .r1 .r0 (.reg .r1), ld .r2 sA, .dp .and .r2 .r2 (.imm 1), mw .r3 0,
    .dp .sub .r2 .r3 (.reg .r2), ld .lr (arg 4)])

/-- The next pass, and the flags of whether it was the last: `k >> j` is 0
after pass `j - 1` exactly when `j = bitLength(k)`. -/
def passNext : List Instr :=
  [sp0, ld .r0 sA, .mov .r0 (.shifted .r0 .lsr 1), st .r0 sA, ld .r0 sD, .dp .add .r0 .r0 (.reg .r0), st .r0 sD,
    ld .r0 sPc, .mov .r0 (.shifted .r0 .lsr 1), st .r0 sPc, .cmp .r0 (.imm 0)]

/-- A pass over the buffer's first `k` bytes. -/
def passOne : Prog isa := seqs [.block passSet, countLoop passBody, .block passNext]

/-- The buffer shifted left by `k - *msg_len` bytes, in `bitLength(k)` passes. -/
def shift : Prog isa := seqs [.block mlArg, .block mlLoad, .block shInit, .loop passOne .ne]

/-- The call's result back to `r0`. -/
def ret : List Instr := [sp0, ld .r0 sRes]

/-- After the call: the message moved to the start of `out`. -/
def tail : Prog isa :=
  seqs [.block clrHi, Bignum.Arm.maskBytes, .block inSet, Bignum.Arm.copyBytes, shift, .block outSet,
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
