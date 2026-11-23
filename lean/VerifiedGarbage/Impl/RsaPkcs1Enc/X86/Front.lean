module

public import VerifiedGarbage.Impl.RsaOaep.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-!
# RSAES-PKCS1-v1_5 decryption with the message first, on x86 (32-bit)

`vg_rsa_pkcs1_decrypt_precomputed` takes the arguments of
`vg_rsa_pkcs1_decrypt_precomputed_body`, all 25 on the stack, and calls it
(`body`, by its name) with them, copied to the first 100 bytes of a frame of
`frameBytes` (144) bytes, RSASSA-PSS's and RSAES-OAEP's
(`Impl/RsaPss/X86.lean`), inside the push of the callee-saved registers
(`wrap`, `Impl/RsaPkcs1Sig/X86/Wrap.lean`): `setup`.

That function writes the message `M` at the end of `out`, after `k - L`
zeros (`L` its length, at `*msg_len`), or zeros and a length of 0. After
the call its result waits in the slot `sRet`, `scratch` (our argument 21) is
in `ebp` (`after`), and the first `oBuf + 2048` bytes of `scratch`, whose
contents on return are unspecified, hold a buffer of 2048 bytes at `oBuf`:
cleared (`clearBuf`), `out`'s `k` bytes copied to it (`copyIn`), shifted
left by `s = k - *msg_len` bytes in eleven passes (`shift`), pass `j`
moving each of its first 1024 bytes `2^j` bytes under the mask of bit `j`
of `s` (RSAES-OAEP's `passOne`, with the slots `sA`, `sD` and `sPc`;
`s ≤ k ≤ 1024 < 2^11`), and its first `k` bytes copied back to `out`
(`copyOut`): `M`, then zeros. `*msg_len` is left as the call wrote it, and
the result is the call's. No address or branch depends on `s`, which is
secret: only masks do. Every argument we read after the call is our own,
above the frame, which the call does not change.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.X86.Front

open VG VG.X86
open VG.Impl.RsaPkcs1Sig.X86 (wrap at_)
open VG.Impl.RsaPss.X86 (seqs ld st mi atS zeroLoop clrArgs copyArg arg frameBytes sA sD sPc)
open VG.Impl.RsaOaep.X86 (oBuf passOne)

/-- The call's result, after it. -/
def sRet : Nat := 100

/-- Our 25 arguments to the frame's first 25 words, the call's. -/
def setup : List Instr := (List.range 25).flatMap fun j => copyArg j j

/-- The call's result to `sRet`, and `scratch` into `ebp`. -/
def after : List Instr := [st .eax sRet, ld .ebp (arg 21)]

/-- The buffer's 2048 bytes cleared. -/
def clearBuf : Prog isa := .seq (.block (clrArgs oBuf 2048)) zeroLoop

/-- `out` (`esi`), the buffer (`ebx`) and `k` (`ecx`), for `copyBytes`. -/
def inSet : List Instr := [ld .esi (arg 0)] ++ atS .ebx oBuf ++ [ld .ecx (arg 4)]

/-- `out`'s `k` bytes to the buffer. -/
def copyIn : Prog isa := .seq (.block inSet) Impl.Bignum.X86.copyBytes

/-- The distance `s = k - *msg_len` (the low word of `*msg_len`) to `sA`,
the first pass's `1` to `sD`, and the passes, eleven, to `sPc`. -/
def shInit : List Instr :=
  [ld .eax (arg 4), ld .edx (arg 2), .mov .edx (.mem (at_ .edx 0)), .alu .sub .eax (.reg .edx), st .eax sA,
    mi .eax 1, st .eax sD, mi .eax 11, st .eax sPc]

/-- The buffer shifted left by `k - *msg_len` bytes, in eleven passes. -/
def shift : Prog isa := .seq (.block shInit) (.loop passOne .ne)

/-- The buffer (`esi`), `out` (`ebx`) and `k` (`ecx`), for `copyBytes`. -/
def outSet : List Instr := atS .esi oBuf ++ [ld .ebx (arg 0), ld .ecx (arg 4)]

/-- The buffer's first `k` bytes to `out`. -/
def copyOut : Prog isa := .seq (.block outSet) Impl.Bignum.X86.copyBytes

/-- The call's result back to `eax`. -/
def ret : List Instr := [ld .eax sRet]

/-- After the call: the message moved to the start of `out`. -/
def tail : Prog isa := seqs [.block after, clearBuf, copyIn, shift, copyOut, .block ret]

/-- The frame's body, calling `vg_rsa_pkcs1_decrypt_precomputed_body`
(`callee`) by `name`. -/
def body (name : String) (callee : Prog isa) : Prog isa := seqs [.block setup, .call name callee, tail]

/-- `vg_rsa_pkcs1_decrypt_precomputed`, calling `callee` by `name`. -/
def code (name : String) (callee : Prog isa) : Prog isa := wrap frameBytes (body name callee)

end VG.Impl.RsaPkcs1Enc.X86.Front

namespace VG.Impl.RsaPkcs1Enc.X86.Fn

open VG.X86

/-- `Spec.RsaPkcs1Enc.decryptPrecomputedApi`'s function as emitted,
calling `vg_rsa_pkcs1_decrypt_precomputed_body`'s code `callee` by `name`, then
its cleanup: the 3732 bytes of stack its push (16), its frame (144), its
call (4) and the callee (3568) use zeroed. -/
def decryptPrecomputed (name : String) (callee : Prog isa) : Prog isa :=
  Impl.Scrub.X86.scrubAll 32 3732 (Front.code name callee)

end VG.Impl.RsaPkcs1Enc.X86.Fn
