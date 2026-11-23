module

public import VerifiedGarbage.Impl.RsaOaep.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Decrypt

/-!
# RSAES-PKCS1-v1_5 decryption with the message first, on PPC64LE

`vg_rsa_pkcs1_decrypt_precomputed_front` takes the arguments of
`vg_rsa_pkcs1_decrypt_precomputed` and calls it (`callee`, by `name`) with
them: the eight argument registers as they came, and its 17 stack arguments
copied to the frame's Parameter Save Area (`r1 + 96`, as
`withStackScratchArgs` does, `Impl/StackScratch/PPC64LE/Args.lean`), in a
frame of `frameBytes` (272) bytes. Before the call, `setup` saves our
caller's `r14`–`r17` and our return address in the frame's slots, above the
copies, and keeps `out` in `r14`, `out_len` (`k`) in `r15`, `msg_len` in
`r16` and `scratch` (our stack argument 13) in `r17`, which the callee
preserves.

That function writes the message `M` at the end of `out`, after `k - L`
zeros (`L` its length, at `*msg_len`), or zeros and a length of 0. After
the call (`after`, which restores the link register), the result waits in
`r3`, which nothing after it writes, and the first 2048 bytes of `scratch`,
whose contents on return are unspecified, are a buffer: cleared
(`clearBuf`), `out`'s `k` bytes copied to it (`copyIn`), shifted left by
`s = k - *msg_len` bytes in eleven passes (`shift`), pass `j` moving each of
its first 1024 bytes `2^j` bytes under the mask of bit `j` of `s`
(`shiftPass`, as RSAES-OAEP decryption's, `Impl/RsaOaep/PPC64LE/Decrypt.lean`;
`s ≤ k ≤ 1024 < 2^11`), and its first `k` bytes copied back to `out`
(`copyOut`): `M`, then zeros. `*msg_len` is left as the call wrote it, and
the result is the call's. No address or branch depends on `s`, which is
secret: only masks do. `restore` restores our caller's `r14`–`r17`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.PPC64LE.Front

open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)
open VG.Impl.RsaOaep.PPC64LE (zeroLoop copyLoop)
open VG.Impl.StackScratch.PPC64LE (copyArg)

/-- The size of the frame: its header, the Parameter Save Area with the
callee's 17 stack arguments (to `r1 + 232`), and the slots. -/
def frameBytes : Nat := 272

/-! The slots: our caller's `r14`–`r17`, and our return address. -/
def o14 : Nat := 232
def o15 : Nat := 240
def o16 : Nat := 248
def o17 : Nat := 256
def oLr : Nat := 264

/-- The stack arguments to the frame's Parameter Save Area, `r14`–`r17` and
the return address to their slots, and `out`, `k`, `msg_len` and `scratch`
(our stack argument 13) into `r14`–`r17`. -/
def setup : List Instr :=
  [.addSp .r12 0] ++ (List.range 17).flatMap (copyArg frameBytes) ++
    [.store .d .r14 .r12 o14, .store .d .r15 .r12 o15, .store .d .r16 .r12 o16, .store .d .r17 .r12 o17,
      .mflr .r0, .store .d .r0 .r12 oLr, mov .r14 .r3, mov .r15 .r4, mov .r16 .r5,
      .load .d .r17 .r12 (frameBytes + 96 + 8 * 13)]

/-- The return address back from its slot. -/
def after : List Instr := [.addSp .r12 0, .load .d .r0 .r12 oLr, .mtlr .r0]

/-- The buffer's 2048 bytes cleared. -/
def clearBuf : Prog isa := .seq (.block [mov .r4 .r17, .li .r5 2048, .li .r6 0]) zeroLoop

/-- `out`'s `k` bytes to the buffer. -/
def copyIn : Prog isa := .seq (.block [mov .r4 .r14, mov .r5 .r17, mov .r6 .r15]) copyLoop

/-- A pass: each of the buffer's first 1024 bytes replaced by the one `d`
(`r9`) bytes after it if bit 0 of `a` (`r8`) is set. -/
def shiftPass : Prog isa :=
  .seq (.block [mov .r4 .r17, .add .r5 .r4 .r9, .li .r6 1, .logic .and .r6 .r8 .r6, .li .r7 0,
      .sub .r6 .r7 .r6, .li .r7 1024])
    (.loop (.block [.lbz .r11 .r4 0, .lbz .r12 .r5 0, .logic .xor .r12 .r12 .r11, .logic .and .r12 .r12 .r6,
      .logic .xor .r11 .r11 .r12, .stb .r11 .r4 0, .addi .r4 .r4 1, .addi .r5 .r5 1, .subi .r7 .r7 1])
      (.nonzero .d .r7))

/-- The next pass: the next bit of `a`, twice the distance. -/
def nextPass : List Instr := [.lsr .d .r8 .r8 1, .add .r9 .r9 .r9, .subi .r10 .r10 1]

/-- The buffer shifted left by `k - *msg_len` bytes, in eleven passes. -/
def shift : Prog isa :=
  .seq (.block [.load .d .r8 .r16 0, .sub .r8 .r15 .r8, .li .r9 1, .li .r10 11])
    (.loop (.seq shiftPass (.block nextPass)) (.nonzero .d .r10))

/-- The buffer's first `k` bytes to `out`. -/
def copyOut : Prog isa := .seq (.block [mov .r4 .r17, mov .r5 .r14, mov .r6 .r15]) copyLoop

/-- Our caller's `r14`–`r17` back from their slots. -/
def restore : List Instr :=
  [.addSp .r12 0, .load .d .r14 .r12 o14, .load .d .r15 .r12 o15, .load .d .r16 .r12 o16,
    .load .d .r17 .r12 o17]

/-- After the call: the message moved to the start of `out`. -/
def tail : Prog isa := .seq clearBuf (.seq copyIn (.seq shift copyOut))

/-- The function's body, calling `vg_rsa_pkcs1_decrypt_precomputed`
(`callee`) by `name`. -/
def body (name : String) (callee : Prog isa) : Prog isa :=
  .seq (.block setup) (.seq (.call name callee) (.seq (.block after) (.seq tail (.block restore))))

/-- `vg_rsa_pkcs1_decrypt_precomputed_front`, calling `callee` by `name`. -/
def code (name : String) (callee : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (body name callee) (.free frameBytes)

/-- The name of `vg_rsa_pkcs1_decrypt_precomputed`'s code before its
cleanup, an internal function. -/
def bodyName : String := "vg_rsa_pkcs1_decrypt_precomputed_body"

end VG.Impl.RsaPkcs1Enc.PPC64LE.Front

namespace VG.Impl.RsaPkcs1Enc.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `Spec.RsaPkcs1Enc.decryptPrecomputedFrontApi`'s function as emitted,
calling `vg_rsa_pkcs1_decrypt_precomputed`'s code before its cleanup
(`Decrypt.codeP`) as the internal function `Front.bodyName`, then its
cleanup: the 3920 bytes of stack its frame (272) and the callee (3648) use
zeroed, and every volatile register cleared, as for
`vg_rsa_pkcs1_decrypt_precomputed` (`Fn.decryptPrecomputed`). -/
def decryptPrecomputedFront : Prog isa :=
  scrubAll 32 3920 Impl.Scrub.PPC64LE.Clear.all (Front.code Front.bodyName Impl.RsaPkcs1Enc.PPC64LE.Decrypt.codeP)

end VG.Impl.RsaPkcs1Enc.PPC64LE.Fn
