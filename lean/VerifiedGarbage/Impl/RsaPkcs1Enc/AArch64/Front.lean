module

public import VerifiedGarbage.Impl.RsaOaep.AArch64
public import VerifiedGarbage.Impl.Scrub.AArch64.Writes

/-!
# RSAES-PKCS1-v1_5 decryption with the message first, on AArch64

`vg_rsa_pkcs1_decrypt_precomputed` takes the arguments of
`vg_rsa_pkcs1_decrypt_precomputed_body` and calls it (`body`, by its name) with
them: the argument registers `x0`–`x7` as they came, and its 17 stack
arguments copied to the bottom of a frame of `frameBytes` (272) bytes,
RSAES-OAEP's (`Impl/RsaOaep/AArch64.lean`), inside one saving `x30`. `out`,
`n_len` (`k`) and `msg_len` wait for the call in the frame's slots `sOut`,
`sK` and `sMl`, above the copies (`setup`).

That function writes the message `M` at the end of `out`, after `k - L`
zeros (`L` its length, at `*msg_len`), or zeros and a length of 0. After
the call its result waits in `sR`, and `scratch` (our stack argument 13) in
`sScr` (`after`), RSAES-OAEP's slot for it, over the copies, which are done
with. The first `oBuf + 2048` bytes of `scratch`, whose contents on return
are unspecified, hold a buffer of 2048 bytes at `oBuf`: cleared
(`clearBuf`, RSAES-OAEP's), `out`'s `k` bytes copied to it (`copyIn`),
shifted left by `s = k - *msg_len` bytes in eleven passes (`shift`), pass
`j` moving each of its first 1024 bytes `2^j` bytes under the mask of bit
`j` of `s` (RSAES-OAEP's `pass`; `s ≤ k ≤ 1024 < 2^11`), and its first `k`
bytes copied back to `out` (`copyOut`): `M`, then zeros. `*msg_len` is left
as the call wrote it, and the result is the call's. No address or branch
depends on `s`, which is secret: only masks do.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.AArch64.Front

open VG.AArch64
open VG.Impl.RsaOaep.AArch64 (frameBytes sOut sK sMl sR sScr oBuf scr mvArg copyLoop clearBuf pass)
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs)

/-- `out`, `k` and `msg_len` to their slots, `x9 = sp`, and our 17 stack
arguments to the frame's first 17 words, the callee's stack arguments. -/
def setup : List Instr :=
  [.addSp .x9 0, .str .x .x0 .x9 sOut, .str .x .x4 .x9 sK, .str .x .x2 .x9 sMl] ++
    (List.range 17).flatMap fun j => mvArg j (8 * j)

/-- The call's result to `sR`, and `scratch` (our stack argument 13) to
`sScr`. -/
def after : List Instr := [.addSp .x9 0, .str .x .x0 .x9 sR] ++ mvArg 13 sScr

/-- `out`'s `k` bytes (at `x11`, `x13` of them) to the buffer (at `x12`). -/
def copyIn : Prog isa := .seq (.block ([.ldrSp .x11 sOut] ++ scr .x12 oBuf ++ [.ldrSp .x13 sK])) copyLoop

/-- The buffer (at `x17`) shifted left by `k - *msg_len` bytes (`x9`), in
eleven passes. -/
def shift : Prog isa :=
  .seq (.block (scr .x17 oBuf ++ [.ldrSp .x9 sK, .ldrSp .x10 sMl, .ldr .x .x10 .x10 0, .sub .x .x9 .x9 .x10,
      .movz .x .x14 1 0, .movz .x .x8 11 0]))
    (.loop pass (.nonzero .x .x8))

/-- The buffer's first `k` bytes (at `x11`, `x13` of them) to `out` (at
`x12`). -/
def copyOut : Prog isa := .seq (.block (scr .x11 oBuf ++ [.ldrSp .x12 sOut, .ldrSp .x13 sK])) copyLoop

/-- The call's result back to `x0`. -/
def ret : List Instr := [.ldrSp .x0 sR]

/-- After the call: the message moved to the start of `out`. -/
def tail : Prog isa := seqs [clearBuf, copyIn, shift, copyOut, .block ret]

/-- The inner frame's body, calling `vg_rsa_pkcs1_decrypt_precomputed_body`
(`callee`) by `name`. -/
def body (name : String) (callee : Prog isa) : Prog isa :=
  seqs [.block setup, .call name callee, .block after, tail]

/-- `vg_rsa_pkcs1_decrypt_precomputed`, calling `callee` by `name`. -/
def code (name : String) (callee : Prog isa) : Prog isa :=
  .frame (.push .x30) (.frame (.alloc frameBytes) (body name callee) (.free frameBytes)) (.pop .x30)

end VG.Impl.RsaPkcs1Enc.AArch64.Front

namespace VG.Impl.RsaPkcs1Enc.AArch64.Fn

open VG.AArch64
open VG.Impl.Scrub.AArch64 (scrubOf)

/-- `Spec.RsaPkcs1Enc.decryptPrecomputedApi`'s function as emitted,
calling `vg_rsa_pkcs1_decrypt_precomputed_body`'s code `callee` by `name`, then
its cleanup: the registers the code may write cleared, and the 3776 bytes of
stack its frames (288) and the callee (3488) use zeroed. -/
def decryptPrecomputed (name : String) (callee : Prog isa) : Prog isa :=
  scrubOf 3776 32 (Front.code name callee)

end VG.Impl.RsaPkcs1Enc.AArch64.Fn
