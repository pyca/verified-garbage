module

public import VerifiedGarbage.Impl.AesXts.X86_64Vaes

/-!
# XTS-AES on x86-64 in one pass, with AES-NI and PCLMULQDQ

`vg_aes_xts_encrypt_aesni_pclmul` and `vg_aes_xts_decrypt_aesni_pclmul`, with
the contracts of `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt`, for CPUs with
AES-NI and PCLMULQDQ but not VAES: their code is all legacy SSE, so they need
no AVX. They are `X86_64Vaes.crypt` with
another loop: the arguments, the first eight tweaks (`gen`), the blocks left
after the loop and the tweak copied back are those of the VAES functions
(`X86_64Vaes.lean`).

The loop takes eight blocks at a time, one in each of `xmm0`–`xmm7`, through
the AES-NI round code (`AesNi.aes`, or `AesNi.aesDec`, which keeps the round
key in `xmm8`): each block register is loaded from the data and XORed with its
tweak from `scratch + 256` (`tPre`, through `rax`), AES runs on all eight, and
each is XORed with its tweak again and stored (`tPost`). Then each tweak in
the buffer is multiplied by `α⁸` (`stepT`): `T ⊗ α⁸` is `T` shifted left by
eight bits (`pslldq` by one byte) XORed with the carry-less product of its
top byte (`psrldq` by fifteen bytes, of a copy in `xmm10`) and `0x87`
(`pclmulqdq` with `0x87` in `xmm11`). There are not registers enough for the tweaks, so they stay in the
buffer, read and written sixteen bytes at a time.

Every branch and every address depends only on the pointers, `rounds` and
`n`. No callee-saved register is written.
-/

@[expose] public section

namespace VG.Impl.AesXts.X86_64AesNi

open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ regs8)
open VG.Impl.AesXts.X86_64Vaes (crypt tPre tPost)

/-- `0x87` into the low quadword of `xmm11`. -/
def constK : List Instr := [.movImm64 .rax 0x87, .xop (.movq .xmm11 .rax)]

/-- The tweak at `rax + 16 k` times `α⁸`. -/
def stepT (k : Nat) : List Instr :=
  [.movdquLoad .xmm9 (at_ .rax (16 * k)), .xop (.bin .movdqa .xmm10 .xmm9), .xop (.shift .psrldq .xmm10 15),
   .xop (.pclmulqdq .xmm10 .xmm11 0), .xop (.shift .pslldq .xmm9 1),
   .xop (.bin .pxor .xmm9 .xmm10), .movdquStore (at_ .rax (16 * k)) .xmm9]

/-- All eight tweaks times `α⁸`. -/
def steps : List Instr := (List.range 8).flatMap stepT

/-- Eight blocks through `f`. -/
def group (f : List XReg → Prog isa) : Prog isa :=
  .seq (.block (tPre regs8 0))
    (.seq (f regs8)
      (.block (tPost regs8 0 ++ steps ++ ([.alu .add .r11 (.imm 128), .alu .sub .r9 (.imm 8),
        .alu .cmp .r9 (.imm 8)] : List Instr))))

/-- The eight-block loop, if eight blocks are left. -/
def loop8 (f : List XReg → Prog isa) : Prog isa :=
  .ite .b (.block [])
    (.seq (.block (constK ++ ([.mov .rax (.reg .r8), .alu .add .rax (.imm 256)] : List Instr)))
      (.loop (group f) .ae))

def encrypt : Prog isa := crypt (.block []) (loop8 Aes.X86_64.AesNi.aes) Aes.X86_64.AesNi.aes

def decrypt : Prog isa :=
  crypt Aes.X86_64.AesNi.imcKeys (loop8 Aes.X86_64.AesNi.aesDec) Aes.X86_64.AesNi.aesDec

end VG.Impl.AesXts.X86_64AesNi
