module

public import VerifiedGarbage.Impl.CmacAes.X86_64.AesNi

/-!
# AES-CBC encryption with AES-NI on x86-64

`vg_aes_cbc_encrypt_aesni(schedule = rdi, rounds = rsi, iv = rdx, data = rcx, n = r8,
scratch = r9)`: `Cᵢ = CIPH_K(Cᵢ₋₁ ⊕ Pᵢ)`, one block after the other.

The chaining value stays in `xmm0`, loaded once and stored once. Each round
key is loaded from the schedule into `xmm1` when its round uses it, so the
code writes three vector registers: `xmm2` holds `K₀` while `Pᵢ ⊕ K₀` is
formed in `xmm1`, off the chain of dependent instructions, which is one
`pxor` and the `Nr` rounds for each block. The number of rounds selects one
of three loops, once (a branch on the public `rounds`).

`scratch` is not used, nor the stack, and no callee-saved register is
written. Every branch and every address depends only on the pointers,
`rounds` and `n`.
-/

@[expose] public section

namespace VG.Impl.AesCbc.X86_64.Encrypt

open VG.X86_64
open VG.Impl.CmacAes.X86_64.AesNi (at_)

/-- Round `j` of the block in `xmm0`, with round key `j` loaded into `xmm1`. -/
def round (j : Nat) : List Instr :=
  [.movdquLoad .xmm1 (at_ .rdi (16 * j)), .xop (.bin .aesenc .xmm0 .xmm1)]

/-- Rounds 1 to `k` of the block in `xmm0`. -/
def rounds (k : Nat) : List Instr := (List.range k).flatMap fun j => round (j + 1)

/-- `xmm0 ⊕ Pᵢ ⊕ K₀`: the first `AddRoundKey` of `Cᵢ₋₁ ⊕ Pᵢ`. -/
def first : List Instr :=
  [.movdquLoad .xmm1 (at_ .rcx 0), .movdquLoad .xmm2 (at_ .rdi 0), .xop (.bin .pxor .xmm1 .xmm2),
   .xop (.bin .pxor .xmm0 .xmm1)]

/-- The last round, the ciphertext block stored, and on to the next block;
ZF is set when no blocks are left. -/
def final (nr : Nat) : List Instr :=
  [.movdquLoad .xmm1 (at_ .rdi (16 * nr)), .xop (.bin .aesenclast .xmm0 .xmm1),
   .movdquStore (at_ .rcx 0) .xmm0, .alu .add .rcx (.imm 16), .alu .sub .r8 (.imm 1)]

/-- One block, for `nr` rounds. -/
def body (nr : Nat) : List Instr := first ++ rounds (nr - 1) ++ final nr

/-- The blocks, for `nr` rounds. -/
def blocks (nr : Nat) : Prog isa := .loop (.block (body nr)) .ne

/-- The blocks, for `rounds` (10, 12 or 14) in `rsi`, after `cmp rsi, 10`. -/
def loops : Prog isa :=
  .ite .e (blocks 10) (.seq (.block [.alu .cmp .rsi (.imm 12)]) (.ite .e (blocks 12) (blocks 14)))

/-- The chaining value into `xmm0`, and `cmp rsi, 10`. -/
def setup : List Instr := [.movdquLoad .xmm0 (at_ .rdx 0), .alu .cmp .rsi (.imm 10)]

/-- The chaining value, the last ciphertext block, to `iv`. -/
def finish : List Instr := [.movdquStore (at_ .rdx 0) .xmm0]

def encrypt : Prog isa :=
  .seq (.block [.alu .test .r8 (.reg .r8)])
    (.ite .e (.block []) (.seq (.block setup) (.seq loops (.block finish))))

end VG.Impl.AesCbc.X86_64.Encrypt
