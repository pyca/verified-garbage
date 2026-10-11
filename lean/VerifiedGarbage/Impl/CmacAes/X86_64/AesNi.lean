module

public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# AES-CMAC's chaining with AES-NI on x86-64

`vg_cmac_aes_update_aesni_cbc(schedule = rdi, rounds = rsi, state = rdx, data = rcx, n = r8,
scratch = r9)`, with the contract of `vg_cmac_aes_update`
(`Spec.Cmac.aesUpdateContract`), for CPUs with AES-NI: §6.2 step 6,
`Cᵢ = CIPH_K(Cᵢ₋₁ ⊕ Mᵢ)`, one block after the other in registers.

The round keys stay in SSE registers across all blocks: round key `j`
(`1 ≤ j ≤ 13`) in `xmm(j + 1)` (`kreg j`), loaded once, all 13 of them
whatever the number of rounds (the 240-byte schedule buffer holds them).
The chaining value stays in `xmm0`, loaded once and stored once, XORed with
the first round key `K₀`: then `pxor` with the next block `Mᵢ` (loaded into
`xmm1`) is the cipher's first `AddRoundKey` of `Cᵢ₋₁ ⊕ Mᵢ`, and the last
round, `aesenclast` with `K_Nr ⊕ K₀` (in `xmm15`), leaves `Cᵢ ⊕ K₀` for the
next block. Each block is `Nr + 1` dependent instructions. The number of
rounds selects one of three loops, once (a branch on the public `rounds`).

`scratch` is not used, nor the stack, and no callee-saved register is
written. Every branch and every address depends only on the pointers,
`rounds` and `n`.
-/

@[expose] public section

namespace VG.Impl.CmacAes.X86_64.AesNi

open VG.X86_64

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- The register that holds round key `j` (`1 ≤ j ≤ 13`). -/
def kreg : Nat → XReg
  | 1 => .xmm2 | 2 => .xmm3 | 3 => .xmm4 | 4 => .xmm5 | 5 => .xmm6 | 6 => .xmm7 | 7 => .xmm8
  | 8 => .xmm9 | 9 => .xmm10 | 10 => .xmm11 | 11 => .xmm12 | 12 => .xmm13 | _ => .xmm14

/-- Round keys 1 to `k` into their registers. -/
def loadKeys (k : Nat) : List Instr :=
  (List.range k).map fun i => .movdquLoad (kreg (i + 1)) (at_ .rdi (16 * (i + 1)))

/-- `K₀` into `xmm1`, `C ⊕ K₀` into `xmm0`, round keys 1 to 13 into their
registers, and `cmp rsi, 10`. -/
def setup : List Instr :=
  [.movdquLoad .xmm1 (at_ .rdi 0), .movdquLoad .xmm0 (at_ .rdx 0), .xop (.bin .pxor .xmm0 .xmm1)] ++
  loadKeys 13 ++ [.alu .cmp .rsi (.imm 10)]

/-- `K_Nr ⊕ K₀` into `xmm15`, for `nr` rounds. -/
def last (nr : Nat) : List Instr :=
  [.movdquLoad .xmm15 (at_ .rdi (16 * nr)), .xop (.bin .pxor .xmm15 .xmm1)]

/-- Rounds 1 to `k` of the block in `xmm0`. -/
def rounds (k : Nat) : List Instr :=
  (List.range k).map fun j => .xop (.bin .aesenc .xmm0 (kreg (j + 1)))

/-- One block, for `nr` rounds; ZF is set when no blocks are left. -/
def body (nr : Nat) : List Instr :=
  [.movdquLoad .xmm1 (at_ .rcx 0), .xop (.bin .pxor .xmm0 .xmm1)] ++ rounds (nr - 1) ++
  [.xop (.bin .aesenclast .xmm0 .xmm15), .alu .add .rcx (.imm 16), .alu .sub .r8 (.imm 1)]

/-- The blocks, for `nr` rounds. -/
def blocks (nr : Nat) : Prog isa := .seq (.block (last nr)) (.loop (.block (body nr)) .ne)

/-- The blocks, for `rounds` (10, 12 or 14) in `rsi`, after `cmp rsi, 10`. -/
def loops : Prog isa :=
  .ite .e (blocks 10) (.seq (.block [.alu .cmp .rsi (.imm 12)]) (.ite .e (blocks 12) (blocks 14)))

/-- `Cₙ ⊕ K₀ ⊕ K₀` to the state. -/
def finish : List Instr :=
  [.movdquLoad .xmm1 (at_ .rdi 0), .xop (.bin .pxor .xmm0 .xmm1), .movdquStore (at_ .rdx 0) .xmm0]

def update : Prog isa :=
  .seq (.block [.alu .test .r8 (.reg .r8)])
    (.ite .e (.block []) (.seq (.block setup) (.seq loops (.block finish))))

end VG.Impl.CmacAes.X86_64.AesNi
