module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.TCB.RISCV64.Target

import VerifiedGarbage.Proof.Argon2.Dimensions

/-!
# Argon2 on RISC-V: the contract of the derivation's proof

`deriveRV`: `vg_argon2`'s contract, with its precondition a structure
(`DPre`; `Derive/Verified.lean` reaches the shared contract). The
derivation uses the 320 bytes of stack below the stack pointer, its frame:
the functions it calls use none. `memory` and `scratch` are 8-byte aligned,
as RISC-V's contracts require of arrays of `u64` (`Abi.alignsBufs`).
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

/-- Argument `i`: `a0`–`a7`, then those on the stack. -/
def arg (s : State) : Nat → BitVec 64
  | 0 => s.gpr .a0
  | 1 => s.gpr .a1
  | 2 => s.gpr .a2
  | 3 => s.gpr .a3
  | 4 => s.gpr .a4
  | 5 => s.gpr .a5
  | 6 => s.gpr .a6
  | 7 => s.gpr .a7
  | i + 8 => stackArg s i

/-- The 32-bit argument `i`. -/
abbrev arg32 (s : State) (i : Nat) : BitVec 32 := (arg s i).setWidth 32

/-- The 32-bit arguments: `kind`, `iterations`, `memory_cost`, `lanes` and
`threads`. -/
def intArgs : List Nat := [0, 5, 6, 7, 8]

/-- What is public of argument `i`: its low 32 bits if it is a 32-bit one. -/
def argPub (s : State) (i : Nat) : BitVec 64 :=
  if i ∈ intArgs then (arg32 s i).setWidth 64 else arg s i

section
variable (s₀ : State)

abbrev kindV : BitVec 32 := arg32 s₀ 0
abbrev pwP : Addr := arg s₀ 1
abbrev pwL : Nat := (arg s₀ 2).toNat
abbrev saltP : Addr := arg s₀ 3
abbrev saltL : Nat := (arg s₀ 4).toNat
abbrev itersN : Nat := (arg32 s₀ 5).toNat
abbrev mcostN : Nat := (arg32 s₀ 6).toNat
abbrev lanesN : Nat := (arg32 s₀ 7).toNat
abbrev threadsN : Nat := (arg32 s₀ 8).toNat
abbrev secP : Addr := arg s₀ 9
abbrev secL : Nat := (arg s₀ 10).toNat
abbrev adP : Addr := arg s₀ 11
abbrev adL : Nat := (arg s₀ 12).toNat
abbrev memP : Addr := arg s₀ 13
abbrev blocksN : Nat := (arg s₀ 14).toNat
abbrev scrP : Addr := arg s₀ 15
abbrev outP : Addr := arg s₀ 16
abbrev outL : Nat := (arg s₀ 17).toNat

/-- The parameters. -/
abbrev prm : Params := params (kindV s₀).toNat (itersN s₀) (mcostN s₀) (lanesN s₀) (outL s₀)

abbrev pwR : Region := ⟨pwP s₀, pwL s₀⟩
abbrev saltR : Region := ⟨saltP s₀, saltL s₀⟩
abbrev secR : Region := ⟨secP s₀, secL s₀⟩
abbrev adR : Region := ⟨adP s₀, adL s₀⟩
abbrev memR : Region := ⟨memP s₀, blocksN s₀ * 1024⟩
abbrev scrR : Region := ⟨scrP s₀, 16384⟩
abbrev outR : Region := ⟨outP s₀, outL s₀⟩
/-- The ten arguments on the stack. -/
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 80⟩
/-- The stack the derivation uses. -/
abbrev stkR0 : Region := below s₀.sp 320

/-- The inputs, on entry. -/
abbrev pwB : List Byte := bytesAt s₀.mem (pwR s₀).base (pwL s₀)
abbrev saltB : List Byte := bytesAt s₀.mem (saltR s₀).base (saltL s₀)
abbrev secB : List Byte := bytesAt s₀.mem (secR s₀).base (secL s₀)
abbrev adB : List Byte := bytesAt s₀.mem (adR s₀).base (adL s₀)

end

/-- The facts of `deriveRV`'s precondition. -/
structure DPre (s₀ : State) : Prop where
  rd : s₀.rd = [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀]
  wr : s₀.wr = [memR s₀, scrR s₀, outR s₀]
  ro_w : ∀ r ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀], ∀ w ∈ [memR s₀, scrR s₀, outR s₀],
    r.Disjoint w
  mem_scr : (memR s₀).Disjoint (scrR s₀)
  mem_out : (memR s₀).Disjoint (outR s₀)
  scr_out : (scrR s₀).Disjoint (outR s₀)
  stk_all : ∀ r ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, memR s₀, scrR s₀, outR s₀], (stkR0 s₀).Disjoint r
  pw_fits : (pwP s₀).toNat + pwL s₀ ≤ 2 ^ 64
  salt_fits : (saltP s₀).toNat + saltL s₀ ≤ 2 ^ 64
  sec_fits : (secP s₀).toNat + secL s₀ ≤ 2 ^ 64
  ad_fits : (adP s₀).toNat + adL s₀ ≤ 2 ^ 64
  mem_fits : (memP s₀).toNat + blocksN s₀ * 1024 ≤ 2 ^ 64
  scr_fits : (scrP s₀).toNat + 16384 ≤ 2 ^ 64
  out_fits : (outP s₀).toNat + outL s₀ ≤ 2 ^ 64
  sp_lo : 320 ≤ s₀.sp.toNat
  sp_hi : s₀.sp.toNat + 80 ≤ 2 ^ 64
  sp_al : s₀.sp.toNat % 16 = 0
  mem_al : (memP s₀).toNat % 8 = 0
  scr_al : (scrP s₀).toNat % 8 = 0
  kind_le : (kindV s₀).toNat ≤ 2
  valid : valid (prm s₀) (pwL s₀) (saltL s₀) (secL s₀) (adL s₀)
  threads : 1 ≤ threadsN s₀ ∧ threadsN s₀ < 2 ^ 24
  blocks : blocksN s₀ = (prm s₀).blocks

/-- `vg_argon2`. -/
def deriveRV : Contract isa where
  pre := DPre
  post s s' := bytesAt s'.mem (outP s) (outL s) =
    derive (prm s) (pwB s) (saltB s) (secB s) (adB s)
  pub s₁ s₂ := (s₁.sp = s₂.sp ∧ ∀ i < 18, argPub s₁ i = argPub s₂ i) ∧
    references (prm s₁) (pwB s₁) (saltB s₁) (secB s₁) (adB s₁) =
      references (prm s₂) (pwB s₂) (saltB s₂) (secB s₂) (adB s₂)

namespace DPre
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem lanes_pos : 1 ≤ lanesN s₀ := hp.valid.1
theorem lanes_lt : lanesN s₀ < 2 ^ 24 := hp.valid.2.1
theorem passes_pos : 1 ≤ itersN s₀ := hp.valid.2.2.1
theorem memory_ge : 8 * lanesN s₀ ≤ mcostN s₀ := hp.valid.2.2.2.2.1
theorem tag_ge : 4 ≤ outL s₀ := hp.valid.2.2.2.2.2.2.1
theorem tag_lt : outL s₀ < 2 ^ 32 := hp.valid.2.2.2.2.2.2.2.1

theorem segLen_two : 2 ≤ (prm s₀).segmentLen :=
  Proof.Argon2.segmentLen_ge_two _ hp.lanes_pos hp.memory_ge

theorem segLen_eq : (prm s₀).segmentLen = mcostN s₀ / (4 * lanesN s₀) :=
  Proof.Argon2.segmentLen_eq _ hp.lanes_pos

theorem laneLen_eq : (prm s₀).laneLen = 4 * (prm s₀).segmentLen :=
  Proof.Argon2.laneLen_segments _ hp.lanes_pos

theorem blocks_eq : blocksN s₀ = lanesN s₀ * (prm s₀).laneLen := by
  rw [hp.blocks]; exact Proof.Argon2.blocks_lanes _ hp.lanes_pos

theorem blocks_le : blocksN s₀ ≤ mcostN s₀ := by
  rw [hp.blocks]; exact Proof.Argon2.blocks_le_memory _

end DPre

theorem mcost_lt (s₀ : State) : mcostN s₀ < 2 ^ 32 := (arg32 s₀ 6).isLt

end VG.Proof.Argon2.RISCV64.Derive
