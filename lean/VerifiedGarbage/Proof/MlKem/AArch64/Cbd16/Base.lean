module
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.AArch64.Isa

import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Impl.MlKem.AArch64.Basic

/-! # CBD2 contract and input representation -/

@[expose] public section

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- AArch64 contract for `vg_mlkem_cbd2(b = x0, f = x1)`: writes
`SamplePolyCBD₂` of the 128 bytes at `b` to `f`, reduced. The code may read
`b` and write `f`, which do not overlap. -/
def cbd2AArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, 128⟩] ∧ s.wr = [⟨s.gpr .x1, 1024⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 128⟩ ⟨s.gpr .x1, 1024⟩
  post s s' := PolyIs s'.mem (s.gpr .x1) (samplePolyCBD 2 (bytesAt s.mem (s.gpr .x0) 128))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Cbd2

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .x0
abbrev fP : Addr := s₀.gpr .x1
abbrev bR : Region := ⟨bP s₀, 128⟩
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) 128
/-- Coefficient `i` of the output. -/
def G (i : Nat) : BitVec 32 := BitVec.ofNat 32 ((samplePolyCBD 2 (B s₀))[i]!).val
/-- Byte `j` of the input, as a number. -/
abbrev byte (j : Nat) : Nat := ((B s₀).getD j 0).toNat

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [bR s₀]
  wr : s₀.wr = [polyRegion (fP s₀)]
  disj : (bR s₀).Disjoint (polyRegion (fP s₀))

theorem Pre.byte_eq {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [polyRegion (fP s₀)] s₀.mem m)
    {j : Nat} (hj : j < 128) : (m (bP s₀ + BitVec.ofNat 64 j)).toNat = byte s₀ j := by
  rw [byte_frame (len := 128) hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj)
    (by decide) hj]
  show _ = ((bytesAt s₀.mem (bP s₀) 128).getD j 0).toNat
  rw [bytesAt_getD _ _ hj]

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 1024⟩]

end VG.Proof.MlKem.AArch64.Cbd2
