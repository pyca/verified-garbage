module

import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.MlKem.Ntt
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# ML-KEM on AArch64: what the NTT and its inverse share

The per-target contract of both (`inPlaceAArch64`), what it gives the proofs
(`Pre`), and the constants they load (`vconsts_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem

/-- The contract the proofs are written against (and verified callers use);
the artifacts' are the shared contracts of `Spec/`, which imply it.
AArch64 contract for `f = x0, scratch = x1`: if the polynomial at `f` is
reduced, it becomes `t` of it, reduced. The code may read and write `f` and
`scratch` (1024 bytes), which do not overlap. -/
def inPlaceAArch64 (t : Poly → Poly) : Contract AArch64.isa where
  pre s :=
    s.rd = [] ∧ s.wr = [⟨s.gpr .x0, 1024⟩, ⟨s.gpr .x1, 1024⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 1024⟩ ⟨s.gpr .x1, 1024⟩ ∧ Reduced s.mem (s.gpr .x0)
  post s s' := PolyIs s'.mem (s.gpr .x0) (t (polyAt s.mem (s.gpr .x0)))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Ntt

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem

section
variable (s₀ : State)

abbrev fP : Addr := s₀.gpr .x0
abbrev sP : Addr := s₀.gpr .x1
end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [polyRegion (fP s₀), polyRegion (sP s₀)]
  disj : (polyRegion (fP s₀)).Disjoint (polyRegion (sP s₀))
  red : Reduced s₀.mem (fP s₀)

theorem pre_of {t : Poly → Poly} {s₀ : State} (h : (inPlaceAArch64 t).pre s₀) : Pre s₀ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- `vconsts`: `q` and `M` in `x9`, `x10` and the lanes of `v16`, `v17`. -/
theorem vconsts_ok (s : State) :
    WP isa (.block vconsts) s fun s' => Keep [.x9, .x10] s s' ∧ s'.mem = s.mem ∧ VConsts s' ∧
      ∀ r, r ≠ .v16 → r ≠ .v17 → s'.v r = s.v r := by
  show WP isa (.block ((.movz .x .x9 3329 0 :: movImm .x10 645083) ++
    ([.vop (.dup .s4 .v16 .x9), .vop (.dup .s4 .v17 .x10)] : List Instr))) s _
  refine wp_scalar (by decide) (P := fun s₂ => Keep [.x9, .x10] s s₂ ∧ s₂.mem = s.mem ∧
      (s₂.gpr .x9).toNat = 3329 ∧ (s₂.gpr .x10).toNat = 645083)
    (wp_movz fun s₁ h₁ e₁ => by
      rw [← List.append_nil (movImm _ _)]
      exact wp_movImm fun s₂ h₂ e₂ => wp_nil ⟨(h₁.keep.trans h₂.keep).mono, by rw [h₂.mem, h₁.mem],
        by rw [h₂.get .x9, e₁]; rfl, by rw [e₂]; rfl⟩) fun s₂ ⟨k₂, m₂, e9, e10⟩ hv₂ => ?_
  refine wp_vop (d := .v16) rfl fun s₃ h₃ => wp_vop (d := .v17) rfl fun s₄ h₄ => wp_nil ?_
  refine ⟨(k₂.trans (h₃.keep.trans h₄.keep)).mono, by rw [h₄.mem, h₃.mem, m₂], ⟨?_, ?_⟩,
    fun r h16 h17 => by rw [h₄.get r h17, h₃.get r h16, hv₂]⟩
  · rw [h₄.get .v16, h₃.v]
    exact lanes_dup.congr fun _ _ => by rw [BitVec.toNat_setWidth, e9]
  · rw [h₄.v, h₃.gpr]
    exact lanes_dup.congr fun _ _ => by rw [BitVec.toNat_setWidth, e10]

end VG.Proof.MlKem.AArch64.Ntt
