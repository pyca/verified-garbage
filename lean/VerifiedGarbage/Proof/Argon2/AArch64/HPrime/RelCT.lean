import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-! # Composition helpers for ARM64 H′ timing proofs -/

namespace VG.AArch64

theorem RelCT.taintRegs {τ : Taint.T} {P : State → State → Prop} {c : Prog isa}
    (hp : ∀ s₁ s₂, P s₁ s₂ → Taint.Agree τ s₁ s₂) (rs : List Reg) {hc : VG.Taint.Hint Taint.T}
    (h : ((taint.check τ c hc).map fun τ' => (RegSet.ofList rs).subset τ') = some true) :
    RelCT isa P c fun s t => s.sp = t.sp ∧ ∀ r ∈ rs, s.gpr r = t.gpr r := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨τ', hc', hs⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hc' (hp _ _ hP) e₁ e₂
  exact ⟨ht, ha.1, fun r hr => ha.2 r (RegSet.mem_of_subset hs (RegSet.mem_ofList.mpr hr))⟩

end VG.AArch64
