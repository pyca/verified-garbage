module

public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# Constant time of code the taint analysis checks, by relating two runs (x86-64)

`RelCT.taintRegs`, apart from `RelCT.lean` so that its importers that never
use the taint analysis need not import it.
-/

@[expose] public section

namespace VG.X86_64

/-- Code the taint analysis proves constant time, which leaves the registers
`rs` public: they agree in the final states. -/
theorem RelCT.taintRegs {τ : Taint.T} {P : State → State → Prop} {c : Prog isa}
    (hp : ∀ s₁ s₂, P s₁ s₂ → Taint.Agree τ s₁ s₂) (rs : List Reg) {hc : VG.Taint.Hint Taint.T}
    (h : ((taint.check τ c hc).map fun τ' => (RegSet.ofList rs).subset τ'.regs) = some true) :
    RelCT isa P c fun s₁ s₂ => ∀ r ∈ rs, s₁.gpr r = s₂.gpr r := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨τ', hc', hs⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hc' (hp _ _ hP) e₁ e₂
  exact ⟨ht, fun r hr => ha.rf.1 r (RegSet.mem_of_subset hs (RegSet.mem_ofList.mpr hr))⟩

end VG.X86_64
