module

public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Framework.RelCT

/-!
# Calls as inlined code: relational constant time

`ConstantTime.of_inline` for a piece of code (`RelCT.of_inline`), such as a
function's body within its frames: related states that run `c.inline`, keep
every buffer off the 8 bytes below `rsp` and agree on `rsp` give `c` the
leakage `c.inline` has.
-/

@[expose] public section

namespace VG.X86_64

theorem RelCT.of_inline {c : Prog isa} (hc : c.InlineOk = true) {P : State → State → Prop}
    (hrun : ∀ s₁ s₂, P s₁ s₂ → (∃ t s', Exec isa c.inline s₁ t s') ∧ ∃ t s', Exec isa c.inline s₂ t s')
    (hclear : ∀ s₁ s₂, P s₁ s₂ → Clear (hole (s₁.gpr .rsp)) s₁ ∧ Clear (hole (s₂.gpr .rsp)) s₂)
    (hrsp : ∀ s₁ s₂, P s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp)
    (hct : RelCT isa P c.inline fun _ _ => True) : RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨⟨tb₁, b₁, f₁⟩, ⟨tb₂, b₂, f₂⟩⟩ := hrun s₁ s₂ hp
  obtain ⟨c₁, c₂⟩ := hclear s₁ s₂ hp
  obtain ⟨_, _, ta₁, a₁, _, l₁⟩ := Exec.of_inline hc f₁ c₁
  obtain ⟨_, _, ta₂, a₂, _, l₂⟩ := Exec.of_inline hc f₂ c₂
  obtain ⟨rfl, -⟩ := Exec.det e₁ a₁
  obtain ⟨rfl, -⟩ := Exec.det e₂ a₂
  have ht := (hct s₁ s₂ tb₁ tb₂ b₁ b₂ hp f₁ f₂).1
  subst ht
  rw [hrsp s₁ s₂ hp] at l₁
  exact ⟨l₁.unique l₂, trivial⟩

end VG.X86_64
