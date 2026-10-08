import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.LoopStep

/-! # Termination leaves exactly the fixed final batch or batches -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)

theorem stopped_length {s₀ : State} (hp : SPre s₀) (dec : Bool) (g : Nat)
    (hm : g % 8 = 0) (ht : g + tailSize dec ≤ nb s₀) (hl : nb s₀ - g < threshold dec) :
    nb s₀ = g + tailSize dec := by
  have hn := hp.nbm
  cases dec <;> simp [tailSize, threshold] at ht hl ⊢ <;> omega

theorem loopRun_ok {s₀ s : State} {P : Nat → Block} {dec : Bool} {g : Nat}
    (hp : SPre s₀) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ P dec g s)
    (hn : g + threshold dec ≤ nb s₀) :
    WP isa (.loop (body8 dec (nr s₀)) .ae) s fun t =>
      ∃ g, nb s₀ = g + tailSize dec ∧ LoopInv s₀ P dec g t := by
  let I : Nat → State → Prop := fun m t => ∃ g,
    m = nb s₀ - g ∧ g + threshold dec ≤ nb s₀ ∧ LoopInv s₀ P dec g t
  have step : ∀ m t, I m t → WP isa (body8 dec (nr s₀)) t fun u =>
      (eval .ae u = some false ∧ ∃ g, nb s₀ = g + tailSize dec ∧ LoopInv s₀ P dec g u) ∨
      (eval .ae u = some true ∧ ∃ m' < m, I m' u) := by
    rintro m t ⟨g, rfl, hn, h⟩
    refine WP.mono (loopStep_ok hp hlaw h hn) fun u ⟨hu, hcf⟩ => ?_
    by_cases halt : nb s₀ - (g + 8) < threshold dec
    · exact .inl ⟨by simp only [eval, hcf, halt, decide_true, Option.map_some, Bool.not_true],
        g + 8, stopped_length hp dec (g + 8) hu.multiple hu.tail_le halt, hu⟩
    · have hg := hu.core.g_le
      refine .inr ⟨by simp only [eval, hcf, halt, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - (g + 8), ?_, g + 8, rfl, by omega, hu⟩
      have ht := hu.tail_le
      have hl : 0 < tailSize dec := by cases dec <;> decide
      omega
  exact WP.loop (M := isa) I step (nb s₀ - g) s ⟨g, rfl, hn, h⟩

theorem loopMaybe_ok {s₀ s : State} {P : Nat → Block} {dec : Bool} {g : Nat}
    (hp : SPre s₀) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ P dec g s)
    (hcf : s.cf = some (decide (nb s₀ - g < threshold dec))) :
    WP isa (.ite .b (.block []) (.loop (body8 dec (nr s₀)) .ae)) s fun t =>
      ∃ g, nb s₀ = g + tailSize dec ∧ LoopInv s₀ P dec g t := by
  refine WP.ite (decide (nb s₀ - g < threshold dec)) (by simp only [eval, hcf]) (fun he => ?_) (fun he => ?_)
  · exact WP.block_nil ⟨g, stopped_length hp dec g h.multiple h.tail_le (by simpa using he), h⟩
  · have hn : ¬nb s₀ - g < threshold dec := by simpa using he
    have hg := h.core.g_le
    exact loopRun_ok hp hlaw h (by omega)

end VG.Proof.Gcm.X86_64.StitchAvx8
