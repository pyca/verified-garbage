module

public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified

/-!
# x86-64: code that restores MXCSR, with its calls inlined

`ctlOk` (`Mxcsr.lean`) of a code is `ctlOk` of the code with its calls
inlined (`Code.inline`), which the proofs of the functions that call others
run.
-/

@[expose] public section

namespace VG.X86_64

theorem restores_inline {a b : Prog isa} (h : restores a b = true) : restores a.inline b.inline = true := by
  unfold restores at h
  split at h
  · simp only [Code.inline]
    unfold restores
    simpa only [Code.allInstrs_inline] using h
  · cases h

/-- Code that restores MXCSR around every load of it does so with its calls inlined. -/
theorem ctlOk_inline : ∀ {c : Prog isa}, ctlOk c = true → ctlOk c.inline = true
  | .block _, h => h
  | .seq a b, h => by
    simp only [ctlOk, Bool.or_eq_true, Bool.and_eq_true] at h
    simp only [Code.inline, ctlOk, Bool.or_eq_true, Bool.and_eq_true]
    rcases h with h | ⟨ha, hb⟩
    · exact .inl (restores_inline h)
    · exact .inr ⟨ctlOk_inline ha, ctlOk_inline hb⟩
  | .ite _ t e, h => by
    simp only [ctlOk, Bool.and_eq_true] at h
    simp only [Code.inline, ctlOk, Bool.and_eq_true]
    exact ⟨ctlOk_inline h.1, ctlOk_inline h.2⟩
  | .loop b _, h => ctlOk_inline (c := b) h
  | .call _ b, h => h
  | .frame i b j, h => by
    simp only [ctlOk, Bool.and_eq_true] at h
    simp only [Code.inline, ctlOk, Bool.and_eq_true]
    exact ⟨⟨h.1.1, ctlOk_inline h.1.2⟩, h.2⟩
  | .icall .., h => h

end VG.X86_64
