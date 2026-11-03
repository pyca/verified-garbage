module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
public import VerifiedGarbage.Proof.RsaOaep.Arm.EncEm

import VerifiedGarbage.Proof.RsaOaep.Arm.EncMask
import VerifiedGarbage.Proof.RsaOaep.Arm.EncCall
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# RSAES-OAEP encryption with a precomputed public key on ARMv7: the body

The checks, then zeros to `out` if the message does not fit (`fail_vp`), or
`EM` (`em_vp`), its masks (`mask_vp`) and the call (`pa_vp`, `call_vp`):
`body_vp`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Enc

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

/-- Two runs of `(a; b); c` are two runs of `a; (b; c)`. -/
theorem relCT_unassoc {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          simp only [List.append_assoc] at ht ⊢
          exact ⟨ht, hq⟩

theorem vp_unassoc {F G : State → State → Prop} {a b c : Prog isa} (h : VP F (.seq a (.seq b c)) G) :
    VP F (.seq (.seq a b) c) G :=
  ⟨fun σ s hs => WP.assoc' (h.wp σ s hs), relCT_unassoc h.ct⟩

variable (h : OHash)

/-- A stage, with what follows it, keeping the addresses of the statics. -/
abbrev Sy (F : State → State → Prop) (σ s : State) : Prop := F σ s ∧ s.syms = σ.syms

/-- After the checks, when the message fits, with MGF1's hash function `g`. -/
theorem main_vp (P : EP) (g : OHash) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) (c : PdImpl) :
    VP (Sy (E0 h P)) (encMain h.H f c.name c.code) (Sy (Fin h g P)) := by
  show VP _ (.seq (encEm h.H) (.seq (.block (dbArgs h.H 3)) (.seq (mgfXor f 15) (.seq (.block (seedArgs h.H 3))
    (.seq (mgfXor f 15) (.seq (.block pubArgs) (.call c.name c.code))))))) _
  refine (VP.syms (em_vp h P)).seq (VP.assoc (VP.assoc (VP.assoc ?_)))
  exact (vp_unassoc (vp_unassoc (mask_vp h g P hT fne))).seq (VP.syms ((pa_vp h g P).seq (call_vp h g P c)))

/-- The body. -/
theorem body_vp (P : EP) (g : OHash) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) (c : PdImpl) :
    VP (Sy (S h P)) (encBody h.H f c.name c.code) (Sy (Fin h g P)) := by
  show VP _ (.seq (.block (encChk h.H)) (.ite .ne encFail (encMain h.H f c.name c.code))) _
  refine (VP.syms (chk_vp h P)).seq (VP.ite (fun _ _ _ _ h₁ h₂ => by
    rw [VG.Proof.X25519.Arm.eval_ne, VG.Proof.X25519.Arm.eval_ne, h₁.1.2.2, h₂.1.2.2])
    ((VP.syms (fail_vp h g P)).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x) ?_)
  refine (main_vp h P g hT fne c).mono (fun σ s ⟨⟨⟨hc, hi, z⟩, sy⟩, e⟩ => ⟨⟨hc, hi, ?_⟩, sy⟩) fun _ _ hh => hh
  rw [VG.Proof.X25519.Arm.eval_ne, z] at e
  simpa using e

end VG.Proof.RsaOaep.Arm.Enc
