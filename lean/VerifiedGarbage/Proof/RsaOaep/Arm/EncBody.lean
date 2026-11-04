module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
public import VerifiedGarbage.Proof.RsaOaep.Arm.EncEm

import VerifiedGarbage.Proof.RsaOaep.Arm.EncMask
import VerifiedGarbage.Proof.RsaOaep.Arm.EncCall
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaOaep.Arm.LabelT
import VerifiedGarbage.Proof.RsaOaep.Arm.Calls
import VerifiedGarbage.Proof.RsaPss.Arm.Step
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Impl.RsaOaep.Arm

/-!
# RSAES-OAEP encryption with a precomputed public key on ARMv7: the body

The digest length of the label's hash function's table (`len_vp`), and, for
that length (`byLen_vp`), the checks, then zeros to `out` if the message
does not fit (`fail_vp`), or `EM` (`em_vp`), its masks (`mask_vp`) and the
call (`pa_vp`, `call_vp`): `body_vp`.
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

/-- After the checks, when the message fits, with the label's hash function
`h` and MGF1's `g`. -/
theorem main_vp (P : EP) (g : OHash) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) (c : PdImpl) :
    VP (Sy (E0 h P)) (encMain h.H f c.name c.code) (Sy (Fin h g P)) := by
  show VP _ (.seq (encEm h.H f) (.seq (.block (dbArgs h.H 3)) (.seq (mgfXor f 17) (.seq (.block (seedArgs h.H 3))
    (.seq (mgfXor f 17) (.seq (.block pubArgs) (.call c.name c.code))))))) _
  refine (em_vp h P hTL fne).seq (VP.assoc (VP.assoc (VP.assoc ?_)))
  exact (vp_unassoc (vp_unassoc (mask_vp h g P hT fne))).seq (VP.syms ((pa_vp h g P).seq (call_vp h g P c)))

/-- The digest length of the label's hash function's table to `r1`. -/
theorem len_vp (P : EP) {f : Fns} (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ) :
    VP (S h P) (.block (lenLoad 16)) (fun σ s => S h P σ s ∧ s.gpr .r1 = BitVec.ofNat 32 h.H.D) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  obtain ⟨tR, tRo, tC⟩ := tblL_of hi₀
  show VP _ (.block ([Impl.RsaPss.Arm.ld .r1 (Impl.RsaPss.Arm.arg 16)] ++ [.ldr .r1 .r1 16])) _
  refine VP.block_append (G := fun σ s => S h P σ s ∧ s.gpr .r1 = P.tabL)
    (VP.ldrSp (c := [(.r1, Impl.RsaPss.Arm.arg 16)]) (fun _ _ _ _ h₁ h₂ => h₁.2.sp.trans h₂.2.sp.symm)
      fun σ s hs => ?_)
    (VP.taint [.r1] lenWord_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
  · obtain ⟨hi, st⟩ := id hs
    obtain ⟨a16, r16, v16⟩ := argAt hi st (j := 16) (by decide)
    replace v16 : s.mem.readW ((P.lay h.H.D).fr (Impl.RsaPss.Arm.arg 16)) 32 = P.tabL := v16
    have hw : WP isa (.block [.ldrSp .r1 (Impl.RsaPss.Arm.arg 16)]) s fun t => t = s.setReg .r1 P.tabL := by
      apply WP.of_runBlock
      simp only [runBlock_cons, exec, arg_lt (show 16 < 18 by decide), ↓reduceIte, State.load32, st.sp, a16,
        r16, v16, Option.map_some, runStep_some, runBlock_nil]
      simp
    refine WP.mono hw fun t e => ?_
    subst e
    exact ⟨⟨hi, st.regs rfl rfl rfl rfl⟩, by simp only [VG.Arm.RegUpd.gpr_setReg, ↓reduceIte]⟩
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
  · obtain ⟨⟨hi, st⟩, h1⟩ := hs
    have T := hTL σ hi.tabTL
    refine WP.mono (wp_ldrT (by decide) h1 (St_roR st tRo (tC 16 (by decide)))
      ((St_roW st tRo (tC 16 (by decide))).trans T.d)) fun t e => ?_
    subst e
    exact ⟨⟨hi, st.regs rfl rfl rfl rfl⟩, by simp only [VG.Arm.RegUpd.gpr_setReg, ↓reduceIte]⟩

/-- The tail for a digest length, which is all it uses of the hash
function's shape. -/
theorem encTail_D {G G' : Impl.Pbkdf2.Stream.Arm.Hash} (hD : G.D = G'.D) (f : Fns) (n : String) (c : Prog isa) :
    encTail G f n c = encTail G' f n c := by
  simp only [encTail, encMain, encEm, encChk, seedSet, lhSet, dbArgs, seedArgs, hD]

/-- The body. -/
theorem body_vp (P : EP) (g : OHash) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) (c : PdImpl) :
    VP (Sy (S h P)) (encBody f c.name c.code) (Sy (Fin h g P)) := by
  show VP _ (.seq (.block (lenLoad 16)) (byLen (fun d => encTail (ofLen d) f c.name c.code) lens)) _
  refine (VP.syms (len_vp h P hTL)).seq (byLen_vp (D := h.H.D) (by have := h.D_le; omega) (fun _ _ hs => hs.1.2)
    (fun σ s v ⟨⟨⟨hi, st⟩, r1⟩, sy⟩ => ⟨⟨⟨hi, st.regs rfl rfl rfl rfl⟩, r1⟩, sy⟩) ?_ h.lens lens_certs)
  show VP _ (encTail (ofLen h.H.D) f c.name c.code) _
  rw [encTail_D (G := ofLen h.H.D) (G' := h.H) rfl]
  show VP _ (.seq (.block (encChk h.H)) (.ite .ne encFail (encMain h.H f c.name c.code))) _
  refine ((VP.syms (chk_vp h P)).mono (fun _ _ ⟨⟨s', _⟩, sy⟩ => ⟨s', sy⟩) fun _ _ x => x).seq
    (VP.ite (fun _ _ _ _ h₁ h₂ => by
      rw [VG.Proof.X25519.Arm.eval_ne, VG.Proof.X25519.Arm.eval_ne, h₁.1.2.2, h₂.1.2.2])
    ((VP.syms (fail_vp h g P)).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x) ?_)
  refine (main_vp h P g hT hTL fne c).mono (fun σ s ⟨⟨⟨hc, hi, z⟩, sy⟩, e⟩ => ⟨⟨hc, hi, ?_⟩, sy⟩) fun _ _ hh => hh
  rw [VG.Proof.X25519.Arm.eval_ne, z] at e
  simpa using e

end VG.Proof.RsaOaep.Arm.Enc
