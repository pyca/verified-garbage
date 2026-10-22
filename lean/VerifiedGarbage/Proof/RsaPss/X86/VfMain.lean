module

public import VerifiedGarbage.Proof.RsaPss.X86.VfLogic
import VerifiedGarbage.Proof.RsaPss.X86.SgEnc3
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt

/-!
# RSASSA-PSS verification with a precomputed public key on x86: the body

As on ARMv7 (`Proof/RsaPss/Arm/VfMain.lean`): the checks, then either 0 or
the call and the pieces after it, proven over the state the call leaves
(`VQ.reidx`); the result is `verify`'s (`fin_of`, `body_vq`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Proof.RsaPss.X86.Sg (vpAssoc)

variable (h : PssHash)

/-- The end of the body, over the state `τ` the call leaves. -/
abbrev GE (P : EP) (τ t : State) : Prop :=
  Ctx (P.lay h.D) P.scr τ t ∧ K2 h P τ t.mem ∧
    t.gpr .eax = if acc2 h P τ = 0 ∧ HOk h P τ (if P.any = 0 then Mf h P τ else Ma h P τ) then 1 else 0

/-- The path for the expected salt length, or for any. -/
theorem tailIte_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem) ∧ s.zf = some (decide (P.any = 0)))
      (.ite .e (fixedPath h.H) (anyPath h.H)) (GE h P) := by
  refine VP.ite (fun σ s hs => ⟨decide (P.any = 0), by simp only [eval, hs.2]⟩)
    (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
  · by_cases ha : P.any = 0
    · exact (fixed_vp h P hP).mono (fun τ s ⟨⟨⟨hc, hk⟩, _⟩, _⟩ => ⟨hc, hk, ha⟩)
        fun τ s ⟨hc, hk, r0⟩ => ⟨hc, hk, by rw [r0, ite_eq_left ha]⟩
    · exact VP.empty fun τ s ⟨⟨_, z⟩, e⟩ => by
        simp only [eval, z, decide_eq_false ha] at e; exact absurd e (by decide)
  · by_cases ha : P.any = 0
    · exact VP.empty fun τ s ⟨⟨_, z⟩, e⟩ => by
        simp only [eval, z, decide_eq_true ha] at e; exact absurd e (by decide)
    · exact (any_vp h P hP).mono (fun τ s ⟨⟨⟨hc, hk⟩, _⟩, _⟩ => ⟨hc, hk, trivial⟩)
        fun τ s ⟨hc, hk, r0⟩ => ⟨hc, hk, by rw [r0, ite_eq_right ha]⟩

/-- After the call. -/
theorem rest_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (W0 h P) (.seq (.block accSet) (.seq (.block acc0) (.seq (mgfXor h.H) (.seq (.block topSet)
      (.seq (.block topAnd) (.seq (.block scanSet) (.seq (countLoop scanBody) (.seq (.block posChk)
        (.ite .e (fixedPath h.H) (anyPath h.H)))))))))) (GE h P) :=
  vpAssoc ((acc_vp h P hP).seq (vpAssoc (vpAssoc ((unmask_vp h P hP).seq
    ((scanSet_vp h P hP).seq ((scan_vp h P hP).seq ((pos_vp h P hP).seq (tailIte_vp h P hP))))))))

/-- The result is `verify`'s. -/
theorem fin_of (P : EP) {σ τ t : State} (hv : V2 h P σ τ) (hg : GE h P τ t) : Fin h P σ t := by
  obtain ⟨⟨hc, hi, hf, -⟩, hcr⟩ := hv
  obtain ⟨hc', hk, r0⟩ := hg
  have st : (P.lay h.D).St σ t :=
    ⟨hc.st.ok, hc'.st.sp, hc'.st.rd.trans hc.st.rd, hc'.st.wr.trans hc.st.wr, hc.st.frame.trans hc'.st.frame⟩
  refine ⟨⟨hi, st⟩, fun hpre => ?_⟩
  have hw := hcr hpre
  have hxb : Spec.Rsa.bytesAt τ.mem ((P.scr + BitVec.ofNat 32 oEm).setWidth 64) P.K =
      (Spec.Rsa.publicOpChecked P.nB P.eB (sigB P σ)).getD (Spec.RsaPss.zeros P.K) := by
    revert hw
    cases Spec.Rsa.publicOpChecked P.nB P.eB (sigB P σ) with
    | none => exact fun hw => hw.2
    | some y => exact fun hw => hw.2
  have hx : ∀ i < P.K, ((Spec.Rsa.publicOpChecked P.nB P.eB (sigB P σ)).getD (Spec.RsaPss.zeros P.K)).getD i 0 =
      emv P τ i := fun i hi' => by
    rw [← hxb, RsaPkcs1Sig.bytesAt_getD hi', (call_geo h hi).1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hdig : digB h P τ = digB h P σ := hc.st.ro (R := P.DIG h.D) (by simp)
  have g := good_iff h P τ hk.1 hf (RsaPkcs1Sig.bytesAt_len _ _ _) hx
  rw [hdig] at g
  rw [r0]
  by_cases e : acc2 h P τ = 0 ∧ HOk h P τ (if P.any = 0 then Mf h P τ else Ma h P τ)
  · rw [ite_eq_left e, ite_eq_left (g.1 e)]
  · rw [ite_eq_right e, ite_eq_right (fun h' => e (g.2 h'))]

/-- The body. -/
theorem body_vq (P : EP) (c : Ver.PublicImpl) : VQ (S h P) (verifyBody h.H c.name c.code) (Fin h P) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VQ.of_vp (VP.empty fun σ s hs => hP ⟨σ, hs.1⟩)
  show VQ _ (.seq (.block (verifyChk ++ params h.H)) (.ite .ne (.block [mi .eax 0])
    (.seq (.block pubArgs) (.seq (.call c.name c.code) _)))) _
  refine VQ.seq (chk_vp h P) (VQ.ite (fun σ s hs => ⟨!decide (fits h P), by simp only [eval, hs.2.2.2.2.2.2,
      Option.map_some]⟩) (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.2.2.2.2.2.2, h₂.2.2.2.2.2.2])
    (VQ.of_vp (fail_vp h P)) ?_)
  exact VQ.seq ((pa_vp h P).mono (fun σ s ⟨h1, e⟩ => m0_of h h1 e) fun _ _ h => h)
    (VQ.seq (call_vp h P c) (VQ.reidx (rest_vp h P hP) (fun σ s hv => w0_self h hv)
      fun σ τ t hv hg => fin_of h P hv hg))

end VG.Proof.RsaPss.X86.Vf
