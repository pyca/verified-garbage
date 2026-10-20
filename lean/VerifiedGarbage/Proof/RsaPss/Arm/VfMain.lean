module
public import VerifiedGarbage.Proof.RsaPss.Arm.VfAny
public import VerifiedGarbage.Proof.RsaPss.Arm.VfFixed

import VerifiedGarbage.Proof.RsaPss.Arm.VfLogic
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the body

After the call, over the state `τ` it leaves (`rest_vp`): `acc`, the
unmasking, the scan, and the path for the expected salt length; then the
result is `verify`'s (`fin_of`, by `good_iff`). The body (`body_vq`): the
checks, then 0 if something does not fit, or the call and the rest.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable (h : PssHash)

/-- The end of the body, over the state `τ` the call leaves. -/
abbrev GE (P : EP) (τ t : State) : Prop :=
  Ctx (P.lay h.D) P.scr τ t ∧ K2 h P τ t.mem ∧
    t.gpr .r0 = if acc2 h P τ = 0 ∧ HOk h P τ (if P.any = 0 then Mf h P τ else Ma h P τ) then 1 else 0

/-- The path for the expected salt length. -/
theorem tailIte_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem) ∧ s.z = decide (P.any = 0))
      (.ite .eq (fixedPath h.H) (anyPath h.H)) (GE h P) := by
  refine VP.ite (fun _ _ _ _ h₁ h₂ => by
    rw [VG.Proof.X25519.Arm.eval_eq, VG.Proof.X25519.Arm.eval_eq, h₁.2, h₂.2]) ?_ ?_
  · by_cases ha : P.any = 0
    · exact (fixed_vp h P hP).mono (fun τ s ⟨⟨⟨hc, hk⟩, _⟩, _⟩ => ⟨hc, hk, ha⟩)
        fun τ s ⟨hc, hk, r0⟩ => ⟨hc, hk, by rw [r0, ite_eq_left ha]⟩
    · exact VP.empty fun τ s ⟨⟨_, z⟩, e⟩ => by
        rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_false ha] at e; exact absurd e (by decide)
  · by_cases ha : P.any = 0
    · exact VP.empty fun τ s ⟨⟨_, z⟩, e⟩ => by
        rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_true ha] at e; exact absurd e (by decide)
    · exact (any_vp h P hP).mono (fun τ s ⟨⟨⟨hc, hk⟩, _⟩, _⟩ => ⟨hc, hk, trivial⟩)
        fun τ s ⟨hc, hk, r0⟩ => ⟨hc, hk, by rw [r0, ite_eq_right ha]⟩

/-- After the call. -/
theorem rest_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (W0 h P) (.seq (.block accSet) (.seq (.block acc0) (.seq (mgfXor h.H) (.seq (.block topSet)
      (.seq (.block topAnd) (.seq (.block scanSet) (.seq (countLoop scanBody) (.seq (.block posSet)
        (.seq (.block posChk) (.seq (.block anySet) (.ite .eq (fixedPath h.H) (anyPath h.H)))))))))))) (GE h P) :=
  VP.assoc ((acc_vp h P hP).seq (VP.assoc (VP.assoc ((unmask_vp h P hP).seq
    ((scanSet_vp h P hP).seq ((scan_vp h P hP (X := Kd h P) fun _ _ hk => hk.2.1).seq
      (VP.assoc ((pos_vp h P hP).seq ((anySet_vp h P hP).seq (tailIte_vp h P hP))))))))))

/-- The result is `verify`'s. -/
theorem fin_of (P : EP) {σ τ t : State} (hv : V2 h P σ τ) (hg : GE h P τ t) : Fin h P σ t := by
  obtain ⟨⟨hc, hi, hf, -⟩, hcr⟩ := hv
  obtain ⟨hc', hk, r0⟩ := hg
  have st : (P.lay h.D).St σ t :=
    ⟨hc.st.ok, hc'.st.sp, hc'.st.rd.trans hc.st.rd, hc'.st.wr.trans hc.st.wr, hc.st.frame.trans hc'.st.frame⟩
  refine ⟨⟨hi, st⟩, fun hpre => ?_⟩
  have hw := hcr hpre
  have hxb : Spec.Rsa.bytesAt τ.mem (State.addr (P.scr + BitVec.ofNat 32 oEm)) P.K =
      (Spec.Rsa.publicOpChecked P.nB P.eB (sigB P σ)).getD (Spec.RsaPss.zeros P.K) := by
    revert hw
    cases Spec.Rsa.publicOpChecked P.nB P.eB (sigB P σ) with
    | none => exact fun hw => hw.2
    | some y => exact fun hw => hw.2
  have hx : ∀ i < P.K, ((Spec.Rsa.publicOpChecked P.nB P.eB (sigB P σ)).getD (Spec.RsaPss.zeros P.K)).getD i 0 =
      emv P τ i := fun i hi' => by
    rw [← hxb, bytesAt_getD hi', (call_geo h hi).1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hdig : digB h P τ = digB h P σ := hc.st.ro (R := P.DIG h.D) (by simp)
  have g := good_iff h P τ hk.1 hf (bytesAt_length _ _ _) hx
  rw [hdig] at g
  rw [r0]
  by_cases e : acc2 h P τ = 0 ∧ HOk h P τ (if P.any = 0 then Mf h P τ else Ma h P τ)
  · rw [ite_eq_left e, ite_eq_left (g.1 e)]
  · rw [ite_eq_right e, ite_eq_right (fun h' => e (g.2 h'))]

/-- The body. -/
theorem body_vq (P : EP) (c : PdImpl) : VQ (S h P) (verifyBody h.H c.name c.code) (Fin h P) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VQ.of_vp (VP.empty fun σ s hs => hP ⟨σ, hs.1⟩)
  show VQ _ (.seq (.block (verifyChk h.H)) (.seq (.block (params ++ expLen ++ saltFits))
    (.ite .ne (.block [mw .r0 0]) (.seq (.block pubArgs) (.seq (.call c.name c.code) _))))) _
  refine VQ.seq (chk_vp h P) (VQ.seq (par_vp h P) (VQ.ite (fun _ _ _ _ h₁ h₂ => by
      rw [VG.Proof.X25519.Arm.eval_ne, VG.Proof.X25519.Arm.eval_ne, h₁.2.2.2.2.2.2, h₂.2.2.2.2.2.2])
    (VQ.of_vp (fail_vp h P)) ?_))
  exact VQ.seq ((pa_vp h P).mono (fun σ s ⟨h1, e⟩ => m0_of h h1 e) fun _ _ h => h)
    (VQ.seq (call_vp h P c) (VQ.reidx (rest_vp h P hP) (fun σ s hv => w0_self h hv)
      fun σ τ t hv hg => fin_of h P hv hg))

end VG.Proof.RsaPss.Arm.Vf
