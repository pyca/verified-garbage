module
public import VerifiedGarbage.Proof.RsaPss.Arm.VfAny
public import VerifiedGarbage.Proof.RsaPss.Arm.VfFixed

import VerifiedGarbage.Proof.RsaPss.Arm.VfLogic
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the body

After the call, over the state `τ` it leaves (`rest_vp`): `acc`, the
unmasking (MGF1 through the table `mgf1`), the scan, and the path for the expected salt length; then the
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
theorem tailIte_vp {g : RsaOaep.Arm.OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP)
    (Q : TF h g f fg dn P) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => ((Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem) ∧ s.z = decide (P.any = 0)) ∧ s.syms = τ.syms)
      (.ite .eq (fixedPath f h.sh) (anyPath f h.sh)) (fun τ s => GE h P τ s ∧ s.syms = τ.syms) := by
  refine VP.ite (fun _ _ _ _ h₁ h₂ => by
    rw [VG.Proof.X25519.Arm.eval_eq, VG.Proof.X25519.Arm.eval_eq, h₁.1.2, h₂.1.2]) ?_ ?_
  · by_cases ha : P.any = 0
    · exact (fixed_vp h P Q hP).mono (fun τ s ⟨⟨⟨⟨hc, hk⟩, _⟩, sy⟩, _⟩ => ⟨⟨hc, hk, ha⟩, sy⟩)
        fun τ s ⟨⟨hc, hk, r0⟩, sy⟩ => ⟨⟨hc, hk, by rw [r0, ite_eq_left ha]⟩, sy⟩
    · exact VP.empty fun τ s ⟨⟨⟨_, z⟩, _⟩, e⟩ => by
        rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_false ha] at e; exact absurd e (by decide)
  · by_cases ha : P.any = 0
    · exact VP.empty fun τ s ⟨⟨⟨_, z⟩, _⟩, e⟩ => by
        rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_true ha] at e; exact absurd e (by decide)
    · exact (any_vp h P Q hP).mono (fun τ s ⟨⟨⟨⟨hc, hk⟩, _⟩, sy⟩, _⟩ => ⟨⟨hc, hk, trivial⟩, sy⟩)
        fun τ s ⟨⟨hc, hk, r0⟩, sy⟩ => ⟨⟨hc, hk, by rw [r0, ite_eq_right ha]⟩, sy⟩

/-- After the call. -/
theorem rest_vp {g : RsaOaep.Arm.OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP)
    (Q : TF h g f fg dn P) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => W0 h P τ s ∧ s.syms = τ.syms) (.seq (.block accSet) (.seq (.block acc0) (.seq (mgfPart fg h.sh 15)
      (.seq (.block topSet) (.seq (.block topAnd) (.seq (.block scanSet) (.seq (countLoop scanBody)
        (.seq (.block posSet) (.seq (.block posChk) (.seq (.block anySet)
          (.ite .eq (fixedPath f h.sh) (anyPath f h.sh))))))))))))
      (fun τ s => GE h P τ s ∧ s.syms = τ.syms) :=
  VP.assoc ((VP.syms (acc_vp h P hP)).seq ((vmask_vp h P Q hP).seq (VP.assoc ((VP.syms (vtop_vp h P hP)).seq
    ((VP.syms (scanSet_vp h P hP)).seq ((VP.syms (scan_vp h P hP (X := Kd h P) fun _ _ hk => hk.2.1)).seq
      (VP.assoc ((VP.syms (pos_vp h P hP)).seq ((VP.syms (anySet_vp h P hP)).seq (tailIte_vp h P Q hP))))))))))

/-- The result is `verify`'s. -/
theorem fin_of (P : EP) (hGv : Proof.Mgf1.Valid P.G) {σ τ t : State} (hv : V2 h P σ τ) (hg : GE h P τ t) :
    Fin h P.G P σ t := by
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
  have g := good_iff h P hGv τ hk.1 hf (bytesAt_length _ _ _) hx
  rw [hdig] at g
  rw [r0]
  by_cases e : acc2 h P τ = 0 ∧ HOk h P τ (if P.any = 0 then Mf h P τ else Ma h P τ)
  · rw [ite_eq_left e, ite_eq_left (g.1 e)]
  · rw [ite_eq_right e, ite_eq_right (fun h' => e (g.2 h'))]

/-- The body. -/
theorem body_vq {g : RsaOaep.Arm.OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP)
    (Q : TF h g f fg dn P) (c : PdImpl) :
    VQ (fun σ s => S h P σ s ∧ s.syms = σ.syms) (verifyBody f fg h.sh c.name c.code) (Fin h P.G P) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VQ.of_vp (VP.empty fun σ s hs => hP ⟨σ, hs.1.1⟩)
  have hGv : Proof.Mgf1.Valid P.G := Q.gG ▸ g.valid
  show VQ _ (.seq (.block (verifyChk h.sh)) (.seq (.block (params ++ expLen ++ saltFits))
    (.ite .ne (.block [mw .r0 0]) (.seq (.block pubArgs) (.seq (.call c.name c.code) _))))) _
  refine VQ.seq (VP.syms (chk_vp h P)) (VQ.seq (VP.syms (par_vp h P)) (VQ.ite (fun _ _ _ _ h₁ h₂ => by
      rw [VG.Proof.X25519.Arm.eval_ne, VG.Proof.X25519.Arm.eval_ne, h₁.1.2.2.2.2.2.2, h₂.1.2.2.2.2.2.2])
    (VQ.of_vp ((VP.syms (fail_vp h P.G P)).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x.1)) ?_))
  exact VQ.seq ((VP.syms (pa_vp h P)).mono (fun σ s ⟨⟨h1, sy⟩, e⟩ => ⟨m0_of h h1 e, sy⟩) fun _ _ h => h)
    (VQ.seq (VP.syms (call_vp h P c)) (VQ.reidx (rest_vp h P Q hP) (fun σ s ⟨hv, sy⟩ => ⟨w0_self h Q hv sy, rfl⟩)
      fun σ τ t ⟨hv, _⟩ hg => fin_of h P hGv hv hg.1))

end VG.Proof.RsaPss.Arm.Vf
