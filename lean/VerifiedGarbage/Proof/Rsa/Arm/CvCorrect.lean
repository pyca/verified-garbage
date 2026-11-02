module
public import VerifiedGarbage.Proof.Rsa.Arm.CvFinish

import VerifiedGarbage.Proof.Rsa.Arm.CvValid
import VerifiedGarbage.Proof.Rsa.Arm.CvSpec
import VerifiedGarbage.Proof.Framework.Sig

/-! # `vg_rsa_crt_values` on ARMv7: correctness

`cv_ok`: from a state meeting the contract's precondition, the code returns
with the callee-saved registers and `sp` restored and the results of `crtKey`
written out (`CvPost`); `cv_contract_correct` states it as the contract does.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- The results as the contract states them. -/
def CvPost (s0 t : State) : Prop :=
  abiPreserved s0 t ∧ Spec.Rsa.writtenAll t.mem
    [(State.addr (s0.gpr .r0), cvPl s0), (State.addr (s0.gpr .r2), cvQl s0),
      (State.addr (stackArg s0 0), cvPl s0)] (t.gpr .r0)
    ((Spec.Rsa.crtKey (nBytes s0) (pBytes s0) (qBytes s0) (dBytes s0)).map fun v => [v.1, v.2.1, v.2.2])

/-- The outputs of the valid branch are `crtKey`'s. -/
theorem written_valid {s0 t : State} {c : Bool} {R₂ R₃ X : Nat} (o : Outs s0 t c R₂ R₃ X)
    (e : Spec.Rsa.crtKey (nBytes s0) (pBytes s0) (qBytes s0) (dBytes s0) = if c then
      some (Spec.Rsa.i2osp (R₂ % 2 ^ (8 * cvPl s0)) (cvPl s0), Spec.Rsa.i2osp (R₃ % 2 ^ (8 * cvQl s0)) (cvQl s0),
        Spec.Rsa.i2osp (X % 2 ^ (8 * cvPl s0)) (cvPl s0)) else none) :
    Spec.Rsa.writtenAll t.mem
      [(State.addr (s0.gpr .r0), cvPl s0), (State.addr (s0.gpr .r2), cvQl s0),
        (State.addr (stackArg s0 0), cvPl s0)] (t.gpr .r0)
      ((Spec.Rsa.crtKey (nBytes s0) (pBytes s0) (qBytes s0) (dBytes s0)).map fun v => [v.1, v.2.1, v.2.2]) := by
  have r := o.ret; have dp := o.dp; have dq := o.dq; have qi := o.qi
  rw [e]
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte] at r dp dq qi ⊢
    refine ⟨r, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨dp, dq, qi⟩
  · simp only [↓reduceIte] at r dp dq qi ⊢
    refine ⟨r, ?_⟩
    simp only [List.map_cons, List.map_nil]
    rw [show Spec.Rsa.bytesAt t.mem (State.addr (s0.gpr .r0)) (cvPl s0) = outDp t.mem s0 from rfl,
      show Spec.Rsa.bytesAt t.mem (State.addr (s0.gpr .r2)) (cvQl s0) = outDq t.mem s0 from rfl,
      show Spec.Rsa.bytesAt t.mem (State.addr (stackArg s0 0)) (cvPl s0) = outQi t.mem s0 from rfl,
      dp, dq, qi]

theorem crtKey_valid {s0 : State} (pre : CvPre s0)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nBytes s0)) (cvK s0) = true)
    {X₁ X₂ V R₂ R₃ X : Nat}
    (h₁ : 0 < cvP s0 → X₁ = cvN s0 / cvP s0 ∧ X₂ = cvN s0 % cvP s0)
    (h₂ : 1 < cvM s0 → V = Nat.gcd (cvQ s0) (cvM s0) ∧ (cvM s0 : Int) ∣ (X : Int) * cvQ s0 - V ∧
      X < cvM s0)
    (h₃ : 0 < 2 * (cvP s0 / 2) → R₂ = cvD s0 % (2 * (cvP s0 / 2)))
    (h₄ : 0 < 2 * (cvQ s0 / 2) → R₃ = cvD s0 % (2 * (cvQ s0 / 2))) :
    Spec.Rsa.crtKey (nBytes s0) (pBytes s0) (qBytes s0) (dBytes s0) =
      if maskOf (cvP s0) (cvQ s0) X₁ X₂ V then
      some (Spec.Rsa.i2osp (R₂ % 2 ^ (8 * cvPl s0)) (cvPl s0), Spec.Rsa.i2osp (R₃ % 2 ^ (8 * cvQl s0)) (cvQl s0),
        Spec.Rsa.i2osp (X % 2 ^ (8 * cvPl s0)) (cvPl s0)) else none := by
  have ln : (nBytes s0).length = cvK s0 := bytesAt_length _ _ _
  have lp : (pBytes s0).length = cvPl s0 := bytesAt_length _ _ _
  have lq : (qBytes s0).length = cvQl s0 := bytesAt_length _ _ _
  have e := crtKey_masked (nb := nBytes s0) (pb := pBytes s0) (qb := qBytes s0) (db := dBytes s0)
    (by rw [ln]; exact hv) (by rw [lp, ln]; exact pre.pl2) (by rw [lq, ln]; exact pre.ql2) h₁ h₂ h₃ h₄
  rw [lp, lq] at e
  exact e

theorem crtKey_invalid {s0 : State}
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nBytes s0)) (cvK s0) = false) :
    Spec.Rsa.crtKey (nBytes s0) (pBytes s0) (qBytes s0) (dBytes s0) = none := by
  have ln : (nBytes s0).length = cvK s0 := bytesAt_length _ _ _
  unfold Spec.Rsa.crtKey
  simp only [ln, hv, Bool.false_eq_true, false_and, ↓reduceIte]

/-- What the branches leave for `restore`. -/
def CvMid (s0 t : State) : Prop := Done s0 t ∧ Spec.Rsa.writtenAll t.mem
  [(State.addr (s0.gpr .r0), cvPl s0), (State.addr (s0.gpr .r2), cvQl s0),
    (State.addr (stackArg s0 0), cvPl s0)] (t.gpr .r0)
  ((Spec.Rsa.crtKey (nBytes s0) (pBytes s0) (qBytes s0) (dBytes s0)).map fun v => [v.1, v.2.1, v.2.2])

theorem branches_ok [VG.Proof.Rsa.Arm.Keys.InvLaw] {s0 s : State} (pre : CvPre s0) (hb : Base s0 s) (p0 : s.gpr .r0 = s0.gpr .r0)
    (p3 : s.gpr .r3 = s0.gpr .r2)
    (hz : s.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nBytes s0)) (cvK s0)) :
    WP isa (.ite .eq valid fail) s (CvMid s0) := by
  refine WP.ite s.z rfl (fun hv => ?_) (fun hv => ?_)
  · refine WP.mono (valid_ok hb) fun (t : State) ⟨X₁, X₂, V, R₂, R₃, X, h₁, h₂, h₃, h₄, o⟩ => ⟨o.done, ?_⟩
    rw [hz] at hv
    exact written_valid o (crtKey_valid pre hv h₁ h₂ h₃ h₄)
  · refine WP.mono (fail_ok hb p0 p3) fun (t : State) ⟨d, r0, dp, dq, qi⟩ => ⟨d, ?_⟩
    rw [hz] at hv
    rw [crtKey_invalid hv]
    refine ⟨r0, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨dp, dq, qi⟩

theorem cv_ok [VG.Proof.Rsa.Arm.Keys.InvLaw] {s0 : State} (pre : CvPre s0) : WP isa code s0 (CvPost s0) := by
  refine WP.seq (WP.mono (entry_ok pre) fun (s : State) ⟨hb, _, p0, p3, _, hz⟩ =>
    WP.seq (WP.mono (branches_ok pre hb p0 p3 hz) fun (t : State) ⟨ht, w⟩ =>
      WP.mono (restore_ok ht) fun (u : State) ⟨hr, hsp, hm, h0⟩ => ⟨⟨hr, hsp⟩, ?_⟩))
  rw [hm, h0]; exact w

theorem cv_contract_correct [VG.Proof.Rsa.Arm.Keys.InvLaw] (s : State) (h : (Spec.Rsa.crtValuesContract abi 0).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ (Spec.Rsa.crtValuesContract abi 0).post s t := by
  obtain ⟨tr, t, run, ⟨pres, w⟩⟩ := cv_ok (cv_pre s h)
  refine ⟨tr, t, run, pres, ?_⟩
  sig_post [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact w

end VG.Proof.Rsa.Arm.CrtValues
