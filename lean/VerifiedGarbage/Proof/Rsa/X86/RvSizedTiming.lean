module
public import VerifiedGarbage.Proof.Rsa.X86.RvPair
public import VerifiedGarbage.Proof.Rsa.X86.RvResult

import VerifiedGarbage.Proof.Rsa.X86.RvNumbersTiming
import VerifiedGarbage.Proof.Rsa.X86.RvRestTiming
import VerifiedGarbage.Proof.Rsa.X86.RvFailureTiming
import VerifiedGarbage.Proof.Rsa.X86.RvPublicFacts
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Both sized-recovery branches obey the declared timing contract -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Recover
open VG.Spec.Rsa (recoverPrimes)

def SizedPair (g : CallGeometry) (s t : State) : Prop :=
  Pair g s t ∧ inputValue g s.mem 0 = inputValue g t.mem 0 ∧
  Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length = true ∧
  Spec.Rsa.modulusValid (inputValue g t.mem 0) (inputBytes g t.mem 0).length = true ∧
  (calculated g s.mem).2 = (calculated g t.mem).2

theorem sized_relCT (g : CallGeometry) : RelCT isa (SizedPair g) (sized g.n) (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨pair, modulus, vs, vt, attempts⟩ es et
  have tries : (recoverPrimes (inputValue g s.mem 0) (inputValue g s.mem 1) (inputValue g s.mem 2)).2 =
      (recoverPrimes (inputValue g t.mem 0) (inputValue g t.mem 1) (inputValue g t.mem 2)).2 := by
    rw [← calculated_tries_valid vs, ← calculated_tries_valid vt]
    exact attempts
  have sameGo : decide (GoOn (product g s.mem)) = decide (GoOn (product g t.mem)) := by
    have ls := recover_tries_positive (inputValue g s.mem 0) (inputValue g s.mem 1) (inputValue g s.mem 2)
    have lt := recover_tries_positive (inputValue g t.mem 0) (inputValue g t.mem 1) (inputValue g t.mem 2)
    rw [tries] at ls
    apply decide_eq_decide.mpr
    exact ls.symm.trans lt
  obtain ⟨bs, os, gs⟩ := pair.left.modulusFacts vs
  obtain ⟨bt, ot, gt⟩ := pair.right.modulusFacts vt
  cases es with
  | @seq _ _ _ u _ _ _ e1 er =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 fr =>
      have eq1 := (numbers_relCT g _ _ _ _ _ _ pair e1 f1).1
      obtain ⟨cs, zs⟩ := wp_result (numbers_ok pair.left) e1
      obtain ⟨ct, zt⟩ := wp_result (numbers_ok pair.right) f1
      have flag : isa.eval .e u = isa.eval .e v := by change u.zf = v.zf; rw [zs, zt, sameGo]
      cases er with
      | iteT condS es =>
        cases fr with
        | iteT condT et =>
          have goS : GoOn (product g s.mem) := of_decide_eq_true (Option.some.inj (zs.symm.trans condS))
          have goT : GoOn (product g t.mem) := of_decide_eq_true (Option.some.inj (zt.symm.trans condT))
          have eq2 := (rest_relCT g s t pair.left pair.right pair.sp goS goT bs bt os ot gs gt
            modulus tries _ _ _ _ _ _ ⟨cs, ct⟩ es et).1
          exact ⟨by rw [eq1, eq2], trivial⟩
        | iteF condT _ => rw [flag, condT] at condS; cases condS
      | iteF condS es =>
        cases fr with
        | iteT condT _ => rw [flag, condT] at condS; cases condS
        | iteF _ et =>
          have next : Pair g u v := ⟨pair.left.of_KS cs, pair.right.of_KS ct,
            (cs.rest.1 _ (by decide)).trans (pair.sp.trans (ct.rest.1 _ (by decide)).symm)⟩
          have eq2 := (failure_relCT g _ _ _ _ _ _ next es et).1
          exact ⟨by rw [eq1, eq2], trivial⟩

end VG.Proof.Rsa.X86.Recover
