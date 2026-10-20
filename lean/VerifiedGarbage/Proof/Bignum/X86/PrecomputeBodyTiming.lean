module
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputePair
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Bignum.X86.PrecomputeModulusTiming
import VerifiedGarbage.Proof.Bignum.X86.PrecomputeValidTiming
import VerifiedGarbage.Proof.Bignum.X86.PrecomputeFailureTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Words

/-! # Checked public RSA branches only on public key validation -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem precomputeBody_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (fun s t => PrecomputePair base bytes len args s t ∧
      Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len = Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) len)
      PrecomputeFn.body (fun _ _ => True) := by
  let R := fun s t => PrecomputePair base bytes len args s t ∧
    ∃ b : Bool, s.zf = some b ∧ t.zf = some b ∧ (b = true → PrecomputeValidPair base bytes len args s t)
  have Branch : RelCT isa R (.ite .e PrecomputeFn.valid PrecomputeFn.failure) (fun _ _ => True) := by
    apply VG.RelCT.ite (M := isa) (c := .e) (P := R)
    · intro s t ⟨_, b, Zs, Zt, _⟩
      exact Zs.trans Zt.symm
    · intro s t tr ur sf tf ⟨H, Z⟩ E F
      obtain ⟨b, Zs, _, Valid⟩ := H.2
      have B : b = true := by
        change s.zf = some true at Z
        exact Option.some.inj (Zs.symm.trans Z)
      exact ⟨(precomputeValid_relCT base bytes len args _ _ _ _ _ _ (Valid B) E F).1, trivial⟩
    · exact (precomputeFailure_relCT base bytes len args).mono (fun _ _ H => H.1.1) (fun _ _ h => h)
  apply VG.RelCT.assoc
  intro s t tr ur sf tf ⟨H, N⟩ E F
  cases E with
  | @seq _ _ _ u _ _ _ E1 E2 =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 F2 =>
      have T1 := (precomputeModulus_relCT base bytes len args _ _ _ _ _ _ H E1 F1).1
      obtain ⟨Zs, Ms, Ks⟩ := wp_result (precomputeModulus_ok H.left) E1
      obtain ⟨Zt, Mt, Kt⟩ := wp_result (precomputeModulus_ok H.right) F1
      have Next := H.keep Ks Kt (by decide) (by decide)
        (by rw [Ms]; exact Outside.refl _ _ _ _) (by rw [Mt]; exact Outside.refl _ _ _ _)
      have Relation : R u v := by
        refine ⟨Next, _, Zs, ?_, ?_⟩
        · rw [N]; exact Zt
        · intro V
          refine ⟨Next, ?_, ?_⟩
          · rw [Ms]; exact V
          · rw [Mt, ← N]; exact V
      have T2 := (Branch _ _ _ _ _ _ Relation E2 F2).1
      exact ⟨by rw [T1, T2], trivial⟩

end VG.Proof.Bignum.X86
