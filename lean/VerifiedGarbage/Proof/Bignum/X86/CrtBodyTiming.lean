module
public import VerifiedGarbage.Impl.Bignum.X86.CrtFn
public import VerifiedGarbage.Spec.Rsa.Contract
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Bignum.X86.CrtPair
public import VerifiedGarbage.Spec.Weierstrass.Point

import VerifiedGarbage.Proof.Bignum.X86.CrtModulusTiming
import VerifiedGarbage.Proof.Bignum.X86.CrtFailureTiming
import VerifiedGarbage.Proof.Bignum.X86.CrtValidTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Words

/-! # Private RSA branches only on the public modulus -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem body_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (fun s t => Pair base bytes len args s t ∧
      Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len = Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) len)
      Crt.body (fun _ _ => True) := by
  let R := fun s t => Pair base bytes len args s t ∧ ∃ b : Bool, s.zf = some b ∧ t.zf = some b
  have Branch : RelCT isa R (.ite .e Crt.valid PublicFn.failure) (fun _ _ => True) := by
    apply VG.RelCT.ite (M := isa) (c := .e) (P := R)
    · intro s t ⟨_, b, Zs, Zt⟩
      exact Zs.trans Zt.symm
    · exact (valid_relCT base bytes len args).mono (fun _ _ H => H.1.1) (fun _ _ h => h)
    · exact (failure_relCT base bytes len args).mono (fun _ _ H => H.1.1) (fun _ _ h => h)
  apply VG.RelCT.assoc
  intro s t tr ur sf tf ⟨H, N⟩ E F
  cases E with
  | @seq _ _ _ u _ _ _ E1 E2 =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 F2 =>
      have T1 := (modulus_relCT base bytes len args _ _ _ _ _ _ H E1 F1).1
      obtain ⟨Zs, Ms, Ks⟩ := wp_result (modulus_ok H.left) E1
      obtain ⟨Zt, Mt, Kt⟩ := wp_result (modulus_ok H.right) F1
      have Next := H.keep Ks Kt (by decide) (by decide)
        (by rw [Ms]; exact Outside.refl _ _ _ _) (by rw [Mt]; exact Outside.refl _ _ _ _)
      have Relation : R u v := ⟨Next, _, Zs, by rw [N]; exact Zt⟩
      have T2 := (Branch _ _ _ _ _ _ Relation E2 F2).1
      exact ⟨by rw [T1, T2], trivial⟩

end VG.Proof.Bignum.X86.Crt
