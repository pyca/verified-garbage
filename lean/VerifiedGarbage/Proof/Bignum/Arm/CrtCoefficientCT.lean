module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtCoefficient
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtDifferenceCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtTimesInverseCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! # Complete CRT coefficient computation hides all private data -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt
open VG.Spec.Rsa.Mont (arrAt)

theorem crt_coefficient_ct {base src : BitVec 32} {len w k M1 M2 : Nat} {bs1 bs2 : List Byte}
    (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => CrtCoefficientInput base src len w k M1 bs1 s ∧
      CrtCoefficientInput base src len w k M2 bs2 t ∧ s.sp = t.sp) coefficient (fun _ _ => True) := by
  let P := fun (s t : State) => CrtCoefficientInput base src len w k M1 bs1 s ∧
    CrtCoefficientInput base src len w k M2 bs2 t ∧ s.sp = t.sp
  have diff : RelCT isa P difference (fun _ _ => True) :=
    (crt_difference_ct fit).mono (fun _ _ h => ⟨h.1.difference, h.2.1.difference, h.2.2⟩) (fun _ _ _ => trivial)
  have ready := (relCT_keep_sp diff (fun _ _ h => h.2.2)).wp (fun s t h =>
    ⟨(crt_coefficientDifference_ready s h.1).mono (fun _ j => j.1),
      (crt_coefficientDifference_ready t h.2.1).mono (fun _ j => j.1)⟩)
  exact ready.seq ((crt_timesInverse_ct fit).mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
