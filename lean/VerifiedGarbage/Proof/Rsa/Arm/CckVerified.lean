module

public import VerifiedGarbage.Proof.Rsa.Arm.KcFnCT
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
public import VerifiedGarbage.Proof.Rsa.Contract
meta import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Impl.Rsa.Arm.KeyCheck
public import VerifiedGarbage.Proof.Rsa.Arm.KcFn
import VerifiedGarbage.Impl.Rsa.Arm.KeyCheck
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-! # `vg_rsa_check_crt_key` on ARMv7 is verified against the shared RSA contract -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CheckCrtKey
open VG VG.Arm VG.Proof.Rsa.Arm.KeyCheck VG.Impl.Rsa.Arm.KeyCheck

/-- Two runs that agree on `n`, `e`, the pointers and the lengths. -/
theorem pubF_of {s t : State} (sp : s.sp = t.sp)
    (bytes : (Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat ++
        Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (s.gpr .r2)) (s.gpr .r3).toNat).map (·.toNat) =
      (Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (t.gpr .r0)) (t.gpr .r1).toNat ++
        Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (t.gpr .r2)) (t.gpr .r3).toNat).map (·.toNat))
    (p0 : s.gpr .r0 = t.gpr .r0) (p1 : s.gpr .r1 = t.gpr .r1) (p2 : s.gpr .r2 = t.gpr .r2)
    (p3 : s.gpr .r3 = t.gpr .r3) {nA : Nat} (args : ∀ i < nA, stackArg s i = stackArg t i) : PubF nA s t := by
  have b := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 bytes
  obtain ⟨hn, he⟩ := List.append_inj b (by
    rw [VG.Proof.Rsa.Arm.CrtValues.bytesAt_length, VG.Proof.Rsa.Arm.CrtValues.bytesAt_length, p1])
  exact ⟨sp, hn, he, p0, p1, p2, p3, args⟩

end VG.Proof.Rsa.Arm.CheckCrtKey
