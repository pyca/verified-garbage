module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Fn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Implies
import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Correct
import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.CT
public import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_ffdh_check_private` on PPC64LE: verified against the shared contract

With correctness (`kp_correct`), constant time (`kp_ct`) and the shared
contract (`kp_implies`), `checkPrivate` is verified (`kp_verified`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.CheckPrivate

open VG VG.PPC64LE VG.Impl.Ffdh.PPC64LE.CheckPrivate

/-- `vg_ffdh_check_private`. -/
theorem kp_verified : Verified target checkPrivate (Spec.Ffdh.checkPrivateContract abi) :=
  Verified.of_correct kp_correct kp_ct kp_implies

end VG.Proof.Ffdh.PPC64LE.CheckPrivate
