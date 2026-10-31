module

public import VerifiedGarbage.Impl.Ecdsa.P384.ArmComb
import VerifiedGarbage.Proof.P384.Arm.CombLit
meta import VerifiedGarbage.Impl.Ecdsa.P384.ArmComb
meta import VerifiedGarbage.Proof.P384.Arm.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! Materialize P-384's signing, public-key and verification pipelines with the
comb for checked taint evaluation. -/

@[expose] public section
namespace VG
materialize_code Impl.Ecdsa.Arm.signP384Comb
materialize_code Impl.Ecdsa.Arm.publicKeyP384Comb
materialize_code Impl.Ecdsa.Arm.verifyP384Comb
materialize_code Impl.Ecdsa.Arm.signP384CombU
materialize_code Impl.Ecdsa.Arm.publicKeyP384CombU
materialize_code Impl.Ecdsa.Arm.verifyP384CombU
end VG
