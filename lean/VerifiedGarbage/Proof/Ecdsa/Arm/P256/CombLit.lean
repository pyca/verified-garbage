module

public import VerifiedGarbage.Impl.Ecdsa.P256.ArmComb
import VerifiedGarbage.Proof.P256.Arm.CombLit
meta import VerifiedGarbage.Impl.Ecdsa.P256.ArmComb
meta import VerifiedGarbage.Proof.P256.Arm.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! Materialize P-256's signing, public-key and verification pipelines with the
comb for checked taint evaluation. -/

@[expose] public section
namespace VG
materialize_code Impl.Ecdsa.Arm.signP256Comb
materialize_code Impl.Ecdsa.Arm.publicKeyP256Comb
materialize_code Impl.Ecdsa.Arm.verifyP256Comb
end VG
