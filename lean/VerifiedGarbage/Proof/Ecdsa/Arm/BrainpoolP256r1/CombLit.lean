module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.ArmComb
import VerifiedGarbage.Proof.BrainpoolP256r1.Arm.CombLit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.ArmComb
meta import VerifiedGarbage.Proof.BrainpoolP256r1.Arm.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! Materialize brainpoolP256r1's signing, public-key and verification pipelines with the
comb for checked taint evaluation. -/

@[expose] public section
namespace VG
materialize_code Impl.Ecdsa.Arm.signBrainpoolP256r1Comb
materialize_code Impl.Ecdsa.Arm.publicKeyBrainpoolP256r1Comb
materialize_code Impl.Ecdsa.Arm.verifyBrainpoolP256r1Comb
materialize_code Impl.Ecdsa.Arm.signBrainpoolP256r1CombU
materialize_code Impl.Ecdsa.Arm.publicKeyBrainpoolP256r1CombU
materialize_code Impl.Ecdsa.Arm.verifyBrainpoolP256r1CombU
end VG
