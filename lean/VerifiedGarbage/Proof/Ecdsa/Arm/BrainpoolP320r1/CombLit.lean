module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.ArmComb
import VerifiedGarbage.Proof.BrainpoolP320r1.Arm.CombLit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.ArmComb
meta import VerifiedGarbage.Proof.BrainpoolP320r1.Arm.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! Materialize brainpoolP320r1's signing, public-key and verification pipelines with the
comb for checked taint evaluation. -/

@[expose] public section
namespace VG
materialize_code Impl.Ecdsa.Arm.signBrainpoolP320r1Comb
materialize_code Impl.Ecdsa.Arm.publicKeyBrainpoolP320r1Comb
materialize_code Impl.Ecdsa.Arm.verifyBrainpoolP320r1Comb
materialize_code Impl.Ecdsa.Arm.signBrainpoolP320r1CombU
materialize_code Impl.Ecdsa.Arm.publicKeyBrainpoolP320r1CombU
materialize_code Impl.Ecdsa.Arm.verifyBrainpoolP320r1CombU
end VG
