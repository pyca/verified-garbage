module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.ArmComb
import VerifiedGarbage.Proof.BrainpoolP512r1.Arm.CombLit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.ArmComb
meta import VerifiedGarbage.Proof.BrainpoolP512r1.Arm.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! Materialize brainpoolP512r1's signing, public-key and verification pipelines with the
comb for checked taint evaluation. -/

@[expose] public section
namespace VG
materialize_code Impl.Ecdsa.Arm.signBrainpoolP512r1Comb
materialize_code Impl.Ecdsa.Arm.publicKeyBrainpoolP512r1Comb
materialize_code Impl.Ecdsa.Arm.verifyBrainpoolP512r1Comb
materialize_code Impl.Ecdsa.Arm.signBrainpoolP512r1CombU
materialize_code Impl.Ecdsa.Arm.publicKeyBrainpoolP512r1CombU
materialize_code Impl.Ecdsa.Arm.verifyBrainpoolP512r1CombU
end VG
