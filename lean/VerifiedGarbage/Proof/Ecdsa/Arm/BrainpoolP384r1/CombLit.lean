module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.ArmComb
import VerifiedGarbage.Proof.BrainpoolP384r1.Arm.CombLit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.ArmComb
meta import VerifiedGarbage.Proof.BrainpoolP384r1.Arm.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! Materialize brainpoolP384r1's signing, public-key and verification pipelines with the
comb for checked taint evaluation. -/

@[expose] public section
namespace VG
materialize_code Impl.Ecdsa.Arm.signBrainpoolP384r1Comb
materialize_code Impl.Ecdsa.Arm.publicKeyBrainpoolP384r1Comb
materialize_code Impl.Ecdsa.Arm.verifyBrainpoolP384r1Comb
materialize_code Impl.Ecdsa.Arm.signBrainpoolP384r1CombU
materialize_code Impl.Ecdsa.Arm.publicKeyBrainpoolP384r1CombU
materialize_code Impl.Ecdsa.Arm.verifyBrainpoolP384r1CombU
end VG
