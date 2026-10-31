module

public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.ArmComb
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.ArmComb
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! Materialize the shared signing and public-key pipelines for checked taint evaluation. -/

@[expose] public section
namespace VG
materialize_code Impl.Ecdsa.Arm.signSecp256k1Comb
materialize_code Impl.Ecdsa.Arm.publicKeySecp256k1Comb
materialize_code Impl.Ecdsa.Arm.signSecp256k1CombU
materialize_code Impl.Ecdsa.Arm.publicKeySecp256k1CombU
end VG
