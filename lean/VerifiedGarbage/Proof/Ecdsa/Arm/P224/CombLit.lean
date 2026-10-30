module

public import VerifiedGarbage.Impl.Ecdsa.P224.ArmComb
import VerifiedGarbage.Proof.P224.Arm.CombLit
meta import VerifiedGarbage.Impl.Ecdsa.P224.ArmComb
meta import VerifiedGarbage.Proof.P224.Arm.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! Materialize P-224's signing, public-key and verification pipelines with the
comb for checked taint evaluation. -/

@[expose] public section
namespace VG
materialize_code Impl.Ecdsa.Arm.signP224Comb
materialize_code Impl.Ecdsa.Arm.publicKeyP224Comb
materialize_code Impl.Ecdsa.Arm.verifyP224Comb
end VG
