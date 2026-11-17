module

public import VerifiedGarbage.Impl.Ecdsa.P192.ArmComb
import VerifiedGarbage.Proof.P192.Arm.CombLit
meta import VerifiedGarbage.Impl.Ecdsa.P192.ArmComb
meta import VerifiedGarbage.Proof.P192.Arm.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! Materialize P-192's signing, public-key and verification pipelines with the
comb for checked taint evaluation. -/

@[expose] public section
namespace VG
materialize_code Impl.Ecdsa.Arm.signP192Comb
materialize_code Impl.Ecdsa.Arm.publicKeyP192Comb
materialize_code Impl.Ecdsa.Arm.verifyP192Comb
materialize_code Impl.Ecdsa.Arm.signP192CombU
materialize_code Impl.Ecdsa.Arm.publicKeyP192CombU
materialize_code Impl.Ecdsa.Arm.verifyP192CombU
end VG
