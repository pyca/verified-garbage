module

public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP512r1.AArch64.Joint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP512r1Literals
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP512r1.AArch64.Joint
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP512r1Literals
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! Check the unrolled code once for timing and register audits. -/

@[expose] public section
namespace VG
materialize_code Impl.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.stepFront
materialize_code Impl.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.digitTail
materialize_code Impl.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.setup
materialize_code Impl.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.verify
end VG
