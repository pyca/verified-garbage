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

namespace Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint VG.Proof.Weierstrass.AArch64

/-- The literals of `BrainpoolP512r1Literals`, under the terms the verification's code
has: `cfg` is an abbreviation, and `materialize_code` finds a literal by its
term. -/
private noncomputable abbrev validateCode.lit := BrainpoolP512r1Literals.validate.lit
private theorem validateCode.lit_eq : Impl.Ecdh.AArch64.Cfg.validate cfg = validateCode.lit :=
  BrainpoolP512r1Literals.validate.lit_eq
private noncomputable abbrev nPowCode.lit := BrainpoolP512r1Literals.nPow.lit
private theorem nPowCode.lit_eq : cfg.nPow = nPowCode.lit := BrainpoolP512r1Literals.nPow.lit_eq

end Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint

materialize_code Impl.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.verify
end VG
