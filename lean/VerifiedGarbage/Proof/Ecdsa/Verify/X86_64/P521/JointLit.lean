module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.P521Literals
import VerifiedGarbage.Proof.P521.X86_64.JointPartsLit
public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.X86_64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P521Literals
meta import VerifiedGarbage.Proof.P521.X86_64.JointPartsLit
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P521.X86_64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# ECDSA verification over P-521 on x86-64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (`spSafe`, the ABI's checks):
the literals of the code (`materialize_code`, `Proof/Framework/Lit.lean`)
are checked once here instead (with BMI2 and ADX: `JointLitAdx`, in
parallel), reading those of the cache and the doubling (`JointPartsLit`).
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.Verify.X86_64.jointVerifyP521

end VG
