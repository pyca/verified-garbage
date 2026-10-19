module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.P521Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P521Literals
import VerifiedGarbage.Proof.P521.X86_64.JointPartsLitAdx
meta import VerifiedGarbage.Proof.P521.X86_64.JointPartsLitAdx
public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P521.X86_64
import VerifiedGarbage.Impl.Ecdh.P521.X86_64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Impl.Ecdh.P521.X86_64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-!
# ECDSA verification over P-521 on x86-64 with BMI2 and ADX: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (`spSafe`, the ABI's checks):
the literals of the code (`materialize_code`, `Proof/Framework/Lit.lean`)
are checked once here instead (as `JointLit`), reading those of the cache
and the doubling (`JointPartsLitAdx`).
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.Verify.X86_64.jointVerifyP521Adx

end VG
