module

import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Templates
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Templates
public import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64
import VerifiedGarbage.Impl.Ecdh.P256.X86_64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Impl.Ecdh.P256.X86_64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-!
# ECDSA verification over P-256 on x86-64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, `spSafe`): the
literal of the code (`materialize_code`, `Proof/Framework/Lit.lean`) is
checked once here instead.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.Verify.X86_64.verifyP256

end VG
