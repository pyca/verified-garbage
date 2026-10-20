module

import VerifiedGarbage.Proof.Weierstrass.X86_64.P521Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P521Literals
public import VerifiedGarbage.Impl.Ecdsa.P521.X86_64
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Ecdsa.P521.X86_64
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
# ECDSA over P-521 on x86-64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, `spSafe`): the
literal of the code (`materialize_code`, `Proof/Framework/Lit.lean`) is
checked once here instead.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.X86_64.signP521

end VG
