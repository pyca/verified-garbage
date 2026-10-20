module

public import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP384r1
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP384r1
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.X86
meta import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.X86
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-!
# ECDSA verification over brainpoolP384r1 on x86 (32-bit): the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, properties of
every instruction): the literal of the code (`materialize_code`,
`Proof/Framework/Lit.lean`) is checked once here instead.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.Verify.X86.verifyBrainpoolP384r1

end VG
