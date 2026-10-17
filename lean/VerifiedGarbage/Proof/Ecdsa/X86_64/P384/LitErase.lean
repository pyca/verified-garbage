module

public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Lit
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleCms
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleCms

/-!
# ECDSA over P-384 on x86-64: the code without its displacements, as a literal

From a taint that knows no region bases, the analysis does not read
displacements and immediates (`Proof/Framework/X86_64/TaintErase.lean`), so
the constant-time check analyses the code with them erased. Its field
arithmetic is then the same few blocks again and again: with each a constant
(`materialize_shared`), the kernel analyses each once from the same taint.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.P384

/-- The code without its displacements. -/
def signErased : Prog VG.X86_64.isa := VG.X86_64.Code.erase Impl.Ecdsa.X86_64.signP384

materialize_shared signErased

end VG.Proof.Ecdsa.X86_64.P384
