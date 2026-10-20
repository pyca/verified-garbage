module

public import VerifiedGarbage.Proof.Ecdh.X86_64.P384.Lit
meta import VerifiedGarbage.Proof.Ecdh.X86_64.P384.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-!
# ECDH over P-384 on x86-64: the code without its displacements, as a literal

From a taint that knows no region bases, the analysis does not read
displacements and immediates (`Proof/Framework/X86_64/TaintErase.lean`), so
the constant-time check analyses the code with them erased. Its field
arithmetic is then the same few blocks again and again (29 distinct blocks
of 216): with each a constant (`materialize_shared`), the kernel analyses
each once from the same taint.
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86_64.P384

/-- The code without its displacements. -/
def exchangeErased : Prog VG.X86_64.isa := VG.X86_64.Code.erase Impl.Ecdh.X86_64.exchangeP384

materialize_shared exchangeErased

end VG.Proof.Ecdh.X86_64.P384
