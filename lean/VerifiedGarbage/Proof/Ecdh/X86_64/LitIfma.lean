module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
public import VerifiedGarbage.Impl.Ecdh.P256.X86_64.Ifma
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
meta import VerifiedGarbage.Impl.Ecdh.P256.X86_64.Ifma
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# ECDH over P-256 on x86-64 with AVX512_IFMA: the code as a literal

As `Lit.lean`, for the code whose window method's loop is in vectors.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdh.X86_64.exchangeP256Ifma

end VG
