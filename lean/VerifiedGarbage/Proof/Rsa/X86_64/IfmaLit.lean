module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Rsa.X86_64.Calls
meta import VerifiedGarbage.Proof.Rsa.X86_64.Calls
public import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTMain
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTMain
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCode
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTLoop
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT1
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTLoop
meta import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCT1

/-!
# RSA-CRT with AVX512_IFMA on x86-64: the code as a literal

`vg_rsa_private_crt_ifma`'s vector code (and `vg_rsa_private_crt_precomputed_ifma`'s) is unrolled, so the kernel would build
its instructions again in every check that evaluates it (`InlineOk`, the
stack depth, `spSafe`, in the registration file and the variant): the literal
of the code (`materialize_code`, `Proof/Framework/Lit.lean`) is checked once
here instead.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

materialize_code crtIfma := Impl.Rsa.X86_64.CrtIfma.code CallMont.adx.mm
materialize_code crtIfmaPc := Impl.Rsa.X86_64.CrtIfma.code CallMont.adx.mm true

end VG.Proof.Rsa.X86_64
