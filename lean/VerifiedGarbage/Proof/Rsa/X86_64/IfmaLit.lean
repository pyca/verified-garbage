module

public import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
public import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Bignum.Amm52
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
meta import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Bignum.Amm52
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSA-CRT with AVX512_IFMA on x86-64: the code as a literal

`vg_rsa_private_crt_ifma`'s vector code is unrolled, so the kernel would build
its instructions again in every check that evaluates it (`InlineOk`, the
stack depth, `spSafe`, in the registration file and the variant): the literal
of the code (`materialize_code`, `Proof/Framework/Lit.lean`) is checked once
here instead.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

materialize_code crtIfma := Impl.Rsa.X86_64.CrtIfma.code CallMont.adx.mm

end VG.Proof.Rsa.X86_64
