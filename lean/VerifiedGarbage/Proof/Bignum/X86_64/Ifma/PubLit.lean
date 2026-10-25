module

public import VerifiedGarbage.Impl.Rsa.X86_64.PubIfma
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Impl.Rsa.X86_64.PubIfma
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# The precomputed public operation with AVX512_IFMA: the code as a literal

`vg_rsa_public_precomputed_checked_ifma`'s vector code is unrolled, so the
kernel would build its instructions again in every check that evaluates it
(the variant's stack checks, `spSafe` in the registration file): the literal
of the code (`materialize_code`, `Proof/Framework/Lit.lean`) is checked once
here instead.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma.Pub

-- The vector code of each size, which its constant-time check (`pubT`)
-- evaluates too.
materialize_code exp2048 := Impl.Rsa.X86_64.PubIfma.exp65537 Impl.Rsa.X86_64.PubIfma.pay2048
materialize_code exp3072 := Impl.Rsa.X86_64.PubIfma.exp65537 Impl.Rsa.X86_64.PubIfma.pay3072
materialize_code exp4096 := Impl.Rsa.X86_64.PubIfma.exp65537 Impl.Rsa.X86_64.PubIfma.pay4096

materialize_code pubIfma := Impl.Rsa.X86_64.PubIfma.checked Mont.adxSquare.mm

end VG.Proof.Bignum.X86_64.Ifma.Pub
