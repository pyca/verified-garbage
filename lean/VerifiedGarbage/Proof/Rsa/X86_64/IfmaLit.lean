import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Rsa.X86_64.Calls

/-!
# RSA-CRT with AVX512_IFMA on x86-64: the code as a literal

`vg_rsa_private_crt_ifma`'s vector code is unrolled, so the kernel would build
its instructions again in every check that evaluates it (`InlineOk`, the
stack depth, `spSafe`, in the registration file and the variant): the literal
of the code (`materialize_code`, `Proof/Framework/Lit.lean`) is checked once
here instead.
-/

namespace VG.Proof.Rsa.X86_64

materialize_code crtIfma := Impl.Rsa.X86_64.CrtIfma.code CallMont.adx.mm

end VG.Proof.Rsa.X86_64
