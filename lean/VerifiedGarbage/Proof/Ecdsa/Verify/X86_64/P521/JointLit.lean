import VerifiedGarbage.Proof.Weierstrass.X86_64.P521Literals
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P521.X86_64

/-!
# ECDSA verification over P-521 on x86-64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (`spSafe`, the ABI's checks):
the literals of the code (`materialize_code`, `Proof/Framework/Lit.lean`)
are checked once here instead.
-/

namespace VG

materialize_code Impl.Ecdsa.Verify.X86_64.jointVerifyP521
materialize_code Impl.Ecdsa.Verify.X86_64.jointVerifyP521Adx

end VG
