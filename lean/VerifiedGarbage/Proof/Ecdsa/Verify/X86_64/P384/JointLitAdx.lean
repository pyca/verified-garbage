import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.VerifyLit
import VerifiedGarbage.Proof.P384.X86_64.JointPartsLitAdx
import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86_64

/-!
# ECDSA verification over P-384 on x86-64 with BMI2 and ADX: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (`spSafe`, the ABI's checks):
the literals of the code (`materialize_code`, `Proof/Framework/Lit.lean`)
are checked once here instead (as `JointLit`), reading those of the cache
and the doubling (`JointPartsLitAdx`).
-/

namespace VG

materialize_code Impl.Ecdsa.Verify.X86_64.jointVerifyP384Adx

end VG
