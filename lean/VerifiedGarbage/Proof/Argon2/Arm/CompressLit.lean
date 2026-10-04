import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Argon2.Arm.Compress

/-!
# Argon2 compression on ARMv7: the code as a literal

The compression function is fully unrolled: its literal (`materialize_code`)
spares the kernel building the instructions in every check that evaluates
the code (constant time, `spSafe`), and its callers call it.
-/

namespace VG.Impl.Argon2.Arm

materialize_code compress

end VG.Impl.Argon2.Arm
