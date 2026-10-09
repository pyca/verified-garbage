import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitAdx
import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Framework.LitShare

/-!
# ECDSA over P-384 on x86-64 with BMI2 and ADX: the code without its displacements, as a literal

As `LitErase.lean`, for the code that multiplies modulo `p` with BMI2 and ADX.
-/

namespace VG.Proof.Ecdsa.X86_64.P384

/-- The code without its displacements. -/
def signErasedAdx : Prog VG.X86_64.isa := VG.X86_64.Code.erase Impl.Ecdsa.X86_64.signP384Adx

materialize_shared signErasedAdx

end VG.Proof.Ecdsa.X86_64.P384
