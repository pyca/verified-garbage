import VerifiedGarbage.Proof.Ecdsa.X86_64.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.LitAdx
import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Framework.LitShare

/-!
# `vg_p256_mul_base_adx` on x86-64: the code without its displacements, as a literal

As `LitErase.lean` for the signature: the constant-time checks of
`vg_p256_mul_base_adx` analyses its code with its displacements and
immediates erased, each repeated block a constant (`materialize_shared`).
-/

namespace VG.Proof.Ecdsa.X86_64.P256

/-- `vg_p256_mul_base_adx` without its displacements. -/
def mulBaseErasedAdx : Prog VG.X86_64.isa := VG.X86_64.Code.erase Impl.Ecdsa.X86_64.p256x.mulBaseFn

materialize_shared mulBaseErasedAdx

end VG.Proof.Ecdsa.X86_64.P256
