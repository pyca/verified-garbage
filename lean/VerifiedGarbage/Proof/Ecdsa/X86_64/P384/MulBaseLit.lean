import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitAdx
import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Framework.LitShare

/-!
# `vg_p384_mul_base` on x86-64: the code without its displacements, as literals

As `LitErase.lean` for the signature: the constant-time checks of
`vg_p384_mul_base` and `_adx` analyse their code with its displacements and
immediates erased, each repeated block a constant (`materialize_shared`).
-/

namespace VG.Proof.Ecdsa.X86_64.P384

/-- `vg_p384_mul_base` without its displacements. -/
def mulBaseErased : Prog VG.X86_64.isa := VG.X86_64.Code.erase Impl.Ecdsa.X86_64.p384.mulBaseFn

materialize_shared mulBaseErased

/-- `vg_p384_mul_base_adx` without its displacements. -/
def mulBaseErasedAdx : Prog VG.X86_64.isa := VG.X86_64.Code.erase Impl.Ecdsa.X86_64.p384x.mulBaseFn

materialize_shared mulBaseErasedAdx

end VG.Proof.Ecdsa.X86_64.P384
