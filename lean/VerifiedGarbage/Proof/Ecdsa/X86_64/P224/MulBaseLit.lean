import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Lit
import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Framework.LitShare

/-!
# `vg_p224_mul_base` on x86-64: the code without its displacements, as literals

As `LitErase.lean` for the signature: the constant-time checks of
`vg_p224_mul_base` analyses its code with its displacements and
immediates erased, each repeated block a constant (`materialize_shared`).
-/

namespace VG.Proof.Ecdsa.X86_64.P224

/-- `vg_p224_mul_base` without its displacements. -/
def mulBaseErased : Prog VG.X86_64.isa := VG.X86_64.Code.erase Impl.Ecdsa.X86_64.p224.mulBaseFn

materialize_shared mulBaseErased

end VG.Proof.Ecdsa.X86_64.P224
