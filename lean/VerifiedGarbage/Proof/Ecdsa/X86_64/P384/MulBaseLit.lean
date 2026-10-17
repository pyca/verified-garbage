module

public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Lit
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitAdx
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitAdx
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Weierstrass.X86_64.P384Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P384Literals

/-!
# `vg_p384_mul_base` on x86-64: the code without its displacements, as literals

As `LitErase.lean` for the signature: the constant-time checks of
`vg_p384_mul_base` and `_adx` analyse their code with its displacements and
immediates erased, each repeated block a constant (`materialize_shared`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.P384

/-- `vg_p384_mul_base` without its displacements. -/
def mulBaseErased : Prog VG.X86_64.isa := VG.X86_64.Code.erase Impl.Ecdsa.X86_64.p384.mulBaseFn

materialize_shared mulBaseErased

/-- `vg_p384_mul_base_adx` without its displacements. -/
def mulBaseErasedAdx : Prog VG.X86_64.isa := VG.X86_64.Code.erase Impl.Ecdsa.X86_64.p384x.mulBaseFn

materialize_shared mulBaseErasedAdx

end VG.Proof.Ecdsa.X86_64.P384
