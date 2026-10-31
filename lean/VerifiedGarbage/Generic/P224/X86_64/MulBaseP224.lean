module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.P224.Comb7
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.MulBaseVerified
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Lit

/-!
# P-224's base point multiplication on x86-64

`vg_p224_mul_base` (`Spec/Weierstrass/MulBase.lean`), which the signature
and the public key derivation call. A generic file (see `TCB/Emit.lean`)
over P-224's group law and inversions `h`, the variant
`Variants/P224/X86_64/Law.lean`: the comb's proof takes the group law, and
the curve's facts (`p224_ok`) its inversions.
-/

@[expose] public section

namespace VG.Generic.P224.X86_64.MulBaseP224

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P224.MulBase

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P224.curve) : List Artifact :=
  [C.mulBaseApi.artifact X86_64.target {
      consts := p224.combConsts
      code := cfg.mulBaseFn
      verified := mb_verified h.law (Proof.P224.combOk7 h.law) h.inv }]

end VG.Generic.P224.X86_64.MulBaseP224
