module

public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.P224.Comb7
public import VerifiedGarbage.Impl.EcKey.P224.X86_64
public import VerifiedGarbage.Proof.EcKey.X86_64.P224.Verified
import VerifiedGarbage.Proof.EcKey.X86_64.P224.Lit
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-224 public keys (FIPS 186-5 §A.2) on x86-64

A generic file (see `TCB/Emit.lean`) over P-224's group law and
inversions `h`, the variant
`Variants/P224/X86_64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P224.X86_64.EcP224

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P224.curve) : List Artifact := [
  Spec.EcKey.P224.publicKeyApi.artifact X86_64.target {
    notes := ["The function is `vg_ecdsa_p224_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it saves \
      its caller's callee-saved registers in `scratch`; field elements are four 64-bit words in \
      Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS) with a final \
      conditional subtraction; `[d]G` is the signature's comb over the 7-bit windows of `d`, from \
      the static `VG_P224_COMB`; and `Z⁻¹` is by the signature's divsteps. The result (or zeros) is selected by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so \
      the time depends only on the pointers."]
    consts := Impl.Ecdsa.X86_64.p224.combConsts
    code := Impl.EcKey.X86_64.publicKeyP224
    stack := 8
    verified := Proof.EcKey.X86_64.P224.pk_verified h.law (Proof.P224.combOk7 h.law) h.inv }]

end VG.Generic.P224.X86_64.EcP224
