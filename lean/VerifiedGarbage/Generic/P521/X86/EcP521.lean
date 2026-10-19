module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.P521.X86
import VerifiedGarbage.Proof.EcKey.X86.P521.Verified
public import VerifiedGarbage.Proof.EcKey.X86.P521.Lit
public import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.P521

/-!
# P-521 public keys (FIPS 186-5 §A.2) on x86 (32-bit)

A generic file (see `TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/X86/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P521.X86.EcP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.EcKey.P521.publicKeyApi.artifact X86.target {
    notes := ["The function is `vg_ecdsa_p521_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it \
      saves the callee-saved registers `ebx`, `esi`, `edi` and `ebp` in `scratch`; field \
      elements are eighteen 32-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, with `mul` and the accumulator in `scratch`, in calls of `vg_p521_mul_mod_p` and the other \
      functions of `p521_mont`) with a final \
      conditional subtraction; `[d]G` is a double-and-add ladder over all 576 bits of the nine \
      words of `d`, with the complete addition formulas of Renes, Costello and Batina for every \
      addition and doubling and a masked selection for each bit; and `Z⁻¹` is Fermat's, by \
      square-and-always-multiply over the bits of `p - 2`. The result (or zeros) is selected \
      by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    code := Impl.EcKey.X86.publicKeyP521
    stack := 20
    verified := Proof.EcKey.X86.P521.pk_verified h.law }]

end VG.Generic.P521.X86.EcP521
