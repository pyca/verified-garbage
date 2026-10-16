module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.P192.X86
public import VerifiedGarbage.Proof.EcKey.X86.P192.Verified
import VerifiedGarbage.Proof.EcKey.X86.P192.Lit
import VerifiedGarbage.Proof.X25519.X86.Column
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-192 public keys (FIPS 186-5 §A.2) on x86 (32-bit)

A generic file (see `TCB/Emit.lean`) over P-192's group law `h`, the variant
`Variants/P192/X86/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P192.X86.EcP192

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve) : List Artifact := [
  Spec.EcKey.P192.publicKeyApi.artifact X86.target {
    notes := ["The function is `vg_ecdsa_p192_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it \
      saves the callee-saved registers `ebx`, `esi`, `edi` and `ebp` in `scratch`; field \
      elements are six 32-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, with `mul` and the accumulator in `scratch`, in calls of `vg_p192_mul_mod_p` and the other \
      functions of `p192_mont`) with a final \
      conditional subtraction; `[d]G` is a double-and-add ladder over all 192 bits of `d`, with \
      the complete addition formulas of Renes, Costello and Batina for every addition and \
      doubling (calls of `vg_p192_point_double` and `vg_p192_point_add`) and a masked \
      selection for each bit; and `Z⁻¹` is Fermat's, by \
      square-and-always-multiply over the bits of `p - 2`. The result (or zeros) is selected \
      by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    code := Impl.EcKey.X86.publicKeyP192
    stack := 28
    verified := Proof.EcKey.X86.P192.pk_verified h.law }]

end VG.Generic.P192.X86.EcP192
