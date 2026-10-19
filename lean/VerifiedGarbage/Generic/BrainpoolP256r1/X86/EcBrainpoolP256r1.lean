module

public import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
import VerifiedGarbage.Impl.EcKey.BrainpoolP256r1.X86
import VerifiedGarbage.Proof.EcKey.X86.BrainpoolP256r1.Verified
public import VerifiedGarbage.Proof.EcKey.X86.BrainpoolP256r1.Lit
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Spec.EcKey.BrainpoolP256r1

/-!
# brainpoolP256r1 public keys (FIPS 186-5 §A.2) on x86 (32-bit)

A generic file (see `TCB/Emit.lean`) over brainpoolP256r1's group law `h`, the variant
`Variants/BrainpoolP256r1/X86/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.X86.EcBrainpoolP256r1

def artifacts (h : Proof.Weierstrass.X86.Inv.HasLawInv Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP256r1.publicKeyApi.artifact X86.target {
    notes := ["The function is `vg_ecdsa_brainpoolp256r1_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it \
      saves the callee-saved registers `ebx`, `esi`, `edi` and `ebp` in `scratch`; field \
      elements are eight 32-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, with `mul` and the accumulator in `scratch`, in calls of `vg_brainpoolp256r1_mul_mod_p` and the other \
      functions of `brainpoolp256r1_mont`) with a final \
      conditional subtraction; `[d]G` is a double-and-add ladder over all 256 bits of `d`, with \
      the complete addition formulas of Renes, Costello and Batina for every addition and \
      doubling (calls of `vg_brainpoolp256r1_point_double` and `vg_brainpoolp256r1_point_add`) and a masked \
      selection for each bit; and `Z⁻¹` is Fermat's, by \
      square-and-always-multiply over the bits of `p - 2`. The result (or zeros) is selected \
      by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    code := Impl.EcKey.X86.publicKeyBrainpoolP256r1
    stack := 28
    verified := Proof.EcKey.X86.BrainpoolP256r1.pk_verified h.law h.inv }]

end VG.Generic.BrainpoolP256r1.X86.EcBrainpoolP256r1
