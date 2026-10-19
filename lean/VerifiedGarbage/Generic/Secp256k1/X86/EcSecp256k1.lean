module

public import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
import VerifiedGarbage.Impl.EcKey.Secp256k1.X86
import VerifiedGarbage.Proof.EcKey.X86.Secp256k1.Verified
public import VerifiedGarbage.Proof.EcKey.X86.Secp256k1.Lit
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Spec.EcKey.Secp256k1

/-!
# secp256k1 public keys (FIPS 186-5 §A.2) on x86 (32-bit)

A generic file (see `TCB/Emit.lean`) over secp256k1's group law `h`, the variant
`Variants/Secp256k1/X86/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.X86.EcSecp256k1

def artifacts (h : Proof.Weierstrass.X86.Inv.HasLawInv Spec.Secp256k1.curve) : List Artifact := [
  Spec.EcKey.Secp256k1.publicKeyApi.artifact X86.target {
    notes := ["The function is `vg_ecdsa_secp256k1_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it \
      saves the callee-saved registers `ebx`, `esi`, `edi` and `ebp` in `scratch`; field \
      elements are eight 32-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, with `mul` and the accumulator in `scratch`, in calls of `vg_secp256k1_mul_mod_p` and the other \
      functions of `secp256k1_mont`) with a final \
      conditional subtraction; `[d]G` is a double-and-add ladder over all 256 bits of `d`, with \
      the complete addition formulas of Renes, Costello and Batina for every addition and \
      doubling (calls of `vg_secp256k1_point_double` and `vg_secp256k1_point_add`) and a masked \
      selection for each bit; and `Z⁻¹` is computed by constant-time divsteps. The result (or zeros) is selected \
      by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    code := Impl.EcKey.X86.publicKeySecp256k1
    stack := 28
    verified := Proof.EcKey.X86.Secp256k1.pk_verified h.law h.inv }]

end VG.Generic.Secp256k1.X86.EcSecp256k1
