import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdsa.P256.X86
import VerifiedGarbage.Proof.Ecdsa.X86.CombVerified
import VerifiedGarbage.Proof.Ecdsa.X86.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombVerified

/-!
# ECDSA over P-256 (FIPS 186-5) on x86 (32-bit)

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/X86/Law.lean`.
-/

namespace VG.Generic.P256.X86.EcdsaP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  { Spec.Ecdsa.P256.signApi with
    target := X86.target
    doc := Spec.Ecdsa.P256.signApi.doc (notes := ["The function saves the callee-saved registers \
      `ebx`, `esi`, `edi` and `ebp` in `scratch`. Field elements and scalars are eight 32-bit \
      words in Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS, \
      with `mul` and the accumulator in `scratch`) with a final conditional subtraction. `[k]G` \
      uses a seven-bit signed comb: 37 complete additions, no doublings, and constant-time \
      SSE2 scans of a shared 148 KiB table. Its position-independent table address uses a \
      balanced four-byte CALL frame. The inversions modulo `p` and `n` use square-and-always-multiply \
      over the bits of `p - 2` and `n - 2`. The signature (or zeros) is selected by a mask, so \
      the time depends only on the pointers."])
    code := Impl.Ecdsa.X86.signP256Comb
    consts := Impl.Ecdsa.X86.p256Comb.combConsts
    stack := 4
    contract := Spec.Ecdsa.P256.inst.signContract (X86.abi.withConsts Impl.Ecdsa.X86.p256Comb.combConsts) 4
    verified := Proof.Ecdsa.X86.signComb_verified h.law
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Ecdsa.P256.verifyApi with
    target := X86.target
    doc := Spec.Ecdsa.P256.verifyApi.doc (notes := ["The function validates the public key and \
      signature without branches. Field elements and scalars are eight 32-bit words in \
      Montgomery form. The fixed-base product `[u]G` uses a seven-bit signed comb: 37 complete \
      additions, no doublings, and constant-time SSE2 scans of a 148 KiB precomputed table. \
      Its position-independent table address uses a balanced four-byte CALL frame. The \
      variable-base product `[v]Q` uses 65 signed four-bit windows with Jacobian doublings \
      and constant-time scans of eight projective points, followed by a complete addition of the \
      two products. Scalar inversion uses square-and-always-multiply. \
      The final check avoids a field inversion: it compares `X = rZ`, or `X = (r+n)Z` when \
      `r+n < p`, and rejects `Z = 0`. Invalid inputs follow the same path and the result is selected by a mask; timing \
      depends only on pointers and the static table address."])
    code := Proof.Ecdsa.Verify.X86.vCombCode
    consts := Impl.Ecdsa.X86.p256Comb.combConsts
    stack := 4
    contract := Spec.Ecdsa.P256.inst.verifyContract (X86.abi.withConsts Impl.Ecdsa.X86.p256Comb.combConsts) 4
    verified := Proof.Ecdsa.Verify.X86.vComb_verified h.law
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.P256.X86.EcdsaP256
