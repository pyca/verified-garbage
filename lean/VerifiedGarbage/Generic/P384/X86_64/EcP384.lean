import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.P384.Comb7
import VerifiedGarbage.Impl.EcKey.P384.X86_64
import VerifiedGarbage.Proof.EcKey.X86_64.P384.Verified
import VerifiedGarbage.Proof.EcKey.X86_64.P384.Lit

/-!
# P-384 public keys (FIPS 186-5 §A.2) on x86-64

A generic file (see `TCB/Emit.lean`) over P-384's group law and
inversions `h`, the variant `Variants/P384/X86_64/Law.lean`.
-/

namespace VG.Generic.P384.X86_64.EcP384

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P384.curve) : List Artifact := [
  { Spec.EcKey.P384.publicKeyApi with
    target := X86_64.target
    doc := Spec.EcKey.P384.publicKeyApi.doc (notes := ["The function is `vg_ecdsa_p384_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it saves \
      its caller's callee-saved registers in `scratch`; field elements are six 64-bit words in \
      Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS) with a final \
      conditional subtraction; `[d]G` is the signature's comb over the 7-bit windows of `d`, from \
      the static `VG_P384_COMB`; and `Z⁻¹` is by the signature's divsteps. The result (or zeros) is selected by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, \
      so the time depends only on the pointers."])
    consts := Impl.Ecdsa.X86_64.p384.combConsts
    code := Impl.EcKey.X86_64.publicKeyP384
    contract := Spec.EcKey.P384.inst.publicKeyContract
      (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p384.combConsts)
    verified := Proof.EcKey.X86_64.P384.pk_verified h.law (Proof.P384.combOk7 h.law) h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.P384.X86_64.EcP384
