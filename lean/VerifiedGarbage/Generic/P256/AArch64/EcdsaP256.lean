import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothVerified
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedVerified

/-!
# ECDSA over P-256 (FIPS 186-5) on AArch64

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/AArch64/Law.lean`.
-/

namespace VG.Generic.P256.AArch64.EcdsaP256

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvToMOrd Spec.P256.curve) : List Artifact := [
  { Spec.Ecdsa.P256.signApi with
    target := AArch64.target
    doc := Spec.Ecdsa.P256.signApi.doc (notes := ["The function saves `x19`–`x25` in its 8 KB \
      scratch buffer. Field elements and scalars are four 64-bit Montgomery words. `[k]G` \
      uses 37 width-7 Booth digits in `[-64,64]`, with no initial correction point. Each \
      affine entry is selected by scanning all 64 entries of its row in `VG_P256_COMB`; \
      sign correction uses a mask. From the lowest window upward, a Jacobian accumulator \
      uses mixed additions (8 products and 3 squares), specialized P-256 squaring, and \
      register forwarding between field operations. The Booth partial-sum and generator-order \
      proofs exclude equal nonzero inputs to the mixed formula. Infinity and zero-digit \
      cases use masks. The result is converted once to homogeneous coordinates `(XZ,Y,Z³)`. \
      Field and scalar inversions use 590 fixed divsteps in ten batches of 59. The signature \
      or zeros is selected by a validity mask. The loops, table accesses and arithmetic \
      have timing independent of the secret key, nonce and digest."])
    consts := Impl.Ecdsa.AArch64.p256.combConsts
    code := Impl.P256.Booth.sign
    contract := Spec.Ecdsa.P256.inst.signContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p256.combConsts)
    verified := Proof.Ecdsa.AArch64.booth_sign_verified h.law h.inv (Proof.P256.combOk7 h.law)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Ecdsa.P256.verifyApi with
    target := AArch64.target
    doc := Spec.Ecdsa.P256.verifyApi.doc (notes := ["The function saves the callee-saved registers \
      `x19`–`x28` and `x30` in its 8 KB scratch buffer. Field elements and scalars are four \
      64-bit words in Montgomery form; field squares use the specialized P-256 Montgomery \
      square. The key is checked without branches, and multiplication uses the key's point \
      if valid, else `G`. The scalar inverse uses nine batches of 59 divsteps, with a tenth \
      batch when the public input requires it. `[u]G + [v]Q` uses one \
      joint Jacobian accumulator with width-7 and width-5 sparse signed digits, respectively. \
      Generator digits reuse the odd multiples in the first row of `VG_P256_COMB`. The eight \
      odd multiples of `Q` cache their Jacobian `Z²` and `Z³` values. The joint loop doubles \
      its accumulator in place, specializes arithmetic to the sparse P-256 prime, and keeps \
      field values in scalar registers across operations with checked scheduling and allocation, \
      then converts once to homogeneous coordinates. Verification compares the projective \
      x-coordinate with `r` and, when in range, `r + n`, without a field inversion. Table \
      lookups, skipped zero digits and exceptional-point branches depend on the public key, \
      digest and signature already declared public by the contract. The result combines \
      the key and scalar checks, rejection of infinity, and `x ≡ r` modulo `n` into a mask."])
    consts := Impl.Ecdsa.AArch64.p256.combConsts
    code := Impl.Ecdsa.Verify.AArch64.P256Allocated.verify
    contract := Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p256.combConsts)
    verified := Proof.Ecdsa.Verify.AArch64.allocatedVerify_verified h.law h.inv h.invToM (Proof.P256.combOk7 h.law)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P256.AArch64.EcdsaP256
