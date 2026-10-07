import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Impl.EcKey.P256.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothVerified

/-!
# P-256 public keys (FIPS 186-5 §A.2) on AArch64

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/AArch64/Law.lean`.
-/

namespace VG.Generic.P256.AArch64.EcP256

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvToM Spec.P256.curve) : List Artifact := [
  { Spec.EcKey.P256.publicKeyApi with
    target := AArch64.target
    doc := Spec.EcKey.P256.publicKeyApi.doc (notes := ["Public-key derivation shares signing's \
      width-7 Booth/Jacobian fixed-base comb and its existing 37 rows of 64 affine entries \
      in `VG_P256_COMB`. Every row is scanned in full; all secret-dependent selections use \
      masks. Mixed additions use specialized P-256 squaring and register forwarding. The \
      Booth/order proof excludes equal nonzero operands; masks handle zero digits and an \
      infinite accumulator. After conversion to homogeneous coordinates, fixed divsteps \
      invert `Z` and the affine coordinates are encoded. The function saves `x19`–`x25` in \
      its 8 KB scratch buffer and returns zeros for an invalid scalar. Timing depends only \
      on the pointers and the static table address."])
    consts := Impl.Ecdsa.AArch64.p256.combConsts
    code := Impl.P256.Booth.publicKey
    contract := Spec.EcKey.P256.inst.publicKeyContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p256.combConsts)
    verified := Proof.EcKey.AArch64.booth_pk_verified h.law h.inv (Proof.P256.combOk7 h.law)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P256.AArch64.EcP256
