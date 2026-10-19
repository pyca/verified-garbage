module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothVerified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.EcKey.AArch64.Lit
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothLit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.P256
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase

/-!
# P-256 public keys (FIPS 186-5 §A.2) on AArch64

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/AArch64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P256.AArch64.EcP256

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvToMOrd Spec.P256.curve) : List Artifact := [
  Spec.EcKey.P256.publicKeyApi.artifact AArch64.target {
    notes := ["Public-key derivation shares signing's \
      width-7 Booth/Jacobian fixed-base comb and its existing 37 rows of 64 affine entries \
      in `VG_P256_COMB`. Every row is scanned in full; all secret-dependent selections use \
      masks. Mixed additions use specialized P-256 squaring and register forwarding. The \
      Booth/order proof excludes equal nonzero operands; masks handle zero digits and an \
      infinite accumulator. After conversion to homogeneous coordinates, fixed divsteps \
      invert `Z` and the affine coordinates are encoded. The function saves `x19`–`x25` in \
      its 8 KB scratch buffer and returns zeros for an invalid scalar. Timing depends only \
      on the pointers and the static table address."]
    consts := Impl.Ecdsa.AArch64.p256.combConsts
    code := Impl.P256.Booth.publicKey
    verified := Proof.EcKey.AArch64.booth_pk_verified h.law h.inv (Proof.P256.combOk7 h.law) }]

end VG.Generic.P256.AArch64.EcP256
