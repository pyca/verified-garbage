module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.VerifyVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's verification equation, on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ed25519Verify.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed25519.verifyEquationApi.artifact PPC64LE.target {
    notes := ["Uses baseline integer instructions. Checks S < L and the canonical encodings of A \
      and R (decoded by one loop running the decoding twice), then evaluates the uncofactored \
      equation using all 512 challenge bits, with `vg_ed25519_scalar_base`'s fixed schedule of \
      16-bit batches for [S] B and [k] A. Branches depend only on the public inputs. Point \
      additions and doublings are calls of `vg_ed25519_r32_point_add`, field products calls of \
      `vg_gf25519_r32_mul`, and the square root's chain to `z^(2^250 - 1)` a call of \
      `vg_gf25519_r32_pow250`, each on `scratch`. Point tables, the saved nonvolatile registers \
      and `lr` reside in `scratch`."]
    code := Impl.Ed25519.PPC64LE.verifyEquation
    verified := Proof.Ed25519.PPC64LE.verifyEquation_verified }]

end VG.Artifacts.Ed25519Verify.PPC64LE
