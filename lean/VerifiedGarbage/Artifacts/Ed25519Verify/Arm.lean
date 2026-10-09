import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyVerified

/-! Baseline ARMv7 Ed25519 primitive with register saves in the reviewed scratch buffer. -/
namespace VG.Artifacts.Ed25519Verify.Arm

def artifacts : List Artifact := [
  { Spec.Ed25519.verifyEquationApi with
    target := Arm.target
    doc := Spec.Ed25519.verifyEquationApi.doc (notes := ["Uses baseline integer instructions. \
      Checks canonical point encodings (A's, then R's, by one loop running the decoding twice) \
      and S < L, then evaluates the uncofactored equation \
      using all 512 challenge bits. Point decoding branches depend only on public inputs. \
      Point additions and doublings are calls of `vg_ed25519_r16_point_add` and \
      `vg_ed25519_r16_point_double`, and the square root's chain to `z^(2^250 - 1)` a call of \
      `vg_gf25519_r16_pow250`, each on `scratch`. Point tables, saved registers and `lr` reside \
      in `scratch`."])
    code := Impl.Ed25519.Arm.verifyEquation
    contract := Spec.Ed25519.verifyEquationContract Arm.abi
    verified := Proof.Ed25519.Arm.verify_verified
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed25519Verify.Arm
