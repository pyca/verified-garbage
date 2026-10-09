import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified

/-! Baseline ARMv7 Ed25519 primitive with register saves in the reviewed scratch buffer. -/
namespace VG.Artifacts.Ed25519ScalarBase.Arm

def artifacts : List Artifact := [
  { Spec.Ed25519.scalarBaseApi with
    target := Arm.target
    doc := Spec.Ed25519.scalarBaseApi.doc (notes := ["Uses baseline integer instructions \
      and a fixed schedule for all 256 input bits. Field products use only low 32-bit \
      `mul` on 16-bit limbs. Point additions and doublings are calls of \
      `vg_ed25519_r16_point_add` and `vg_ed25519_r16_point_double`, and the inversion's chain to \
      `z^(2^250 - 1)` a call of `vg_gf25519_r16_pow250`, each on `scratch`. Point tables, saved \
      registers and `lr` reside in `scratch`."])
    code := Impl.Ed25519.Arm.scalarBase
    contract := Spec.Ed25519.scalarBaseContract Arm.abi
    verified := Proof.Ed25519.Arm.scalarBase_verified
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed25519ScalarBase.Arm
