import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Rc4.Arm.Verified

/-! # Raw RC4 on ARMv7 -/
namespace VG.Artifacts.Rc4.Arm

def artifacts : List Artifact := [
  { Spec.Rc4.initApi with
    target := Arm.target
    doc := Spec.Rc4.initApi.doc (notes := [
      "Secret-indexed table operations visit every word of the table at fixed addresses, \
       selecting and replacing bytes with masks made by `cmp` and `adc`. Our caller's \
       `r4`–`r11` are saved in `scratch`."])
    code := Impl.Rc4.Arm.init
    contract := Spec.Rc4.initContract Arm.abi
    verified := Proof.Rc4.Arm.init_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rc4.applyApi with
    target := Arm.target
    doc := Spec.Rc4.applyApi.doc (notes := [
      "Secret-indexed table operations visit every word of the table at fixed addresses, \
       selecting and replacing bytes with masks made by `cmp` and `adc`. Our caller's \
       `r4`–`r11` are saved in `scratch`."])
    code := Impl.Rc4.Arm.apply
    contract := Spec.Rc4.applyContract Arm.abi
    verified := Proof.Rc4.Arm.apply_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Rc4.Arm
