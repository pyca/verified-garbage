import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Aes.Arm.Ctr32
import VerifiedGarbage.Proof.Aes.Arm.ExpandKey
import VerifiedGarbage.Proof.Aes.Arm.Blocks
import VerifiedGarbage.Proof.Aes.Arm.Frame

/-! # AES on ARMv7 -/

namespace VG.Artifacts.Aes.Arm

def artifacts : List Artifact := [
  { Spec.Aes.expandKeyApi with
    target := Arm.target
    doc := Spec.Aes.expandKeyApi.doc
      (notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence). The working space is in a frame of 512 bytes \
        on the stack, zeroed before returning."])
    code := Impl.StackScratch.Arm.withRegScratchWiped 512 .r3 128 Impl.Aes.Arm.expandKey
    contract := Spec.Aes.expandKeyContract Arm.abi 512
    stack := 512
    verified := Proof.Aes.Arm.expandKey_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Aes.expandKeyScratchApi with
    target := Arm.target
    doc := Spec.Aes.expandKeyScratchApi.doc
      (notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.Arm.expandKey
    contract := Spec.Aes.expandKeyScratchContract Arm.abi
    verified := Proof.Aes.Arm.expandKey_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Gcm.ctr32Api with
    target := Arm.target
    doc := Spec.Gcm.ctr32Api.doc
      (notes := ["Constant-time bitsliced AES, two blocks at a time, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.Arm.ctr32
    contract := Spec.Gcm.ctr32Contract Arm.abi
    verified := Proof.Aes.Arm.ctr32_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Aes.encryptBlocksApi with
    target := Arm.target
    doc := Spec.Aes.encryptBlocksApi.doc
      (notes := ["Constant-time bitsliced AES, two blocks at a time, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.Arm.encryptBlocks
    contract := Spec.Aes.encryptBlocksContract Arm.abi
    verified := Proof.Aes.Arm.Ecb.encryptBlocks_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Aes.decryptBlocksApi with
    target := Arm.target
    doc := Spec.Aes.decryptBlocksApi.doc
      (notes := ["Constant-time bitsliced AES, two blocks at a time, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence): the inverse S-box is the forward one between \
        two inverse affine maps."])
    code := Impl.Aes.Arm.decryptBlocks
    contract := Spec.Aes.decryptBlocksContract Arm.abi
    verified := Proof.Aes.Arm.Ecb.decryptBlocks_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Aes.Arm
