module

public import VerifiedGarbage.Proof.Rc2.Arm.Stream.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RC2 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Rc2.Arm

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact Arm.target {
    notes := ["Baseline ARMv7, copying the IV and calling the verified \
      key expansion (which scans PITABLE in the static `VG_RC2_PITABLE`)."]
    consts := Impl.Rc2.piConsts
    code := Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.init
    stack := 600
    verified := Proof.Rc2.Arm.Stream.init_framed },
  Spec.Rc2.cbcEncryptUpdateApi.artifact Arm.target {
    notes := ["Baseline ARMv7, copying bytes one at a time and \
      calling the verified RC2-CBC encryption."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.encryptUpdate
    stack := 600
    verified := Proof.Rc2.Arm.Stream.encryptUpdate_framed },
  Spec.Rc2.cbcDecryptUpdateApi.artifact Arm.target {
    notes := ["Baseline ARMv7, copying bytes one at a time and \
      calling the verified RC2-CBC decryption."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.decryptUpdate
    stack := 600
    verified := Proof.Rc2.Arm.Stream.decryptUpdate_framed },
  Spec.Rc2.cbcEncryptApi.artifact Arm.target {
    notes := ["Baseline ARMv7, calling the verified RC2 block primitive."]
    code := Impl.Rc2.Arm.Cbc.encrypt
    stack := 0
    verified := Proof.Rc2.Arm.Cbc.encrypt_verified },
  Spec.Rc2.cbcDecryptApi.artifact Arm.target {
    notes := ["Baseline ARMv7, preserving the input ciphertext for the next IV."]
    code := Impl.Rc2.Arm.Cbc.decrypt
    stack := 0
    verified := Proof.Rc2.Arm.Cbc.decrypt_verified },
  Spec.Rc2.expandKeyApi.artifact Arm.target {
    notes := ["Baseline ARMv7. Each PITABLE lookup scans the 256 bytes of the static `VG_RC2_PITABLE` in \
        order, at addresses that depend only on the entry's number, keeping each byte under a mask that is \
        nonzero exactly when the secret index is the entry's number (`eor`, then `(x - 1) >> 8`). No secret \
        is an address or a branch condition."]
    consts := Impl.Rc2.piConsts
    code := Impl.Rc2.Arm.expandKey
    stack := 0
    verified := Proof.Rc2.Arm.key_verified },
  Spec.Rc2.encryptBlockApi.artifact Arm.target {
    notes := ["Baseline ARMv7. Mashing scans all 64 schedule words in a fixed order, in a loop, \
      two words per 32-bit load."]
    code := Impl.Rc2.Arm.encryptBlock
    stack := 0
    verified := Proof.Rc2.Arm.encrypt_verified },
  Spec.Rc2.decryptBlockApi.artifact Arm.target {
    notes := ["Baseline ARMv7. Reverse mashing scans all 64 schedule words in a fixed order, in a \
      loop, two words per 32-bit load."]
    code := Impl.Rc2.Arm.decryptBlock
    stack := 0
    verified := Proof.Rc2.Arm.decrypt_verified }]

end VG.Artifacts.Rc2.Arm
