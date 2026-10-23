module

public import VerifiedGarbage.Proof.AesXts.PPC64LE.Verified
public import VerifiedGarbage.Proof.AesXts.PPC64LE.Unit.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on PPC64LE

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. PPC64LE has one implementation of the block functions, so these are
not generic over them. A call (`bl`) stores nothing in memory, so no stack is
used.
-/

@[expose] public section

namespace VG.Artifacts.AesXts.PPC64LE

open VG.Proof.AesXts.PPC64LE

def artifacts : List Artifact := [
  Spec.Xts.aesEncryptApi.artifact PPC64LE.target {
    notes := [
      "This implementation enciphers one block at a time with `vg_aes_encrypt_blocks`."]
    code := Impl.AesXts.PPC64LE.encrypt
    verified := encrypt_verified },
  Spec.Xts.aesDecryptApi.artifact PPC64LE.target {
    notes := [
      "This implementation deciphers one block at a time with `vg_aes_decrypt_blocks`."]
    code := Impl.AesXts.PPC64LE.decrypt
    verified := decrypt_verified },
  Spec.Xts.aesEncryptUnitApi.artifact PPC64LE.target {
    notes := [
      "This implementation enciphers the tweak value and the data with `vg_aes_xts_encrypt` (the tweak value " ++
        "as one block from a zero tweak), and steals ciphertext by swapping bytes of the last two blocks in place."]
    code := Impl.AesXts.PPC64LEUnit.encrypt
    verified := Unit.encrypt_verified },
  Spec.Xts.aesDecryptUnitApi.artifact PPC64LE.target {
    notes := [
      "This implementation enciphers the tweak value with `vg_aes_xts_encrypt` (as one block from a zero " ++
        "tweak), deciphers the data with `vg_aes_xts_decrypt`, and steals ciphertext by swapping bytes of the " ++
        "last two blocks in place."]
    code := Impl.AesXts.PPC64LEUnit.decrypt
    verified := Unit.decrypt_verified }]

end VG.Artifacts.AesXts.PPC64LE
