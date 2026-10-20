module

public import VerifiedGarbage.Proof.TripleDes.Arm.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Triple DES-CFB8 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb8.Arm

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline ARMv7: the generic CFB8, a byte at a time, of `Impl/Modes/Arm/`, calling the verified \
  `vg_triple_des_ecb_encrypt` on one block per byte, with the chaining block in a 56-byte working \
  space on the stack, zeroed on return."

def artifacts : List Artifact := [
  Spec.TripleDes.cfb8EncryptApi.artifact Arm.target {
    notes := [note]
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfb8Encrypt
    stack := 1088
    verified := Proof.TripleDes.Arm.cfb8Encrypt_framed },
  Spec.TripleDes.cfb8DecryptApi.artifact Arm.target {
    notes := [note]
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfb8Decrypt
    stack := 1088
    verified := Proof.TripleDes.Arm.cfb8Decrypt_framed }]

end VG.Artifacts.TripleDesCfb8.Arm
