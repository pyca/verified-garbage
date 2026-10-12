import VerifiedGarbage.Proof.TripleDes.Arm.FbVerified

/-! # Triple DES-CFB64 artifacts on baseline ARMv7 -/

namespace VG.Artifacts.TripleDesCfb.Arm

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline ARMv7: the generic CFB of `Impl/Modes/Arm/`, calling the verified \
  `vg_triple_des_ecb_encrypt` on one block at a time, with the chaining block in a 56-byte working \
  space on the stack, zeroed on return."

def artifacts : List Artifact := [
  { Spec.TripleDes.cfbEncryptApi with
    target := Arm.target
    doc := Spec.TripleDes.cfbEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbEncrypt
    contract := Spec.TripleDes.cfbEncryptContract Arm.abi 1088
    stack := 1088
    verified := Proof.TripleDes.Arm.cfbEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.TripleDes.cfbDecryptApi with
    target := Arm.target
    doc := Spec.TripleDes.cfbDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbDecrypt
    contract := Spec.TripleDes.cfbDecryptContract Arm.abi 1088
    stack := 1088
    verified := Proof.TripleDes.Arm.cfbDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.TripleDesCfb.Arm
