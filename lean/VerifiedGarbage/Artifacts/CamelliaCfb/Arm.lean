import VerifiedGarbage.Proof.Camellia.Arm.FbVerified

/-! # Camellia-CFB128 artifacts on baseline ARMv7 -/

namespace VG.Artifacts.CamelliaCfb.Arm

/-- How the functions compute the mode. -/
def note : String :=
  "Baseline ARMv7: the generic CFB of `Impl/Modes/Arm/`, one block at a time (each block's input is the ciphertext \
  block before), calling the verified `vg_camellia_ecb_encrypt` (bitsliced, in a batch of eight) on the chaining \
  value with the number of rounds, in a 72-byte working space on the stack, zeroed on return."

def artifacts : List Artifact := [
  { Spec.Camellia.cfbEncryptApi with
    target := Arm.target
    doc := Spec.Camellia.cfbEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbEncrypt
    contract := Spec.Camellia.cfbEncryptContract Arm.abi 2904
    stack := 2904
    verified := Proof.Camellia.Arm.cfbEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Camellia.cfbDecryptApi with
    target := Arm.target
    doc := Spec.Camellia.cfbDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbDecrypt
    contract := Spec.Camellia.cfbDecryptContract Arm.abi 2904
    stack := 2904
    verified := Proof.Camellia.Arm.cfbDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.CamelliaCfb.Arm
