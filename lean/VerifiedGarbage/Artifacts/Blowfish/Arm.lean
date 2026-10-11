import VerifiedGarbage.Proof.Blowfish.Arm.Frame

namespace VG.Artifacts.Blowfish.Arm

def artifacts : List Artifact := [
  { Spec.Blowfish.expandKeyApi with
    target := Arm.target
    doc := Spec.Blowfish.expandKeyApi.doc
      (notes := ["The initial schedule is written from immediates, the P-array keyed a byte of the key at \
        a time, and the 521 encryptions run ECB's block function under the schedule as it is written. \
        Our caller's registers, the next entries' pointer and the encryptions left are kept in 64 bytes \
        of working space on the stack, whose first 48 are zeroed before returning."])
    code := Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 12 Impl.Blowfish.Arm.expandKey
    contract := Spec.Blowfish.expandKeyContract Arm.abi 64
    stack := 64
    verified := Proof.Blowfish.Arm.expandKey_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Blowfish.ecbEncryptApi with
    target := Arm.target
    doc := Spec.Blowfish.ecbEncryptApi.doc
      (notes := ["One block at a time in core registers: each S-box lookup reads the 256 entries of its four \
        byte planes, a word (four entries) of each at a time, keeping the bytes of the entry that is the \
        index under masks computed from it, so no address depends on the data or the schedule. Our \
        caller's registers, the data pointer and the blocks left are kept in 256 bytes of working space \
        on the stack, whose first 48 are zeroed before returning."])
    code := Impl.StackScratch.Arm.withRegScratchWiped 256 .r3 12 Impl.Blowfish.Arm.encrypt
    contract := Spec.Blowfish.ecbEncryptContract Arm.abi 256
    stack := 256
    ofSig := ⟨_, _, _, by unfold Spec.Blowfish.ecbEncryptContract Spec.Blowfish.ecbContract; rfl⟩
    verified := Proof.Blowfish.Arm.ecb_framed true
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Blowfish.ecbDecryptApi with
    target := Arm.target
    doc := Spec.Blowfish.ecbDecryptApi.doc
      (notes := ["One block at a time in core registers: each S-box lookup reads the 256 entries of its four \
        byte planes, a word (four entries) of each at a time, keeping the bytes of the entry that is the \
        index under masks computed from it, so no address depends on the data or the schedule. Our \
        caller's registers, the data pointer and the blocks left are kept in 256 bytes of working space \
        on the stack, whose first 48 are zeroed before returning."])
    code := Impl.StackScratch.Arm.withRegScratchWiped 256 .r3 12 Impl.Blowfish.Arm.decrypt
    contract := Spec.Blowfish.ecbDecryptContract Arm.abi 256
    stack := 256
    ofSig := ⟨_, _, _, by unfold Spec.Blowfish.ecbDecryptContract Spec.Blowfish.ecbContract; rfl⟩
    verified := Proof.Blowfish.Arm.ecb_framed false
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Blowfish.Arm
