import VerifiedGarbage.Proof.Blowfish.X86_64.Frame

namespace VG.Artifacts.Blowfish.X86_64

def artifacts : List Artifact := [
  { Spec.Blowfish.expandKeyApi with
    target := X86_64.target
    doc := Spec.Blowfish.expandKeyApi.doc
      (notes := ["The initial schedule is written from 521 immediates, the P-array keyed a byte of \
        the key at a time, and the 521 encryptions run ECB's rounds under the schedule as it is \
        written; each output leaves the vector registers through 32 bytes of working space on the \
        stack, zeroed before returning."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 40 .rcx 4 Impl.Blowfish.X86_64.expandKey
    contract := Spec.Blowfish.expandKeyContract X86_64.abi 40
    stack := 40
    verified := Proof.Blowfish.X86_64.expandKey_framed
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Blowfish.ecbEncryptApi with
    target := X86_64.target
    doc := Spec.Blowfish.ecbEncryptApi.doc
      (notes := ["One block at a time with SSE2: each S-box lookup scans the 256 entries of its four \
        byte planes, 16 at a time, keeping the bytes of the entry that is the index under masks \
        computed from it, so no address depends on the data or the schedule. Each output block \
        goes through 16 bytes of working space on the stack, zeroed before returning."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 264 .rcx 2 Impl.Blowfish.X86_64.encrypt
    contract := Spec.Blowfish.ecbEncryptContract X86_64.abi 264
    stack := 264
    ofSig := ⟨_, _, _, by unfold Spec.Blowfish.ecbEncryptContract Spec.Blowfish.ecbContract; rfl⟩
    verified := Proof.Blowfish.X86_64.ecb_framed Proof.Blowfish.X86_64.encrypt_verified
      (Code.all_of_allInstrs (by lit_decide)) (by lit_decide)
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Blowfish.ecbDecryptApi with
    target := X86_64.target
    doc := Spec.Blowfish.ecbDecryptApi.doc
      (notes := ["One block at a time with SSE2: each S-box lookup scans the 256 entries of its four \
        byte planes, 16 at a time, keeping the bytes of the entry that is the index under masks \
        computed from it, so no address depends on the data or the schedule. Each output block \
        goes through 16 bytes of working space on the stack, zeroed before returning."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 264 .rcx 2 Impl.Blowfish.X86_64.decrypt
    contract := Spec.Blowfish.ecbDecryptContract X86_64.abi 264
    stack := 264
    ofSig := ⟨_, _, _, by unfold Spec.Blowfish.ecbDecryptContract Spec.Blowfish.ecbContract; rfl⟩
    verified := Proof.Blowfish.X86_64.ecb_framed Proof.Blowfish.X86_64.decrypt_verified
      (Code.all_of_allInstrs (by lit_decide)) (by lit_decide)
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Blowfish.X86_64
