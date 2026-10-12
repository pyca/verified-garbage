import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Blowfish.X86.Frame

/-! # Blowfish on baseline x86 -/
namespace VG.Artifacts.Blowfish.X86

def artifacts : List Artifact := [
  { Spec.Blowfish.expandKeyApi with
    target := X86.target
    doc := Spec.Blowfish.expandKeyApi.doc
      (notes := ["The initial schedule is written from immediates, the P-array keyed a byte of the key at \
        a time, and the 521 encryptions run ECB's block function under the schedule as it is written. \
        Our caller's `ebx`, `esi`, `edi` and `ebp`, the halves, the next entries' pointer and the \
        encryptions left are kept in 64 bytes of working space on the stack, whose first 40 are zeroed \
        before returning."])
    code := Impl.StackScratch.X86.withStackScratchWiped 84 3 10 Impl.Blowfish.X86.expandKey
    contract := Spec.Blowfish.expandKeyContract X86.abi 84
    stack := 84
    verified := Proof.Blowfish.X86.expandKey_framed
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Blowfish.ecbEncryptApi with
    target := X86.target
    doc := Spec.Blowfish.ecbEncryptApi.doc
      (notes := ["One block at a time: each S-box lookup reads the 256 entries of its four byte planes, a \
        word (four entries) of each at a time, keeping the bytes of the entry that is the index under \
        masks made by `cmp` and `sbb`, so no address depends on the data or the schedule. Our caller's \
        `ebx`, `esi`, `edi` and `ebp`, the halves, the data pointer and the blocks left are kept in 256 \
        bytes of working space on the stack, whose first 40 are zeroed before returning."])
    code := Impl.StackScratch.X86.withStackScratchWiped 276 3 10 Impl.Blowfish.X86.encrypt
    contract := Spec.Blowfish.ecbEncryptContract X86.abi 276
    stack := 276
    ofSig := by exact (⟨_, _, _, by unfold Spec.Blowfish.ecbEncryptContract Spec.Blowfish.ecbContract; rfl⟩)
    verified := Proof.Blowfish.X86.ecb_framed true
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Blowfish.ecbDecryptApi with
    target := X86.target
    doc := Spec.Blowfish.ecbDecryptApi.doc
      (notes := ["One block at a time: each S-box lookup reads the 256 entries of its four byte planes, a \
        word (four entries) of each at a time, keeping the bytes of the entry that is the index under \
        masks made by `cmp` and `sbb`, so no address depends on the data or the schedule. Our caller's \
        `ebx`, `esi`, `edi` and `ebp`, the halves, the data pointer and the blocks left are kept in 256 \
        bytes of working space on the stack, whose first 40 are zeroed before returning."])
    code := Impl.StackScratch.X86.withStackScratchWiped 276 3 10 Impl.Blowfish.X86.decrypt
    contract := Spec.Blowfish.ecbDecryptContract X86.abi 276
    stack := 276
    ofSig := by exact (⟨_, _, _, by unfold Spec.Blowfish.ecbDecryptContract Spec.Blowfish.ecbContract; rfl⟩)
    verified := Proof.Blowfish.X86.ecb_framed false
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Blowfish.X86
