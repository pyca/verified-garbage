module

public import VerifiedGarbage.Proof.Blowfish.X86.Frame
import VerifiedGarbage.Proof.Blowfish.X86.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Blowfish on baseline x86 -/

@[expose] public section

namespace VG.Artifacts.Blowfish.X86

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact X86.target {
    notes := ["The initial schedule is written from immediates, the P-array keyed a byte of the key at \
        a time, and the 521 encryptions run ECB's block function under the schedule as it is written. \
        Our caller's `ebx`, `esi`, `edi` and `ebp`, the halves, the next entries' pointer and the \
        encryptions left are kept in 64 bytes of working space on the stack, whose first 40 are zeroed \
        before returning."]
    code := Impl.StackScratch.X86.withStackScratchWiped 84 3 10 Impl.Blowfish.X86.expandKey
    stack := 84
    verified := Proof.Blowfish.X86.expandKey_framed },
  Spec.Blowfish.ecbEncryptApi.artifact X86.target {
    notes := ["One block at a time: each S-box lookup reads the 256 entries of its four byte planes, a \
        word (four entries) of each at a time, keeping the bytes of the entry that is the index under \
        masks made by `cmp` and `sbb`, so no address depends on the data or the schedule. Our caller's \
        `ebx`, `esi`, `edi` and `ebp`, the halves, the data pointer and the blocks left are kept in 256 \
        bytes of working space on the stack, whose first 40 are zeroed before returning."]
    code := Impl.StackScratch.X86.withStackScratchWiped 276 3 10 Impl.Blowfish.X86.encrypt
    stack := 276
    verified := Proof.Blowfish.X86.ecb_framed true },
  Spec.Blowfish.ecbDecryptApi.artifact X86.target {
    notes := ["One block at a time: each S-box lookup reads the 256 entries of its four byte planes, a \
        word (four entries) of each at a time, keeping the bytes of the entry that is the index under \
        masks made by `cmp` and `sbb`, so no address depends on the data or the schedule. Our caller's \
        `ebx`, `esi`, `edi` and `ebp`, the halves, the data pointer and the blocks left are kept in 256 \
        bytes of working space on the stack, whose first 40 are zeroed before returning."]
    code := Impl.StackScratch.X86.withStackScratchWiped 276 3 10 Impl.Blowfish.X86.decrypt
    stack := 276
    verified := Proof.Blowfish.X86.ecb_framed false }]

end VG.Artifacts.Blowfish.X86
