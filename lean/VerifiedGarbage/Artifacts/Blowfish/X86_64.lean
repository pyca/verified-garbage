module
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86_64.Lit

public import VerifiedGarbage.Proof.Blowfish.X86_64.Frame
public import VerifiedGarbage.Proof.Blowfish.X86_64.Verified
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Blowfish.X86_64

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact X86_64.target {
    notes := ["The initial schedule is written from 521 immediates, the P-array keyed a byte of \
        the key at a time, and the 521 encryptions run ECB's rounds under the schedule as it is \
        written; each output leaves the vector registers through 32 bytes of working space on the \
        stack, zeroed before returning."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 40 .rcx 4 Impl.Blowfish.X86_64.expandKey
    stack := 40
    verified := Proof.Blowfish.X86_64.expandKey_framed },
  Spec.Blowfish.ecbEncryptApi.artifact X86_64.target {
    notes := ["One block at a time with SSE2: each S-box lookup scans the 256 entries of its four \
        byte planes, 16 at a time, keeping the bytes of the entry that is the index under masks \
        computed from it, so no address depends on the data or the schedule. Each output block \
        goes through 16 bytes of working space on the stack, zeroed before returning."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 264 .rcx 2 Impl.Blowfish.X86_64.encrypt
    stack := 264
    verified := Proof.Blowfish.X86_64.ecb_framed Proof.Blowfish.X86_64.encrypt_verified },
  Spec.Blowfish.ecbDecryptApi.artifact X86_64.target {
    notes := ["One block at a time with SSE2: each S-box lookup scans the 256 entries of its four \
        byte planes, 16 at a time, keeping the bytes of the entry that is the index under masks \
        computed from it, so no address depends on the data or the schedule. Each output block \
        goes through 16 bytes of working space on the stack, zeroed before returning."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 264 .rcx 2 Impl.Blowfish.X86_64.decrypt
    stack := 264
    verified := Proof.Blowfish.X86_64.ecb_framed Proof.Blowfish.X86_64.decrypt_verified }]

end VG.Artifacts.Blowfish.X86_64
