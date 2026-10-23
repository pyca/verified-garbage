module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Blowfish.PPC64LE

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact PPC64LE.target {
    notes := ["The initial schedule is written from 521 immediates, the P-array keyed a byte of the key \
        at a time, and the 521 encryptions run ECB's block function under the schedule as it is \
        written. Our caller's r14-r17 are kept in 32 bytes of working space on the stack, zeroed \
        before returning."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 64 .r6 4 Impl.Blowfish.PPC64LE.expandKey
    stack := 64
    verified := Proof.Blowfish.PPC64LE.expandKey_framed },
  Spec.Blowfish.ecbEncryptApi.artifact PPC64LE.target {
    notes := ["One block at a time in general-purpose registers: each S-box lookup reads the 256 \
        entries of its four byte planes, a word (four entries) of each at a time, keeping the bytes \
        of the entry that is the index under masks computed from it, so no address depends on the \
        data or the schedule. Our caller's r14-r17 are kept in 32 bytes of working space on the \
        stack, zeroed before returning."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 288 .r6 4 Impl.Blowfish.PPC64LE.encrypt
    stack := 288
    verified := Proof.Blowfish.PPC64LE.ecb_framed Proof.Blowfish.PPC64LE.encrypt_verified },
  Spec.Blowfish.ecbDecryptApi.artifact PPC64LE.target {
    notes := ["One block at a time in general-purpose registers: each S-box lookup reads the 256 \
        entries of its four byte planes, a word (four entries) of each at a time, keeping the bytes \
        of the entry that is the index under masks computed from it, so no address depends on the \
        data or the schedule. Our caller's r14-r17 are kept in 32 bytes of working space on the \
        stack, zeroed before returning."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 288 .r6 4 Impl.Blowfish.PPC64LE.decrypt
    stack := 288
    verified := Proof.Blowfish.PPC64LE.ecb_framed Proof.Blowfish.PPC64LE.decrypt_verified }]

end VG.Artifacts.Blowfish.PPC64LE
