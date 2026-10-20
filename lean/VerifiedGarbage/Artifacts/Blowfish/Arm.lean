module

public import VerifiedGarbage.Proof.Blowfish.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Blowfish.Arm

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact Arm.target {
    notes := ["The initial schedule is copied from the static `VG_BLOWFISH_INIT`, seven words a \
        step, the P-array keyed a byte of the key at a time, and the 521 encryptions run ECB's block \
        function under the schedule as it is written. Our caller's registers, the next entries' \
        pointer and the encryptions left are kept in 64 bytes of working space on the stack, whose \
        first 48 are zeroed before returning."]
    consts := Impl.Blowfish.Arm.initConsts
    code := Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 12 Impl.Blowfish.Arm.expandKey
    stack := 64
    verified := Proof.Blowfish.Arm.expandKey_framed },
  Spec.Blowfish.ecbEncryptApi.artifact Arm.target {
    notes := ["One block at a time in core registers: each S-box lookup reads the 256 entries of its four \
        byte planes, a word (four entries) of each at a time, keeping the bytes of the entry that is the \
        index under masks computed from it, so no address depends on the data or the schedule. Our \
        caller's registers, the data pointer and the blocks left are kept in 256 bytes of working space \
        on the stack, whose first 48 are zeroed before returning."]
    code := Impl.StackScratch.Arm.withRegScratchWiped 256 .r3 12 Impl.Blowfish.Arm.encrypt
    stack := 256
    verified := Proof.Blowfish.Arm.ecb_framed true },
  Spec.Blowfish.ecbDecryptApi.artifact Arm.target {
    notes := ["One block at a time in core registers: each S-box lookup reads the 256 entries of its four \
        byte planes, a word (four entries) of each at a time, keeping the bytes of the entry that is the \
        index under masks computed from it, so no address depends on the data or the schedule. Our \
        caller's registers, the data pointer and the blocks left are kept in 256 bytes of working space \
        on the stack, whose first 48 are zeroed before returning."]
    code := Impl.StackScratch.Arm.withRegScratchWiped 256 .r3 12 Impl.Blowfish.Arm.decrypt
    stack := 256
    verified := Proof.Blowfish.Arm.ecb_framed false }]

end VG.Artifacts.Blowfish.Arm
