module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
public import VerifiedGarbage.Proof.Aes.RISCV64.Ctr32Verified
public import VerifiedGarbage.Proof.Aes.RISCV64.ExpandKeyVerified
public import VerifiedGarbage.Proof.Aes.RISCV64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit

/-!
# AES (FIPS 197) on RISC-V

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted, each made from its function's `Api` (in `Spec/`, reviewed with the
contract), with the notes on the implementation added here.
-/

@[expose] public section

namespace VG.Artifacts.Aes.RISCV64

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact RISCV64.target {
    notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence). The key and the schedule are accessed a byte at a \
        time, since the contract states no alignment for them. The working space is in a frame of \
        512 bytes on the stack, zeroed before returning."]
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a3 64 Impl.Aes.RISCV64.expandKey
    stack := 512
    verified := Proof.Aes.RISCV64.expandKey_framed },
  Spec.Aes.expandKeyScratchApi.artifact RISCV64.target {
    notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence). The key and the schedule are accessed a byte at a \
        time, since the contract states no alignment for them; `scratch` is rounded up to a \
        multiple of 8."]
    code := Impl.Aes.RISCV64.expandKey
    verified := Proof.Aes.RISCV64.expandKey_verified },
  Spec.Gcm.ctr32Api.artifact RISCV64.target {
    notes := ["Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence). The schedule, the counter and the data are \
        accessed a byte at a time, since the contract states no alignment for them; `scratch` is \
        rounded up to a multiple of 8."]
    code := Impl.Aes.RISCV64.ctr32
    verified := Proof.Aes.RISCV64.ctr32_verified },
  Spec.Aes.encryptBlocksApi.artifact RISCV64.target {
    notes := ["Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence). The schedule and the data are accessed a byte at \
        a time, since the contract states no alignment for them; `scratch` is rounded up to a \
        multiple of 8."]
    code := Impl.Aes.RISCV64.encryptBlocks
    verified := Proof.Aes.RISCV64.encryptBlocks_verified },
  Spec.Aes.decryptBlocksApi.artifact RISCV64.target {
    notes := ["Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence): the inverse S-box is the forward one between two \
        inverse affine maps. The schedule and the data are accessed a byte at a time, since the \
        contract states no alignment for them; `scratch` is rounded up to a multiple of 8."]
    code := Impl.Aes.RISCV64.decryptBlocks
    verified := Proof.Aes.RISCV64.decryptBlocks_verified }]

end VG.Artifacts.Aes.RISCV64
