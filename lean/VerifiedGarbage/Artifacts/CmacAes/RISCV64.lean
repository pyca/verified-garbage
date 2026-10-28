module

public import VerifiedGarbage.Proof.CmacAes.RISCV64.Verified
public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-CMAC (NIST SP 800-38B) on RISC-V

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. RISC-V has one implementation of the block functions, so these are
not generic over them. A call (`jal`) stores nothing in memory, and the
return address is saved in the scratch buffer, so
`vg_cmac_aes_subkeys`, `vg_cmac_aes_update` and `vg_cmac_aes_finalize` use
no stack.

The streaming functions keep their working space in a frame of their own
on the stack (`Proof/CmacAes/Stream/RISCV64/Frame.lean`): their `stack` is
that frame.
-/

@[expose] public section

namespace VG.Artifacts.CmacAes.RISCV64

open VG.Proof.CmacAes.RISCV64

/-- How the functions encipher a block. -/
def blockNote : String := "This implementation enciphers each block with `vg_aes_encrypt_blocks`. \
  The subkeys, the chaining value and the data are accessed a byte at a time, since the contract \
  states no alignment for them."

def artifacts : List Artifact := [
  Spec.Cmac.aesSubkeysApi.artifact RISCV64.target {
    notes := [blockNote]
    code := Impl.CmacAes.RISCV64.subkeys
    verified := subkeys_verified },
  Spec.Cmac.aesUpdateApi.artifact RISCV64.target {
    notes := [blockNote]
    code := Impl.CmacAes.RISCV64.update
    verified := update_verified },
  Spec.Cmac.aesFinalizeApi.artifact RISCV64.target {
    notes := [blockNote]
    code := Impl.CmacAes.RISCV64.finalize
    verified := finalize_verified },
  Spec.Cmac.aesInitApi.artifact RISCV64.target {
    notes := [
      "This implementation expands the key with `vg_aes_expand_key_scratch` and derives the subkeys with \
        `vg_cmac_aes_subkeys`."]
    code := Impl.StackScratch.RISCV64.withStackScratch 2304 .a3 Impl.CmacAes.Stream.RISCV64.init
    stack := 2304
    verified := Proof.CmacAes.Stream.RISCV64.init_framed },
  Spec.Cmac.aesAbsorbApi.artifact RISCV64.target {
    notes := [
      "This implementation chains the blocks with `vg_cmac_aes_update`."]
    code := Impl.StackScratch.RISCV64.withStackScratch 2304 .a5 Impl.CmacAes.Stream.RISCV64.absorb
    stack := 2304
    verified := Proof.CmacAes.Stream.RISCV64.absorb_framed },
  Spec.Cmac.aesFinishApi.artifact RISCV64.target {
    notes := [
      "This implementation computes the MAC with `vg_cmac_aes_finalize`."]
    code := Impl.StackScratch.RISCV64.withStackScratch 2304 .a4 Impl.CmacAes.Stream.RISCV64.finish
    stack := 2304
    verified := Proof.CmacAes.Stream.RISCV64.finish_framed }]

end VG.Artifacts.CmacAes.RISCV64
