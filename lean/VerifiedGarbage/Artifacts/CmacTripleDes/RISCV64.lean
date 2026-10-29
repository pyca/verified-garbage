module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on RISC-V

The functions call the verified key expansion and ECB encryption on one
block, keeping the return address in their working space, which is in a
frame of their own on the stack
(`Proof/CmacTripleDes/Stream/RISCV64/Frame.lean`): their `stack` is that
frame and the 944 bytes ECB's frame uses below it.
-/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.RISCV64

/-- How the functions compute Triple DES. -/
def desNote : String :=
  "The streaming functions call the verified key expansion (`vg_triple_des_expand_key`) and ECB \
  encryption (`vg_triple_des_ecb_encrypt`) on one block in place, the chaining value in the streaming \
  state, with the state as the key schedule."

/-- How the streaming functions are built. -/
def streamNote : String :=
  "The subkeys are derived from the enciphered zero block a byte at a time, each byte shifted left with \
  the top bit of the next entering on the right and the last XORed with `0x1b` under a mask made from the \
  top bit of the first; blocks are XORed into the chaining value and the bytes held back are copied a \
  byte at a time, since the contracts state no alignment for the data and `out`."

def artifacts : List Artifact := [
  Spec.Cmac.tdesStreamInitApi.artifact RISCV64.target {
    notes := [desNote, streamNote]
    code := Impl.StackScratch.RISCV64.withStackScratch 640 .a3 Impl.CmacTripleDes.Stream.RISCV64.streamInit
    stack := 1584
    verified := Proof.CmacTripleDes.Stream.RISCV64.init_framed },
  Spec.Cmac.tdesAbsorbApi.artifact RISCV64.target {
    notes := [desNote, streamNote]
    code := Impl.StackScratch.RISCV64.withStackScratch 688 .a4 Impl.CmacTripleDes.Stream.RISCV64.absorb
    stack := 1632
    verified := Proof.CmacTripleDes.Stream.RISCV64.absorb_framed },
  Spec.Cmac.tdesFinishApi.artifact RISCV64.target {
    notes := [desNote, streamNote]
    code := Impl.StackScratch.RISCV64.withStackScratch 640 .a3 Impl.CmacTripleDes.Stream.RISCV64.finish
    stack := 1584
    verified := Proof.CmacTripleDes.Stream.RISCV64.finish_framed }]

end VG.Artifacts.CmacTripleDes.RISCV64
