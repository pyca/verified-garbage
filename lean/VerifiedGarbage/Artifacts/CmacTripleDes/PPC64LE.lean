module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Lit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit

/-!
# TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on baseline PPC64LE

The functions call the verified key expansion and block function, keeping
the return address in the link register, and keep their working space in a
frame of their own on the stack
(`Proof/CmacTripleDes/Stream/PPC64LE/Frame.lean`).
-/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.PPC64LE

/-- How the functions compute Triple DES. -/
def desNote : String :=
  "Baseline PPC64LE: the streaming functions call the verified key expansion \
  (`vg_triple_des_expand_key`) and block function (`vg_triple_des_encrypt_block`), with Boolean \
  S-box circuits and no table lookups, one block at a time, reading the schedule in the streaming state."

/-- How the streaming functions are built. -/
def streamNote : String :=
  "The subkeys are derived from the enciphered zero block with a shift and an XOR under a mask made \
  from the top bit; the bytes held back are copied one at a time, and `absorb` keeps what it counts \
  across the block function's calls in `r29`–`r31`, which it saves in its working space."

def artifacts : List Artifact := [
  Spec.Cmac.tdesStreamInitApi.artifact PPC64LE.target {
    notes := [desNote, streamNote]
    code := Impl.StackScratch.PPC64LE.withStackScratch 672 .r6 Impl.CmacTripleDes.Stream.PPC64LE.streamInit
    stack := 672
    verified := Proof.CmacTripleDes.Stream.PPC64LE.init_framed },
  Spec.Cmac.tdesAbsorbApi.artifact PPC64LE.target {
    notes := [desNote, streamNote]
    code := Impl.StackScratch.PPC64LE.withStackScratch 720 .r7 Impl.CmacTripleDes.Stream.PPC64LE.absorb
    stack := 720
    verified := Proof.CmacTripleDes.Stream.PPC64LE.absorb_framed },
  Spec.Cmac.tdesFinishApi.artifact PPC64LE.target {
    notes := [desNote, streamNote]
    code := Impl.StackScratch.PPC64LE.withStackScratch 672 .r6 Impl.CmacTripleDes.Stream.PPC64LE.finish
    stack := 672
    verified := Proof.CmacTripleDes.Stream.PPC64LE.finish_framed }]

end VG.Artifacts.CmacTripleDes.PPC64LE
