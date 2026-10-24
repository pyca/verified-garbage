module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesLit

/-! # CAST5-OFB artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.PPC64LE

/-- How the function computes CAST5, and the mode. -/
def note : String :=
  "Baseline PPC64LE: one block at a time, through the generic modes of `Impl/Modes/PPC64LE/` over \
  CAST5's ECB block function (inlined): each S-box lookup is a scan of the whole table in the static \
  `VG_CAST5_S1234`, so no secret is an address. The subkeys are read where the caller passed them; the \
  public number of rounds chooses one of two copies of the mode, each with its count fixed. The modes' \
  r29 and r30, which the block function uses, are kept in r6 and r7 meanwhile, and our caller's r14-r28 \
  in the 176-byte working space on the stack, which is zeroed on return."

def artifacts : List Artifact := [
  Spec.Cast5.ofbApi.artifact PPC64LE.target {
    notes := [note]
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.ofb
    stack := 208
    verified := Proof.Cast5.PPC64LE.Modes.ofb_framed }]

end VG.Artifacts.Cast5Ofb.PPC64LE
