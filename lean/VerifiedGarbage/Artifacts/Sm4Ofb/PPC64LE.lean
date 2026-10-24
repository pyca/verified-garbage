module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit

/-! # SM4-OFB artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sm4Ofb.PPC64LE

/-- How the functions compute SM4, and the mode. -/
def note : String :=
  "Baseline PPC64LE: one block at a time, bitsliced in general-purpose registers through the AES \
  S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups, in a batch of sixteen \
  of which the other fifteen are unused: the table of round keys is built once per call, by a call \
  of `vg_sm4_prepare_keys`, and each block is a call of `vg_sm4_crypt_prepared`. The mode is the \
  generic OFB of `Impl/Modes/PPC64LE/`, which keeps its state in `r29`–`r31`; the prepared \
  functions save them in the working space and restore them."

def artifacts : List Artifact := [
  Spec.Sm4.ofbApi.artifact PPC64LE.target {
    notes := [note]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.ofb
    stack := 3296
    verified := Proof.Sm4.PPC64LE.ofb_framed Proof.Sm4.PPC64LE.Modes.ofb_verified }]

end VG.Artifacts.Sm4Ofb.PPC64LE
