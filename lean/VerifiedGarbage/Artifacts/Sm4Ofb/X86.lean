module

public import VerifiedGarbage.Proof.Sm4.X86.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86.FbLit

/-! # SM4-OFB artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Sm4Ofb.X86

/-- How the function computes SM4, and the mode. -/
def note : String :=
  "Baseline IA-32: one block at a time (each output block is the encryption of the one before), encrypted \
  bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), \
  with no table lookups, in a batch of eight of which the other seven are unused; the key schedule's table of round \
  keys is built once per call. The mode is the generic OFB of `Impl/Modes/X86/`, over SM4's ECB core."

def artifacts : List Artifact := [
  Spec.Sm4.ofbApi.artifact X86.target {
    notes := [note]
    code := Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.ofb
    stack := 1516
    verified := Proof.Sm4.X86.Fb.ofb_framed }]

end VG.Artifacts.Sm4Ofb.X86
