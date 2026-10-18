module

public import VerifiedGarbage.Proof.Sm4.X86_64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit

/-! # SM4-OFB artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ofb.X86_64

/-- How the functions compute SM4, and the mode. -/
def note : String :=
  "Baseline x86-64: one block at a time (each block's input depends on the block before), encrypted bitsliced in \
  general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table \
  lookups, in a batch of sixteen of which the other fifteen are unused; the key schedule's table of round keys is \
  built once per call, inline, and each batch is a call of `vg_sm4_crypt_prepared`. The mode is the generic OFB of `Impl/Modes/X86_64/`, over SM4's ECB core."

def artifacts : List Artifact := [
  Spec.Sm4.ofbApi.artifact X86_64.target {
    notes := [note]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ofb
    stack := 3216
    verified := Proof.Sm4.X86_64.ofb_framed }]

end VG.Artifacts.Sm4Ofb.X86_64
