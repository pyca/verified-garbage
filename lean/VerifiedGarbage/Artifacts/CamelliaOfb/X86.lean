module

public import VerifiedGarbage.Proof.Camellia.X86.FbVerified
import VerifiedGarbage.Proof.Camellia.X86.FbLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-OFB artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.X86

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact X86.target {
    notes := ["Baseline IA-32: one block at a time (OFB is sequential), encrypted bitsliced in general-purpose registers, the S-boxes as Boolean circuits, with no table lookups, in a batch of eight of which the other seven are unused; the table of bitsliced subkeys is built once per call. The mode is the generic OFB of `Impl/Modes/X86/`, over Camellia's ECB core."]
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.ofb
    stack := 2756
    verified := Proof.Camellia.X86.Fb.ofb_framed }]

end VG.Artifacts.CamelliaOfb.X86
