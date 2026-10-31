module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit

/-! # Camellia-OFB artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.ofb
    stack := 3408
    verified := Proof.Camellia.PPC64LE.ofb_framed Proof.Camellia.PPC64LE.Modes.ofb_verified }]

end VG.Artifacts.CamelliaOfb.PPC64LE
