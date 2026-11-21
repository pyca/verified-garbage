module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Sm4.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit

/-! # SM4-OFB on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sm4Ofb.PPC64LE

def artifacts : List Artifact := [
  Spec.Sm4.ofbApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.ofb
    verified := Proof.Sm4.PPC64LE.Scrub.ofb_scrubbed },
  Spec.Sm4.ofbFinalApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.ofbFinal
    verified := Proof.Sm4.PPC64LE.Scrub.ofbFinal_scrubbed }]

end VG.Artifacts.Sm4Ofb.PPC64LE
