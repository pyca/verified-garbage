module

public import VerifiedGarbage.Impl.TripleDes.AArch64.Fn
public import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
public import VerifiedGarbage.Proof.TripleDes.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.TripleDes.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.TripleDes.AArch64.FbLit
import VerifiedGarbage.Proof.TripleDes.AArch64.FbFinalLit

/-! # Triple DES-OFB on AArch64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.AArch64

def artifacts : List Artifact := [
  Spec.TripleDes.ofbApi.artifact AArch64.target {
    code := Impl.TripleDes.AArch64.Fn.ofb
    verified := Proof.TripleDes.AArch64.ModesResidue.ofbCode_scrubbed },
  Spec.TripleDes.ofbFinalApi.artifact AArch64.target {
    code := Impl.TripleDes.AArch64.Fn.ofbFinal
    verified := Proof.TripleDes.AArch64.ModesResidue.ofbFinalCode_scrubbed }]

end VG.Artifacts.TripleDesOfb.AArch64
