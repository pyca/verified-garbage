module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Ofb
public import VerifiedGarbage.Spec.Blowfish.OfbFinal
import VerifiedGarbage.Impl.Blowfish.AArch64.Fn
import VerifiedGarbage.Proof.Blowfish.AArch64.FbVerified
import VerifiedGarbage.Proof.Blowfish.AArch64.FbFinalVerified
import VerifiedGarbage.Proof.Blowfish.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.AArch64.ModesLit
import VerifiedGarbage.Proof.Blowfish.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish-OFB on AArch64 -/

namespace VG.Artifacts.BlowfishOfb.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Blowfish.ofbApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.ofb
    verified := Proof.Blowfish.AArch64.ModesResidue.ofbCode_scrubbed },
  Spec.Blowfish.ofbFinalApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.ofbFinal
    verified := Proof.Blowfish.AArch64.ModesResidue.ofbFinalCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.BlowfishOfb.AArch64
