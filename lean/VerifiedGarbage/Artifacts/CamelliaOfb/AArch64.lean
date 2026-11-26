module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Ofb
public import VerifiedGarbage.Spec.Camellia.OfbFinal
import VerifiedGarbage.Impl.Camellia.AArch64.Fn
import VerifiedGarbage.Proof.Camellia.AArch64.FbVerified
import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalVerified
import VerifiedGarbage.Proof.Camellia.AArch64.Residue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.AArch64.FbLit
import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-OFB on AArch64 -/

namespace VG.Artifacts.CamelliaOfb.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Camellia.ofbApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.ofb
    verified := Proof.Camellia.AArch64.Residue.ofbCode_scrubbed },
  Spec.Camellia.ofbFinalApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.ofbFinal
    verified := Proof.Camellia.AArch64.Residue.ofbFinalCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.CamelliaOfb.AArch64
