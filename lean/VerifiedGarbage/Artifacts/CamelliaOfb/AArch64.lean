module

public import VerifiedGarbage.Impl.Camellia.AArch64.Fn
public import VerifiedGarbage.Proof.Camellia.AArch64.FbVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Camellia.AArch64.FbLit
import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalLit

/-! # Camellia-OFB on AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.AArch64

def artifacts : List (Artifact AArch64.target) := [
  Spec.Camellia.ofbApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.ofb
    verified := Proof.Camellia.AArch64.Residue.ofbCode_scrubbed },
  Spec.Camellia.ofbFinalApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.ofbFinal
    verified := Proof.Camellia.AArch64.Residue.ofbFinalCode_scrubbed }]

end VG.Artifacts.CamelliaOfb.AArch64
