module

public import VerifiedGarbage.Proof.Dsa.AArch64.ParameterSearchInit
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA parameter search on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Dsa.AArch64

def artifacts : List Artifact := [
  Spec.Dsa.parameterInitApi.artifact AArch64.target {
    code := Impl.Dsa.AArch64.ParameterSearch.init
    verified := Proof.Dsa.AArch64.ParameterSearchInit.init_verified }]

end VG.Artifacts.Dsa.AArch64
