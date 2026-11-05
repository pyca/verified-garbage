module

public import VerifiedGarbage.Proof.Dsa.X86_64.ParameterSearchInit
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA parameter search on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Dsa.X86_64

def artifacts : List Artifact := [
  Spec.Dsa.parameterInitApi.artifact X86_64.target {
    code := Impl.Dsa.X86_64.ParameterSearch.init
    verified := Proof.Dsa.X86_64.ParameterSearchInit.init_verified }]

end VG.Artifacts.Dsa.X86_64
