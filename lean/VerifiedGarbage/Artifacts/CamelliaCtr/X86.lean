module

public import VerifiedGarbage.Proof.Camellia.X86.Scrub
public import VerifiedGarbage.Impl.Camellia.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Camellia.X86.CtrLit

/-! # Camellia-CTR on x86 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.X86

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact X86.target {
    code := Impl.Camellia.X86.Fn.ctr
    verified := Proof.Camellia.X86.Scrub.ctr_scrubbed },
  Spec.Camellia.ctrFinalApi.artifact X86.target {
    code := Impl.Camellia.X86.Fn.ctrFinal
    verified := Proof.Camellia.X86.Scrub.ctrFinal_scrubbed }]

end VG.Artifacts.CamelliaCtr.X86
