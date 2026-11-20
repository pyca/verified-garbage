module

public import VerifiedGarbage.Impl.Camellia.X86_64.Fn
public import VerifiedGarbage.Proof.Camellia.X86_64.CtrVerified
public import VerifiedGarbage.Proof.Camellia.X86_64.CtrFinal
public import VerifiedGarbage.Proof.Camellia.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit

/-! # Camellia-CTR on x86-64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.X86_64

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.ctr, verified := .scrubbed Proof.Camellia.X86_64.Scrub.ctr_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.ctr_spSafe },
  Spec.Camellia.ctrFinalApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.ctrFinal, verified := .scrubbed Proof.Camellia.X86_64.Scrub.ctrFinal_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.ctrFinal_spSafe }]

end VG.Artifacts.CamelliaCtr.X86_64
