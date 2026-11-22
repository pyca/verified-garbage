module

public import VerifiedGarbage.Proof.Camellia.X86.Scrub
public import VerifiedGarbage.Impl.Camellia.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Camellia.X86.CtrLit
public import VerifiedGarbage.Proof.Variants.CamelliaCtr.X86

/-! # Camellia-CTR on x86 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.X86

/-- `vg_camellia_ctr_final`, with each implementation of `vg_camellia_ctr`'s code. -/
def finals : List Artifact :=
  VG.Proof.Variants.CamelliaCtr.X86.variants.map fun (c : Proof.Camellia.X86.CtrFinal.CtrImpl) =>
    Spec.Camellia.ctrFinalApi.artifact X86.target {
      suffix := c.suffix
      code := Impl.Camellia.X86.Fn.ctrFinal c.name c.code c.words
      verified := Proof.Camellia.X86.Scrub.ctrFinal_scrubbed c
      spSafe := Proof.Camellia.X86.Scrub.ctrFinal_spSafeF c }

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact X86.target {
    code := Impl.Camellia.X86.Fn.ctr
    verified := Proof.Camellia.X86.Scrub.ctr_scrubbed }] ++ finals

end VG.Artifacts.CamelliaCtr.X86
