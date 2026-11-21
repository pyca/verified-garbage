module

public import VerifiedGarbage.Proof.Sm3.X86.Scrub
public import VerifiedGarbage.Impl.Sm3.X86.Stream
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sm3.X86.Lit

/-! # SM3 (GB/T 32905-2016) on x86 -/

@[expose] public section

namespace VG.Artifacts.Sm3.X86

def artifacts : List Artifact := [
  Spec.Sm3.initApi.artifact X86.target {
    code := Impl.Sm3.X86.Fn.init
    verified := Proof.Sm3.X86.Scrub.init_scrubbed },
  Spec.Sm3.updateApi.artifact X86.target {
    code := Impl.Sm3.X86.Fn.update
    verified := Proof.Sm3.X86.Scrub.update_scrubbed },
  Spec.Sm3.finalizeApi.artifact X86.target {
    code := Impl.Sm3.X86.Fn.finalize
    verified := Proof.Sm3.X86.Scrub.finalize_scrubbed }]

end VG.Artifacts.Sm3.X86
