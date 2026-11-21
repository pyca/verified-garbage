module

public import VerifiedGarbage.Impl.Sm3.X86_64.Fn
public import VerifiedGarbage.Proof.Sm3.X86_64.Shared
public import VerifiedGarbage.Proof.Sm3.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Sm3.X86_64.Lit

/-! # SM3 (GB/T 32905-2016) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sm3.X86_64

def artifacts : List Artifact := [
  Spec.Sm3.initApi.artifact X86_64.target { code := Impl.Sm3.X86_64.Fn.init, verified := Proof.Sm3.X86_64.init_scrubbed, spSafe := Proof.Sm3.X86_64.init_spSafe },
  Spec.Sm3.updateApi.artifact X86_64.target { code := Impl.Sm3.X86_64.Fn.update, verified := Proof.Sm3.X86_64.update_scrubbed, spSafe := Proof.Sm3.X86_64.update_spSafe },
  Spec.Sm3.finalizeApi.artifact X86_64.target { code := Impl.Sm3.X86_64.Fn.finalize, verified := Proof.Sm3.X86_64.finalize_scrubbed, spSafe := Proof.Sm3.X86_64.finalize_spSafe }]

end VG.Artifacts.Sm3.X86_64
