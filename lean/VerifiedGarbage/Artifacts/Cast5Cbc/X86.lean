module

public import VerifiedGarbage.Proof.Cast5.X86.Scrub
public import VerifiedGarbage.Impl.Cast5.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Cast5.X86.ModesLit

/-! # CAST5-CBC on x86 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.X86

def artifacts : List Artifact := [
  Spec.Cast5.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.cbcEncryptChained
    verified := Proof.Cast5.X86.Scrub.cbcEncryptChained_scrubbed },
  Spec.Cast5.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.cbcDecryptChained
    verified := Proof.Cast5.X86.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.Cast5Cbc.X86
