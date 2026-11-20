module

public import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Frame
public import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.X86_64.Key
public import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Chained
public import VerifiedGarbage.Proof.Rc2.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Lit

/-! # RC2 on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Rc2.X86_64

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact X86_64.target {
    code := Impl.Rc2.X86_64.Fn.cbcInit
    verified := .scrubbed Proof.Rc2.X86_64.Scrub.cbcInit_scrubbed },
  Spec.Rc2.cbcEncryptChainedApi.artifact X86_64.target {
    code := Impl.Rc2.X86_64.Fn.cbcEncryptChained
    verified := .scrubbed Proof.Rc2.X86_64.Scrub.cbcEncryptChained_scrubbed },
  Spec.Rc2.cbcDecryptChainedApi.artifact X86_64.target {
    code := Impl.Rc2.X86_64.Fn.cbcDecryptChained
    verified := .scrubbed Proof.Rc2.X86_64.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.Rc2.X86_64
