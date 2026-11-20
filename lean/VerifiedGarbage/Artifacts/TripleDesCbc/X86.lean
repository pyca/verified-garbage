module

public import VerifiedGarbage.Proof.TripleDes.X86.Scrub
public import VerifiedGarbage.Impl.TripleDes.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.TripleDes.X86.CbcLit

/-! # Triple DES-CBC on x86 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.X86

def artifacts : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.cbcEncryptChained
    verified := .scrubbed Proof.TripleDes.X86.Scrub.cbcEncryptChained_scrubbed },
  Spec.TripleDes.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.cbcDecryptChained
    verified := .scrubbed Proof.TripleDes.X86.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.TripleDesCbc.X86
