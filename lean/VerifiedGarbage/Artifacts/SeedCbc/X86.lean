module

public import VerifiedGarbage.Proof.Seed.X86.Scrub
public import VerifiedGarbage.Impl.Seed.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Seed.X86.CbcLit

/-! # SEED-CBC on x86 -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.X86

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.Seed.X86.Fn.cbcEncryptChained
    verified := .scrubbed Proof.Seed.X86.Scrub.cbcEncryptChained_scrubbed },
  Spec.Seed.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.Seed.X86.Fn.cbcDecryptChained
    verified := .scrubbed Proof.Seed.X86.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.SeedCbc.X86
