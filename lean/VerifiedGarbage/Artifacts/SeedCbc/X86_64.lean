module

public import VerifiedGarbage.Impl.Seed.X86_64.Fn
public import VerifiedGarbage.Proof.Seed.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Seed.X86_64.ModesLit

/-! # SEED-CBC on x86-64 -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.X86_64

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.cbcEncrypt, verified := .scrubbed Proof.Seed.X86_64.Scrub.cbcEncrypt_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.cbcEncrypt_spSafe },
  Spec.Seed.cbcDecryptChainedApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.cbcDecrypt, verified := .scrubbed Proof.Seed.X86_64.Scrub.cbcDecrypt_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.cbcDecrypt_spSafe }]

end VG.Artifacts.SeedCbc.X86_64
