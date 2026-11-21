module

public import VerifiedGarbage.Impl.Seed.X86_64.Fn
public import VerifiedGarbage.Proof.Seed.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Seed.X86_64.ModesLit
import VerifiedGarbage.Proof.Seed.X86_64.FbFinalLit

/-! # SEED-CFB128 on x86-64 -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.X86_64

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.cfbEncrypt, verified := .scrubbed Proof.Seed.X86_64.Scrub.cfbEncrypt_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.cfbEncrypt_spSafe },
  Spec.Seed.cfbDecryptApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.cfbDecrypt, verified := .scrubbed Proof.Seed.X86_64.Scrub.cfbDecrypt_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.cfbDecrypt_spSafe },
  Spec.Seed.cfbEncryptFinalApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.cfbEncryptFinal, verified := .scrubbed Proof.Seed.X86_64.Scrub.cfbEncryptFinal_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.cfbEncryptFinal_spSafe },
  Spec.Seed.cfbDecryptFinalApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.cfbDecryptFinal, verified := .scrubbed Proof.Seed.X86_64.Scrub.cfbDecryptFinal_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.cfbDecryptFinal_spSafe }]

end VG.Artifacts.SeedCfb.X86_64
