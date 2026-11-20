module

public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Seed.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Seed.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Seed.PPC64LE.FbFinalLit

/-! # SEED-CFB128 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.cfbEncrypt
    verified := .scrubbed Proof.Seed.PPC64LE.Scrub.cfbEncrypt_scrubbed },
  Spec.Seed.cfbDecryptApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.cfbDecrypt
    verified := .scrubbed Proof.Seed.PPC64LE.Scrub.cfbDecrypt_scrubbed },
  Spec.Seed.cfbEncryptFinalApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.cfbEncryptFinal
    verified := .scrubbed Proof.Seed.PPC64LE.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Seed.cfbDecryptFinalApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.cfbDecryptFinal
    verified := .scrubbed Proof.Seed.PPC64LE.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.SeedCfb.PPC64LE
