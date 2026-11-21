module

public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Seed.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesLit

/-! # SEED-CBC on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.PPC64LE

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.cbcEncryptChained
    verified := Proof.Seed.PPC64LE.Scrub.cbcEncryptChained_scrubbed },
  Spec.Seed.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.cbcDecryptChained
    verified := Proof.Seed.PPC64LE.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.SeedCbc.PPC64LE
