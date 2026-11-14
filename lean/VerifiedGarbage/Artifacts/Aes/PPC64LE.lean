module

public import VerifiedGarbage.Proof.Aes.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES (FIPS 197) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Aes.PPC64LE

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.expandKey
    verified := Proof.Aes.PPC64LE.expandKey_direct_verified }]

end VG.Artifacts.Aes.PPC64LE
