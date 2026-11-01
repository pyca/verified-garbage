module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Ghash
public import VerifiedGarbage.Proof.Framework.Registration

import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Lit

/-! # GHASH on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Gcm.PPC64LE

def artifacts : List Artifact := [
  Spec.Gcm.ghashApi.artifact PPC64LE.target {
    code := Impl.Gcm.PPC64LE.Vpmsum.ghash
    verified := Proof.Gcm.PPC64LE.Vpmsum.ghash_verified }]

end VG.Artifacts.Gcm.PPC64LE
