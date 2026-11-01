module

public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ghash
public import VerifiedGarbage.Proof.Framework.Registration

/-! # GHASH on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Gcm.AArch64

def artifacts : List Artifact := [
  Spec.Gcm.ghashStorePowersApi.artifact AArch64.target {
    suffix := "_aes"
    written := [("scratch", 0)]
    code := Impl.Gcm.AArch64.Pmull.ghashS
    verified := Proof.Gcm.AArch64.Pmull.ghashS_verified
    writtenOk := Proof.Gcm.AArch64.Pmull.ghashS_written
    features := ["aes"] }]

end VG.Artifacts.Gcm.AArch64
