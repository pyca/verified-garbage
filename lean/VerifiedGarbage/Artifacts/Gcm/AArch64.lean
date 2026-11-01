module

public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ghash
public import VerifiedGarbage.Proof.Framework.Registration

/-! # GHASH on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Gcm.AArch64

def artifacts : List Artifact := [
  Spec.Gcm.ghashApi.artifact AArch64.target {
    code := Impl.Gcm.AArch64.ghash
    verified := Proof.Gcm.AArch64.ghash_verified },
  Spec.Gcm.ghashApi.artifact AArch64.target {
    suffix := "_aes"
    code := Impl.Gcm.AArch64.Pmull.ghash
    verified := Proof.Gcm.AArch64.Pmull.ghash_verified
    features := ["aes"] },
  Spec.Gcm.ghashStorePowersApi.artifact AArch64.target {
    suffix := "_aes"
    written := [("scratch", 0)]
    code := Impl.Gcm.AArch64.Pmull.ghashS
    verified := Proof.Gcm.AArch64.Pmull.ghashS_verified
    writtenOk := Proof.Gcm.AArch64.Pmull.ghashS_written
    features := ["aes"] }]

end VG.Artifacts.Gcm.AArch64
