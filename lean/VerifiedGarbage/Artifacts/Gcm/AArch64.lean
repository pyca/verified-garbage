module

public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ghash
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# GHASH on AArch64

The PMULL implementation's suffix is `_aes`, like the AES instructions' (e.g.
`vg_aes_ctr32_aes`), since both need the one feature `aes` (FEAT_AES and
FEAT_PMULL; the Arm ARM's `ID_AA64ISAR0_EL1.AES` has no value for PMULL
without AES). With one suffix, a function calling both, such as AES-GCM, has
one variant for that feature, not one for each suffix and their combination.
-/

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
  Spec.Gcm.ghashWithPowersApi.artifact AArch64.target {
    suffix := "_aes"
    code := Impl.Gcm.AArch64.Pmull.ghashW
    verified := Proof.Gcm.AArch64.Pmull.ghashW_verified
    features := ["aes"] },
  Spec.Gcm.ghashStorePowersApi.artifact AArch64.target {
    suffix := "_aes"
    written := [("scratch", 0)]
    code := Impl.Gcm.AArch64.Pmull.ghashS
    verified := Proof.Gcm.AArch64.Pmull.ghashS_verified
    writtenOk := Proof.Gcm.AArch64.Pmull.ghashS_written
    features := ["aes"] }]

end VG.Artifacts.Gcm.AArch64
