module

public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ghash
public import VerifiedGarbage.Proof.AesGcm.AArch64.Prepared.Verified
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
    notes := ["`•` is computed bit by bit as Algorithm 1 of §6.3 does, with masks instead of \
        branches."]
    code := Impl.Gcm.AArch64.ghash
    verified := Proof.Gcm.AArch64.ghash_verified },
  Spec.Gcm.ghashApi.artifact AArch64.target {
    suffix := "_aes"
    notes := ["Uses PMULL: eight blocks at a time, with `H²` to `H⁸` computed on each call \
        that has at least eight blocks, then four, two and one."]
    code := Impl.Gcm.AArch64.Pmull.ghash
    verified := Proof.Gcm.AArch64.Pmull.ghash_verified
    features := ["aes"] },
  Spec.Gcm.ghashWithPowersApi.artifact AArch64.target {
    suffix := "_aes"
    notes := ["Uses PMULL as `vg_ghash_aes` does, loading `H'` to `H'⁸` (`H'ᵏ = Hᵏ · x⁻¹`) from `pw` \
        instead of computing them."]
    code := Impl.Gcm.AArch64.Pmull.ghashW
    verified := Proof.Gcm.AArch64.Pmull.ghashW_verified
    features := ["aes"] },
  Spec.Gcm.derivePrepared8Api.artifact AArch64.target {
    suffix := "_aes"
    notes := ["Uses PMULL: copies the key context, then computes `H'` to `H'⁸` (`H'ᵏ = Hᵏ · x⁻¹`) \
        from its hash subkey and stores them after it, as `vg_ghash_with_powers_aes` reads them."]
    code := Impl.AesGcm.AArch64.Prepared.derive
    verified := Proof.AesGcm.AArch64.derive_verified Proof.Gcm.AArch64.Pmull.prepPow
    features := ["aes"] }]

end VG.Artifacts.Gcm.AArch64
