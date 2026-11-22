module

public import VerifiedGarbage.Proof.Sm4Gcm.X86.Scrub
public import VerifiedGarbage.Proof.AesGcm.X86.Scrub
public import VerifiedGarbage.Impl.Sm4Gcm.X86.Fn
public import VerifiedGarbage.Impl.AesGcm.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sm4.X86.Ctr32Lit
import VerifiedGarbage.Proof.Sm4.X86.Lit
public import VerifiedGarbage.Proof.AesGcm.X86.GhashImpls
public import VerifiedGarbage.Proof.Aes.X86.VariantProof
public import VerifiedGarbage.Proof.Variants.Ghash.X86
public import VerifiedGarbage.Proof.Variants.Sm4Ctr32.X86

/-! # SM4-GCM (NIST SP 800-38D, RFC 8998) on x86 -/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.X86

/-- `vg_sm4_gcm_init`, with each implementation of the key schedule and the
implementation of `vg_sm4_ctr32` chosen for it. -/
def keyed : List Artifact :=
  VG.Proof.Variants.Sm4Ctr32.X86.withExpandKey.map
    fun ((k, c) : Proof.Sm4Gcm.X86.KeyImpl × Proof.Sm4Gcm.X86.CtrImpl) =>
    Spec.Sm4.Gcm.initApi.artifact X86.target {
      suffix := k.suffix
      code := Impl.Sm4Gcm.X86.Fn.init k.fn c.fn
      verified := Proof.Sm4Gcm.X86.Scrub.init_scrubbed k c
      spSafe := Proof.Sm4Gcm.X86.Scrub.init_spSafeF k c }

end VG.Artifacts.Sm4Gcm.X86

-- SM4-GCM (NIST SP 800-38D, RFC 8998) on x86
namespace VG.Artifacts.Sm4Gcm.X86.Ghash

open VG.Proof.AesGcm.X86 (GcmImpl)

/-- The artifacts calling the implementation `v.gh` of `vg_ghash`, those
that encrypt with each implementation of `vg_sm4_ctr32`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.Sm4.Gcm.streamInitApi.artifact X86.target {
    suffix := v.gh.suffix
    code := Impl.AesGcm.X86.Fn.streamInit v.callees
    verified := Proof.AesGcm.X86.Scrub.streamInit_scrubbed v
    spSafe := Proof.AesGcm.X86.Scrub.streamInit_spSafeF v },
  Spec.Sm4.Gcm.streamAadApi.artifact X86.target {
    suffix := v.gh.suffix
    code := Impl.AesGcm.X86.Fn.streamAad v.callees
    verified := Proof.AesGcm.X86.Scrub.streamAad_scrubbed v
    spSafe := Proof.AesGcm.X86.Scrub.streamAad_spSafeF v }] ++
  VG.Proof.Variants.Sm4Ctr32.X86.variants.flatMap fun (c : Proof.Sm4Gcm.X86.CtrImpl) => [
    Spec.Sm4.Gcm.streamEncryptApi.artifact X86.target {
      suffix := c.suffix ++ v.gh.suffix
      code := Impl.Sm4Gcm.X86.Fn.streamEncrypt v.callees c.fn
      verified := Proof.Sm4Gcm.X86.Scrub.streamEncrypt_scrubbed v c
      spSafe := Proof.Sm4Gcm.X86.Scrub.streamEncrypt_spSafeF v c },
    Spec.Sm4.Gcm.streamDecryptApi.artifact X86.target {
      suffix := c.suffix ++ v.gh.suffix
      code := Impl.Sm4Gcm.X86.Fn.streamDecrypt v.callees c.fn
      verified := Proof.Sm4Gcm.X86.Scrub.streamDecrypt_scrubbed v c
      spSafe := Proof.Sm4Gcm.X86.Scrub.streamDecrypt_spSafeF v c },
    Spec.Sm4.Gcm.streamFinishApi.artifact X86.target {
      suffix := c.suffix ++ v.gh.suffix
      code := Impl.Sm4Gcm.X86.Fn.streamFinish v.callees c.fn
      verified := Proof.Sm4Gcm.X86.Scrub.streamFinish_scrubbed v c
      spSafe := Proof.Sm4Gcm.X86.Scrub.streamFinish_spSafeF v c },
    Spec.Sm4.Gcm.streamVerifyApi.artifact X86.target {
      suffix := c.suffix ++ v.gh.suffix
      code := Impl.Sm4Gcm.X86.Fn.streamVerify v.callees c.fn
      verified := Proof.Sm4Gcm.X86.Scrub.streamVerify_scrubbed v c
      spSafe := Proof.Sm4Gcm.X86.Scrub.streamVerify_spSafeF v c },
    Spec.Sm4.Gcm.sealApi.artifact X86.target {
      suffix := c.suffix ++ v.gh.suffix
      code := Impl.Sm4Gcm.X86.Fn.«seal» v.callees c.fn
      verified := Proof.Sm4Gcm.X86.Scrub.seal_scrubbed v c
      spSafe := Proof.Sm4Gcm.X86.Scrub.seal_spSafeF v c },
    Spec.Sm4.Gcm.openApi.artifact X86.target {
      suffix := c.suffix ++ v.gh.suffix
      code := Impl.Sm4Gcm.X86.Fn.«open» v.callees c.fn
      verified := Proof.Sm4Gcm.X86.Scrub.open_scrubbed v c
      spSafe := Proof.Sm4Gcm.X86.Scrub.open_spSafeF v c }]

/-- The artifacts of a variant, from the implementation of `vg_ghash` it names. -/
def artifacts (v : Proof.AesGcm.X86.GhashName) : List Artifact :=
  artifactsOf (Proof.AesGcm.X86.GcmImpl.mk Proof.Aes.X86.Ctr32Impl.scalar v.impl)

end VG.Artifacts.Sm4Gcm.X86.Ghash

namespace VG.Artifacts.Sm4Gcm.X86

def artifacts : List Artifact :=
  keyed ++
  (VG.Proof.Variants.Ghash.X86.variants.flatMap fun v => Ghash.artifacts v)

end VG.Artifacts.Sm4Gcm.X86
