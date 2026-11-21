module

public import VerifiedGarbage.Proof.Sm4.X86_64.Ctr32Verified
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Sm4.X86_64.Ctr32Lit
public import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
public import VerifiedGarbage.Proof.AesGcm.X86_64.Scrub
public import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls
public import VerifiedGarbage.Proof.Aes.X86_64.Variant
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Variants.Ghash.X86_64

/-! # SM4-GCM (NIST SP 800-38D, RFC 8998) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.X86_64

def direct : List Artifact := [Spec.Sm4.Gcm.initApi.artifact X86_64.target {
  code := Impl.Sm4Gcm.X86_64.Fn.init
  verified := Proof.Sm4Gcm.X86_64.init_scrubbed
  spSafe := Proof.Sm4Gcm.X86_64.init_spSafeFn }]

end VG.Artifacts.Sm4Gcm.X86_64

-- SM4-GCM (NIST SP 800-38D, RFC 8998) on x86-64
namespace VG.Artifacts.Sm4Gcm.X86_64.Ghash

open VG.Proof.AesGcm.X86_64 (GcmImpl GhashName KeyImpl)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.Sm4Gcm.X86_64
open VG.Proof.AesGcm.X86_64.Scrub (gcmOf ghOf)

/-- The artifacts calling the implementation `n` of `vg_ghash`. -/
def artifacts (n : GhashName) : List Artifact :=
  let v : GcmImpl := { ctr := Ctr32Impl.scalar, key := KeyImpl.scalar, gh := n.impl }
  [Spec.Sm4.Gcm.sealApi.artifact X86_64.target {
    suffix := v.gh.suffix
    code := Impl.Sm4Gcm.X86_64.Fn.«seal» (sm4Level v) v.callees
    verified := Proof.Sm4Gcm.X86_64.seal_scrubbed v
    spSafe := Proof.Sm4Gcm.X86_64.seal_spSafeFn v },
  Spec.Sm4.Gcm.openApi.artifact X86_64.target {
    suffix := v.gh.suffix
    code := Impl.Sm4Gcm.X86_64.Fn.«open» (sm4Level v) v.callees
    verified := Proof.Sm4Gcm.X86_64.open_scrubbed v
    spSafe := Proof.Sm4Gcm.X86_64.open_spSafeFn v },
  Spec.Sm4.Gcm.streamInitApi.artifact X86_64.target
    (match (ghOf n).gh.free with
    | some f =>
      { suffix := n.impl.suffix
        code := Impl.AesGcm.X86_64.Fn.streamInit ((ghOf n).lv .sse) 240 (ghOf n).callees
        verified := Proof.AesGcm.X86_64.Scrub.sm4StreamInitF_scrubbed n f
        spSafe := Proof.AesGcm.X86_64.Scrub.sm4StreamInitF_spSafeFn n }
    | none =>
      { suffix := n.impl.suffix
        code := Impl.AesGcm.X86_64.Fn.streamInit ((ghOf n).lv .sse) 784 (ghOf n).callees
        verified := Proof.AesGcm.X86_64.Scrub.sm4StreamInit_scrubbed n
        spSafe := Proof.AesGcm.X86_64.Scrub.sm4StreamInit_spSafeFn n }),
  Spec.Sm4.Gcm.streamAadApi.artifact X86_64.target
    (match (ghOf n).gh.free with
    | some f =>
      { suffix := n.impl.suffix
        code := Impl.AesGcm.X86_64.Fn.streamAad ((ghOf n).lv .sse) 192 (ghOf n).callees
        verified := Proof.AesGcm.X86_64.Scrub.sm4StreamAadF_scrubbed n f
        spSafe := Proof.AesGcm.X86_64.Scrub.sm4StreamAadF_spSafeFn n }
    | none =>
      { suffix := n.impl.suffix
        code := Impl.AesGcm.X86_64.Fn.streamAad ((ghOf n).lv .sse) 784 (ghOf n).callees
        verified := Proof.AesGcm.X86_64.Scrub.sm4StreamAad_scrubbed n
        spSafe := Proof.AesGcm.X86_64.Scrub.sm4StreamAad_spSafeFn n }),
  Spec.Sm4.Gcm.streamEncryptApi.artifact X86_64.target {
    suffix := v.gh.suffix
    code := Impl.Sm4Gcm.X86_64.Fn.streamEncrypt (sm4Level v) v.callees
    verified := Proof.Sm4Gcm.X86_64.streamEncrypt_scrubbed v
    spSafe := Proof.Sm4Gcm.X86_64.streamEncrypt_spSafeFn v },
  Spec.Sm4.Gcm.streamDecryptApi.artifact X86_64.target {
    suffix := v.gh.suffix
    code := Impl.Sm4Gcm.X86_64.Fn.streamDecrypt (sm4Level v) v.callees
    verified := Proof.Sm4Gcm.X86_64.streamDecrypt_scrubbed v
    spSafe := Proof.Sm4Gcm.X86_64.streamDecrypt_spSafeFn v },
  Spec.Sm4.Gcm.streamFinishApi.artifact X86_64.target {
    suffix := v.gh.suffix
    code := Impl.Sm4Gcm.X86_64.Fn.streamFinish (sm4Level v) v.callees
    verified := Proof.Sm4Gcm.X86_64.streamFinish_scrubbed v
    spSafe := Proof.Sm4Gcm.X86_64.streamFinish_spSafeFn v },
  Spec.Sm4.Gcm.streamVerifyApi.artifact X86_64.target {
    suffix := v.gh.suffix
    code := Impl.Sm4Gcm.X86_64.Fn.streamVerify (sm4Level v) v.callees
    verified := Proof.Sm4Gcm.X86_64.streamVerify_scrubbed v
    spSafe := Proof.Sm4Gcm.X86_64.streamVerify_spSafeFn v }]

end VG.Artifacts.Sm4Gcm.X86_64.Ghash

namespace VG.Artifacts.Sm4Gcm.X86_64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.Ghash.X86_64.variants.flatMap fun v => Ghash.artifacts v)

end VG.Artifacts.Sm4Gcm.X86_64
