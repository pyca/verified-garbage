module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Instances
public import VerifiedGarbage.Proof.Aes.X86_64.Variant
public import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86_64
public import VerifiedGarbage.Proof.Variants.Ghash.X86_64
public import VerifiedGarbage.Proof.Gcm.X86_64.PrepareScrub
public import VerifiedGarbage.Proof.AesGcm.X86_64.Scrub
public import VerifiedGarbage.Proof.AesGcm.X86_64.Leaves
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Short
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Gather
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.StreamTo
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.BlocksVerified
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerifiedP
public import VerifiedGarbage.Proof.Variants.AesGcm.X86_64
import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.Lit
public import VerifiedGarbage.Proof.Gcm.X86_64.Ghash
public import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Ghash
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
public import VerifiedGarbage.Proof.Gcm.X86_64.PrepareZ
public import VerifiedGarbage.Proof.Gcm.X86_64.PrepareAvx.Ok
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepare16

/-! # AES-GCM (NIST SP 800-38D) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.AesGcm.X86_64.AesCtr32Ghash

open VG.Proof.AesGcm.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The artifacts calling the implementation `c` of `vg_aes_ctr32` and `n` of
`vg_ghash`, a pair that a variant of AES-GCM calls (`streamPairs`). -/
def artifacts (c : Ctr32Impl) (n : GhashName) : List Artifact := [
  Spec.Gcm.streamFinishApi.artifact X86_64.target (Proof.AesGcm.X86_64.Scrub.streamFinishReg c n),
  Spec.Gcm.streamVerifyApi.artifact X86_64.target (Proof.AesGcm.X86_64.Scrub.streamVerifyReg c n)]

end VG.Artifacts.AesGcm.X86_64.AesCtr32Ghash

-- AES-GCM's AES-only function on x86-64: `vg_aes_gcm_init`
namespace VG.Artifacts.AesGcm.X86_64.AesCtr32

open VG.Proof.AesGcm.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The artifacts calling the implementation `c` of `vg_aes_ctr32`, with the
key expansion for the same CPUs, and no GHASH. -/
def artifacts (c : Ctr32Impl) : List Artifact :=
  [Spec.Gcm.initApi.artifact X86_64.target (Proof.AesGcm.X86_64.Scrub.initReg c)]

end VG.Artifacts.AesGcm.X86_64.AesCtr32

-- AES-GCM (NIST SP 800-38D) on x86-64
namespace VG.Artifacts.AesGcm.X86_64.AesGcm

open VG.Proof.AesGcm.X86_64

/-- The prepared artifacts of the implementations `v` whose loops read the
48 prepared powers: by the flag, those or the ones on the key context. -/
def artifactsR (v : GcmVariant) : List Artifact := [
  Spec.Gcm.sealPreparedApi.artifact X86_64.target (sealPrepR v),
  Spec.Gcm.openPreparedApi.artifact X86_64.target (openPrepR v),
  Spec.Gcm.openToPreparedApi.artifact X86_64.target (openToPrepR v),
  Spec.Gcm.streamEncryptPreparedApi.artifact X86_64.target (streamEncryptPrepR v),
  Spec.Gcm.streamDecryptPreparedApi.artifact X86_64.target (streamDecryptPrepR v),
  Spec.Gcm.sealGatherPreparedApi.artifact X86_64.target (sealGatherPrepR v)]

/-- The prepared artifacts of the implementations `v`, which read only the
key context. -/
def artifactsW (v : GcmVariant) : List Artifact := [
  Spec.Gcm.sealPreparedApi.artifact X86_64.target (sealPrepW v),
  Spec.Gcm.openPreparedApi.artifact X86_64.target (openPrepW v),
  Spec.Gcm.openToPreparedApi.artifact X86_64.target (openToPrepW v),
  Spec.Gcm.streamEncryptPreparedApi.artifact X86_64.target (streamEncryptPrepW v),
  Spec.Gcm.streamDecryptPreparedApi.artifact X86_64.target (streamDecryptPrepW v),
  Spec.Gcm.sealGatherPreparedApi.artifact X86_64.target (sealGatherPrepW v)]

/-- The prepared artifacts of the implementations `v` whose loops read 16
prepared powers: by the count, those or the ones on the key context. -/
def artifactsR16W (v : GcmVariant) (r : R16 v) : List Artifact := [
  Spec.Gcm.sealPreparedApi.artifact X86_64.target (sealPrepR16 v r),
  Spec.Gcm.openPreparedApi.artifact X86_64.target (openPrepR16 v r),
  Spec.Gcm.openToPreparedApi.artifact X86_64.target (openToPrepR16 v r),
  Spec.Gcm.streamEncryptPreparedApi.artifact X86_64.target (streamEncryptPrepR16 v),
  Spec.Gcm.streamDecryptPreparedApi.artifact X86_64.target (streamDecryptPrepR16 v),
  Spec.Gcm.sealGatherPreparedApi.artifact X86_64.target (sealGatherPrepR16 v r)]

/-- The artifacts of a variant: its prepared ones, for what its loops read:
16 prepared powers (`r16`), 48 (`stitchR`), or the key context alone. -/
def artifacts (v : GcmVariant) : List Artifact :=
  match v.r16 with
  | some r => artifactsR16W v r.down
  | none => if v.stitchR.isSome then artifactsR v else artifactsW v

end VG.Artifacts.AesGcm.X86_64.AesGcm

-- AES-GCM's GHASH-only functions on x86-64
namespace VG.Artifacts.AesGcm.X86_64.Ghash

open VG.Proof.AesGcm.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The artifacts calling the implementation `n` of `vg_ghash`, and no AES. -/
def artifacts (n : GhashName) : List Artifact := [
  Spec.Gcm.streamInitApi.artifact X86_64.target (Proof.AesGcm.X86_64.Scrub.streamInitReg n),
  Spec.Gcm.streamAadApi.artifact X86_64.target (Proof.AesGcm.X86_64.Scrub.streamAadReg n)]

end VG.Artifacts.AesGcm.X86_64.Ghash

namespace VG.Artifacts.AesGcm.X86_64

def artifacts : List Artifact :=
  ((Proof.AesGcm.X86_64.streamPairs VG.Proof.Variants.AesGcm.X86_64.variants).flatMap fun (c, n) =>
    AesCtr32Ghash.artifacts c n) ++
  (VG.Proof.Variants.AesCtr32.X86_64.variants.flatMap fun v => AesCtr32.artifacts v) ++
  (VG.Proof.Variants.AesGcm.X86_64.variants.flatMap fun v => AesGcm.artifacts v) ++
  (VG.Proof.Variants.Ghash.X86_64.variants.flatMap fun v => Ghash.artifacts v) ++
  [
    Spec.Gcm.prepareApi.artifact X86_64.target Proof.Gcm.X86_64.PrepareScrub.zReg,
    Spec.Gcm.prepareApi.artifact X86_64.target Proof.Gcm.X86_64.PrepareScrub.p16Reg,
    Spec.Gcm.prepareApi.artifact X86_64.target Proof.Gcm.X86_64.PrepareScrub.avxReg,
    Spec.Gcm.prepareApi.artifact X86_64.target Proof.Gcm.X86_64.PrepareScrub.absentReg,
    Spec.Gcm.wipePreparedApi.artifact X86_64.target (Proof.Gcm.X86_64.PrepareScrub.wipeReg true),
    Spec.Gcm.wipePreparedApi.artifact X86_64.target (Proof.Gcm.X86_64.PrepareScrub.wipeReg false)]

end VG.Artifacts.AesGcm.X86_64
