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
open VG.Proof.AesGcm.X86_64.Scrub (gcmOf pairOf)

/-- The artifacts calling the implementation `c` of `vg_aes_ctr32` and `n` of
`vg_ghash`, a pair that a variant of AES-GCM calls (`streamPairs`). -/
def artifacts (c : Ctr32Impl) (n : GhashName) : List Artifact := [
  Spec.Gcm.streamFinishApi.artifact X86_64.target
    (match c.free, (pairOf c n).gh.free with
    | some f, some g =>
      { suffix := c.suffix ++ n.impl.suffix
        code := Impl.AesGcm.X86_64.Fn.streamFinish ((pairOf c n).lv .sse) 232 (pairOf c n).callees
        verified := .scrubbed (Proof.AesGcm.X86_64.Scrub.streamFinishFF_scrubbed c n f g)
        spSafe := Proof.AesGcm.X86_64.Scrub.streamFinishFF_spSafeFn c n }
    | some f, none =>
      { suffix := c.suffix ++ n.impl.suffix
        code := Impl.AesGcm.X86_64.Fn.streamFinish ((pairOf c n).lv .sse) 792 (pairOf c n).callees
        verified := .scrubbed (Proof.AesGcm.X86_64.Scrub.streamFinishF_scrubbed c n f)
        spSafe := Proof.AesGcm.X86_64.Scrub.streamFinishF_spSafeFn c n }
    | none, _ =>
      { suffix := c.suffix ++ n.impl.suffix
        code := Impl.AesGcm.X86_64.Fn.streamFinish ((pairOf c n).lv .sse) 2584 (pairOf c n).callees
        verified := .scrubbed (Proof.AesGcm.X86_64.Scrub.streamFinish_scrubbed c n)
        spSafe := Proof.AesGcm.X86_64.Scrub.streamFinish_spSafeFn c n }),
  Spec.Gcm.streamVerifyApi.artifact X86_64.target
    (match c.free, (pairOf c n).gh.free with
    | some f, some g =>
      { suffix := c.suffix ++ n.impl.suffix
        code := Impl.AesGcm.X86_64.Fn.streamVerify ((pairOf c n).lv .sse) 304 (pairOf c n).callees
        verified := .scrubbed (Proof.AesGcm.X86_64.Scrub.streamVerifyFF_scrubbed c n f g)
        spSafe := Proof.AesGcm.X86_64.Scrub.streamVerifyFF_spSafeFn c n }
    | some f, none =>
      { suffix := c.suffix ++ n.impl.suffix
        code := Impl.AesGcm.X86_64.Fn.streamVerify ((pairOf c n).lv .sse) 800 (pairOf c n).callees
        verified := .scrubbed (Proof.AesGcm.X86_64.Scrub.streamVerifyF_scrubbed c n f)
        spSafe := Proof.AesGcm.X86_64.Scrub.streamVerifyF_spSafeFn c n }
    | none, _ =>
      { suffix := c.suffix ++ n.impl.suffix
        code := Impl.AesGcm.X86_64.Fn.streamVerify ((pairOf c n).lv .sse) 2592 (pairOf c n).callees
        verified := .scrubbed (Proof.AesGcm.X86_64.Scrub.streamVerify_scrubbed c n)
        spSafe := Proof.AesGcm.X86_64.Scrub.streamVerify_spSafeFn c n })]

end VG.Artifacts.AesGcm.X86_64.AesCtr32Ghash

-- AES-GCM's AES-only function on x86-64: `vg_aes_gcm_init`
namespace VG.Artifacts.AesGcm.X86_64.AesCtr32

open VG.Proof.AesGcm.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.AesGcm.X86_64.Scrub (gcmOf gcmOfF)

/-- The artifacts calling the implementation `c` of `vg_aes_ctr32`, with the
key expansion for the same CPUs, and no GHASH. -/
def artifacts (c : Ctr32Impl) : List Artifact :=
  [Spec.Gcm.initApi.artifact X86_64.target
    (match c.free with
    | some fc =>
      { suffix := c.suffix
        code := Impl.AesGcm.X86_64.Fn.init ((gcmOfF c).lv .sse) 192 (gcmOfF c).callees
        verified := .scrubbed (Proof.AesGcm.X86_64.Scrub.initF_scrubbed c fc)
        spSafe := Proof.AesGcm.X86_64.Scrub.initF_spSafeFn c }
    | none =>
      { suffix := c.suffix
        code := Impl.AesGcm.X86_64.Fn.init ((gcmOf c).lv .sse) 2576 (gcmOf c).callees
        verified := .scrubbed (Proof.AesGcm.X86_64.Scrub.init_scrubbed c)
        spSafe := Proof.AesGcm.X86_64.Scrub.init_spSafeFn c })]

end VG.Artifacts.AesGcm.X86_64.AesCtr32

-- AES-GCM (NIST SP 800-38D) on x86-64
namespace VG.Artifacts.AesGcm.X86_64.AesGcm

open VG.Proof.AesGcm.X86_64

/-- The prepared artifacts of the implementations `v` whose loops read the
48 prepared powers: by the flag, those or the ones on the key context. -/
def artifactsR (v : GcmVariant) : List Artifact := [
  Spec.Gcm.sealPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.AesGcm.X86_64.Fn.sealP v.lv 48 v.impl.short v.impl.fin (v.impl.withBlk (blkR v)) v.impl.callees
    verified := .scrubbed (Proof.AesGcm.X86_64.sealR_scrubbed v)
    spSafe := Proof.AesGcm.X86_64.sealR_spSafeFn v },
  Spec.Gcm.openPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.AesGcm.X86_64.Fn.openP v.lvA 48 v.impl.short (v.impl.withBlk (blkR v)) v.impl.callees
    verified := .scrubbed (Proof.AesGcm.X86_64.openR_scrubbed v)
    spSafe := Proof.AesGcm.X86_64.openR_spSafeFn v },
  Spec.Gcm.openToPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.AesGcm.X86_64.Fn.openToP v.lvT 48 v.stitchToDecR.isSome v.impl.copyW (openFnF v).fn (openSplitFnF v).fn
            (openSplitFnB v v.ctrTo).fn
    verified := .scrubbed (Proof.AesGcm.X86_64.openToR_scrubbed v)
    spSafe := Proof.AesGcm.X86_64.openToR_spSafeFn v },
  Spec.Gcm.streamEncryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.AesGcm.X86_64.Fn.streamEncryptP v.lv 48 (v.impl.withBlk (blkR v)) v.impl.callees
    verified := .scrubbed (Proof.AesGcm.X86_64.streamEncryptR_scrubbed v)
    spSafe := Proof.AesGcm.X86_64.streamEncryptR_spSafeFn v },
  Spec.Gcm.streamDecryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.AesGcm.X86_64.Fn.streamDecryptP v.lv 48 (v.impl.withBlk (blkR v)) v.impl.callees
    verified := .scrubbed (Proof.AesGcm.X86_64.streamDecryptR_scrubbed v)
    spSafe := Proof.AesGcm.X86_64.streamDecryptR_spSafeFn v },
  Spec.Gcm.sealGatherPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.AesGcm.X86_64.Fn.sealGatherP v.lvGA 48 (tlsLong v) (copyBelow v) (splitFrom v) (sealFnF v).fn
            (splitFnF v).fn (toFnF v).fn (sealFn v.impl).fn (splitFn v).fn (toFn v).fn (initFn v.impl).fn
            (aadFn v.impl).fn (finFn v.impl).fn false
    verified := .scrubbed (Proof.AesGcm.X86_64.sealGatherR_scrubbed v)
    spSafe := Proof.AesGcm.X86_64.sealGatherR_spSafeFn v }]

/-- The prepared artifacts of the implementations `v`, which read only the
key context. -/
def artifactsW (v : GcmVariant) : List Artifact := [
  Spec.Gcm.sealPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.AesGcm.X86_64.Fn.sealW v.lv v.impl.short v.impl.fin v.impl.callees
    verified := .scrubbed (Proof.AesGcm.X86_64.sealW_scrubbed v)
    spSafe := Proof.AesGcm.X86_64.sealW_spSafeFn v },
  Spec.Gcm.openPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.AesGcm.X86_64.Fn.openW v.lv v.impl.short v.impl.callees
    verified := .scrubbed (Proof.AesGcm.X86_64.openW_scrubbed v)
    spSafe := Proof.AesGcm.X86_64.openW_spSafeFn v },
  Spec.Gcm.openToPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.AesGcm.X86_64.Fn.openToW v.lvTW (openSplitFnB v v.ctrTo).fn
    verified := .scrubbed (Proof.AesGcm.X86_64.openToW_scrubbed v)
    spSafe := Proof.AesGcm.X86_64.openToW_spSafeFn v },
  Spec.Gcm.streamEncryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.AesGcm.X86_64.Fn.streamEncryptW v.lv v.impl.callees
    verified := .scrubbed (Proof.AesGcm.X86_64.streamEncryptW_scrubbed v)
    spSafe := Proof.AesGcm.X86_64.streamEncryptW_spSafeFn v },
  Spec.Gcm.streamDecryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.AesGcm.X86_64.Fn.streamDecryptW v.lv v.impl.callees
    verified := .scrubbed (Proof.AesGcm.X86_64.streamDecryptW_scrubbed v)
    spSafe := Proof.AesGcm.X86_64.streamDecryptW_spSafeFn v },
  Spec.Gcm.sealGatherPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.AesGcm.X86_64.Fn.sealGatherW v.lvG (copyBelow v) (splitFrom v) (sealFn v.impl).fn (splitFn v).fn
            (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn
    verified := .scrubbed (Proof.AesGcm.X86_64.sealGatherW_scrubbed v)
    spSafe := Proof.AesGcm.X86_64.sealGatherW_spSafeFn v }]

/-- The prepared artifacts of the implementations `v` whose loops read 16
prepared powers: by the count, those or the ones on the key context. -/
def artifactsR16W (v : GcmVariant) (r : R16 v) : List Artifact := [
  Spec.Gcm.sealPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.AesGcm.X86_64.Fn.sealP v.lv 16 v.impl.short v.impl.fin (v.impl.withBlk (blkR16 v)) v.impl.callees
    verified := .scrubbed (Proof.AesGcm.X86_64.sealR16_scrubbed v r)
    spSafe := Proof.AesGcm.X86_64.sealR16_spSafeFn v r },
  Spec.Gcm.openPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.AesGcm.X86_64.Fn.openP v.lvA 16 v.impl.short (v.impl.withBlk (blkR16 v)) v.impl.callees
    verified := .scrubbed (Proof.AesGcm.X86_64.openR16_scrubbed v r)
    spSafe := Proof.AesGcm.X86_64.openR16_spSafeFn v r },
  Spec.Gcm.openToPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.AesGcm.X86_64.Fn.openToP v.lvT 16 v.stitchToDecR16.isSome v.impl.copyW (openFnF16 v r).fn
            (openSplitFnF16 v).fn (openSplitFnB v v.ctrTo).fn
    verified := .scrubbed (Proof.AesGcm.X86_64.openToR16_scrubbed v r)
    spSafe := Proof.AesGcm.X86_64.openToR16_spSafeFn v r },
  Spec.Gcm.streamEncryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.AesGcm.X86_64.Fn.streamEncryptP v.lv 16 (v.impl.withBlk (blkR16 v)) v.impl.callees
    verified := .scrubbed (Proof.AesGcm.X86_64.streamEncryptR16_scrubbed v)
    spSafe := Proof.AesGcm.X86_64.streamEncryptR16_spSafeFn v },
  Spec.Gcm.streamDecryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.AesGcm.X86_64.Fn.streamDecryptP v.lv 16 (v.impl.withBlk (blkR16 v)) v.impl.callees
    verified := .scrubbed (Proof.AesGcm.X86_64.streamDecryptR16_scrubbed v)
    spSafe := Proof.AesGcm.X86_64.streamDecryptR16_spSafeFn v },
  Spec.Gcm.sealGatherPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.AesGcm.X86_64.Fn.sealGatherP v.lvGA 16 (tlsLong v) (copyBelow v) (splitFrom v) (sealFnF16 v r).fn
            (splitFnF16 v r).fn (toFnF16 v).fn (sealFn v.impl).fn (splitFn v).fn (toFn v).fn (initFn v.impl).fn
            (aadFn v.impl).fn (finFn v.impl).fn true
    verified := .scrubbed (Proof.AesGcm.X86_64.sealGatherR16_scrubbed v r)
    spSafe := Proof.AesGcm.X86_64.sealGatherR16_spSafeFn v r }]

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
open VG.Proof.AesGcm.X86_64.Scrub (gcmOf ghOf)

/-- The artifacts calling the implementation `n` of `vg_ghash`, and no AES. -/
def artifacts (n : GhashName) : List Artifact := [
  Spec.Gcm.streamInitApi.artifact X86_64.target
    (match (ghOf n).gh.free with
    | some f =>
      { suffix := n.impl.suffix
        code := Impl.AesGcm.X86_64.Fn.streamInit ((ghOf n).lv .sse) 240 (ghOf n).callees
        verified := .scrubbed (Proof.AesGcm.X86_64.Scrub.streamInitF_scrubbed n f)
        spSafe := Proof.AesGcm.X86_64.Scrub.streamInitF_spSafeFn n }
    | none =>
      { suffix := n.impl.suffix
        code := Impl.AesGcm.X86_64.Fn.streamInit ((ghOf n).lv .sse) 784 (ghOf n).callees
        verified := .scrubbed (Proof.AesGcm.X86_64.Scrub.streamInit_scrubbed n)
        spSafe := Proof.AesGcm.X86_64.Scrub.streamInit_spSafeFn n }),
  Spec.Gcm.streamAadApi.artifact X86_64.target
    (match (ghOf n).gh.free with
    | some f =>
      { suffix := n.impl.suffix
        code := Impl.AesGcm.X86_64.Fn.streamAad ((ghOf n).lv .sse) 192 (ghOf n).callees
        verified := .scrubbed (Proof.AesGcm.X86_64.Scrub.streamAadF_scrubbed n f)
        spSafe := Proof.AesGcm.X86_64.Scrub.streamAadF_spSafeFn n }
    | none =>
      { suffix := n.impl.suffix
        code := Impl.AesGcm.X86_64.Fn.streamAad ((ghOf n).lv .sse) 784 (ghOf n).callees
        verified := .scrubbed (Proof.AesGcm.X86_64.Scrub.streamAad_scrubbed n)
        spSafe := Proof.AesGcm.X86_64.Scrub.streamAad_spSafeFn n })]

end VG.Artifacts.AesGcm.X86_64.Ghash

namespace VG.Artifacts.AesGcm.X86_64

def artifacts : List Artifact :=
  ((Proof.AesGcm.X86_64.streamPairs VG.Proof.Variants.AesGcm.X86_64.variants).flatMap fun (c, n) =>
    AesCtr32Ghash.artifacts c n) ++
  (VG.Proof.Variants.AesCtr32.X86_64.variants.flatMap fun v => AesCtr32.artifacts v) ++
  (VG.Proof.Variants.AesGcm.X86_64.variants.flatMap fun v => AesGcm.artifacts v) ++
  (VG.Proof.Variants.Ghash.X86_64.variants.flatMap fun v => Ghash.artifacts v) ++
  [
    Spec.Gcm.prepareApi.artifact X86_64.target {
      suffix := "_vpclmul_avx512"
      code := Impl.Gcm.X86_64.Fn.prepareZ
      verified := .scrubbed Proof.Gcm.X86_64.PrepareScrub.z_scrubbed
      spSafe := Proof.Gcm.X86_64.PrepareScrub.z_spSafeFn },
    Spec.Gcm.prepareApi.artifact X86_64.target {
      suffix := "_vpclmul"
      code := Impl.Gcm.X86_64.Fn.prepare16
      verified := .scrubbed Proof.Gcm.X86_64.PrepareScrub.p16_scrubbed
      spSafe := Proof.Gcm.X86_64.PrepareScrub.p16_spSafeFn },
    Spec.Gcm.prepareApi.artifact X86_64.target {
      suffix := "_pclmul_avx"
      code := Impl.Gcm.X86_64.Fn.prepareAvx
      verified := .scrubbed Proof.Gcm.X86_64.PrepareScrub.avx_scrubbed
      spSafe := Proof.Gcm.X86_64.PrepareScrub.avx_spSafeFn },
    Spec.Gcm.prepareApi.artifact X86_64.target {
      suffix := ""
      code := Impl.Gcm.X86_64.Fn.prepareAbsent
      verified := .scrubbed Proof.Gcm.X86_64.PrepareScrub.absent_scrubbed
      spSafe := Proof.Gcm.X86_64.PrepareScrub.absent_spSafeFn },
    Spec.Gcm.wipePreparedApi.artifact X86_64.target {
      suffix := "_avx"
      code := Impl.Gcm.X86_64.Fn.wipe true
      verified := .scrubbed (Proof.Gcm.X86_64.PrepareScrub.wipe_scrubbed true)
      spSafe := Proof.Gcm.X86_64.PrepareScrub.wipe_spSafeFn true },
    Spec.Gcm.wipePreparedApi.artifact X86_64.target {
      suffix := ""
      code := Impl.Gcm.X86_64.Fn.wipe false
      verified := .scrubbed (Proof.Gcm.X86_64.PrepareScrub.wipe_scrubbed false)
      spSafe := Proof.Gcm.X86_64.PrepareScrub.wipe_spSafeFn false }]

end VG.Artifacts.AesGcm.X86_64
