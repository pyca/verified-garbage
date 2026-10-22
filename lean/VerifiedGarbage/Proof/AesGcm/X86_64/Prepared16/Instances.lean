module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Instances
public import VerifiedGarbage.Spec.Gcm.Prepared16
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.StreamCallee
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.GatherCallee
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.GatherSplit
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.GatherSeal
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.Short
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.Split
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.StreamTo
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.BlocksTo
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.Gather
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.BlocksVerified
import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.Ok

/-!
# AES-GCM on x86-64: the functions a variant's `_prepared16` artifacts are built from

The 256-bit interleaved loops (`StitchName.vaes`) read only the first eight
pairs of a prepared key context (`StitchR.stitchR_okN 8`); `stitchR16` and
`stitchToR16` give them, with that proof, for the variants that name them,
and `blkR16`, …, `shortFnR16` the instances of the functions their callers
call, as `blkR`, …, `shortFnR` do for the 48 powers.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

open Gcm.X86_64.Stitch (CtxMode)

/-- The 256-bit loops, for a key context with the first 16 prepared powers. -/
theorem StitchName.okR16 : (n : StitchName) → n = .vaes →
    Proof.Gcm.X86_64.Stitch.StitchOkM CtxMode.prepared16 n.encR n.decR
      (if n.fullR then 1 else 16) (if n.fullDR then 1 else 16)
  | .vaes, _ => (Proof.Gcm.X86_64.StitchR.stitchR_okN 8).weaken (by decide) (by decide)
  | .vaesAvx512, h => by cases h
  | .aesniAvx, h => by cases h

/-- `okR16`'s loops on fewer than 16 blocks. -/
theorem StitchName.okRS16 : (n : StitchName) → n = .vaes →
    Proof.Gcm.X86_64.Stitch.StitchOkSmall CtxMode.prepared16 n.encRS n.decRS
      (if n.smallR then 1 else 16) (if n.smallR then 1 else 16)
  | .vaes, _ => (Proof.Gcm.X86_64.StitchR.stitchR_okN 8).small
  | .vaesAvx512, h => by cases h
  | .aesniAvx, h => by cases h

/-- The 256-bit loops of a variant naming them, for a key context of
`vg_aes_gcm_prepare16`. -/
def GcmVariant.stitchR16 (v : GcmVariant) : Option (StitchCode CtxMode.prepared16 true) :=
  v.stitch.bind fun p => match h : p.name with
    | .vaes => p.pieceR.map fun q =>
      ⟨p.name.encR, p.name.decR, p.name.fullR, p.name.fullDR, p.name.smallR, p.name.smallR, p.name.small4R,
        p.name.encRS, p.name.decRS, p.name.okR16 h, p.name.okRS16 h, q.enc, q.dec,
        (p.name.pieceRS q).1, (p.name.pieceRS q).2⟩
    | _ => none

/-- The 256-bit out-of-place loop, for a key context with the first 16
prepared powers. -/
theorem StitchToName.okR16 : (n : StitchToName) → n = .vaes →
    Proof.Gcm.X86_64.Stitch.StitchToOkM CtxMode.prepared16 n.encR (if n.fullR then 1 else 16)
  | .vaes, _ => Proof.Gcm.X86_64.StitchR.stitchTo_okN 8
  | .vaesAvx512, h => by cases h
  | .aesniAvx, h => by cases h

def GcmVariant.stitchToR16 (v : GcmVariant) : Option (StitchToCode CtxMode.prepared16 true) :=
  (v.stitch.bind (·.toPart)).bind fun p => match h : p.name with
    | .vaes => p.pieceR.map fun q => ⟨p.name.encR, p.name.fullR, p.name.okR16 h, q.enc⟩
    | _ => none

/-- Whole-block implementations for a key context of `vg_aes_gcm_prepare16`. -/
def blkR16 (v : GcmVariant) : BlkFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 :=
  v.impl.blkM v.stitchR16 (Spec.Gcm.encryptBlocksPrepared16Api.name ++ v.impl.suffix)
    (Spec.Gcm.decryptBlocksPrepared16Api.name ++ v.impl.suffix)

def blkToR16 (v : GcmVariant) : StreamTo.BlkToFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 :=
  .ofBlocks (Spec.Gcm.encryptBlocksToPrepared16Api.name ++ v.impl.suffix) (blkR16 v) v.stitchToR16

def encFnR16 (v : GcmVariant) : StreamTo.EncFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 :=
  .ofPrepared16 ⟨Spec.Gcm.streamEncryptPrepared16Api.name ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2584 1
        (Impl.AesGcm.X86_64.streamEncrypt (v.impl.withBlk (blkR16 v)))⟩
    (streamEncryptPrepared16_framed v.impl (blkR16 v)) (X86_64.withStackArgScratch_spSafe (streamEncryptM_spSafe v.impl (blkR16 v)))
    (StreamTo.framed_xdepth (streamEncryptM_xdepth v.impl (blkR16 v))) (StreamTo.framed_mx (streamEncryptM_mx v.impl (blkR16 v)))

def toFnR16 (v : GcmVariant) : Gather.ToFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 :=
  .ofPrepared16 ⟨Spec.Gcm.streamEncryptToPrepared16Api.name ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2232 3
        (Impl.AesGcm.X86_64.StreamTo.encrypt (blkToR16 v).fn (encFnR16 v).fn)⟩
    (StreamTo.streamEncryptToPrepared16_framed (blkToR16 v) (encFnR16 v))
    (X86_64.withStackArgScratch_spSafe (StreamTo.encrypt_spAll (blkToR16 v) (encFnR16 v)))
    (StreamTo.framed_xdepth (StreamTo.encrypt_xdepth (blkToR16 v) (encFnR16 v)))
    (StreamTo.framed_mx (StreamTo.encrypt_mx (blkToR16 v) (encFnR16 v)))

/-- The instance of `vg_aes_gcm_seal_prepared16` of a variant. -/
def sealFnR16 (v : GcmVariant) (hs : v.impl.short = false) : Gather.SealFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 :=
  .ofPrepared16 ⟨Spec.Gcm.sealPrepared16Api.name ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCodeP (v.impl.withBlk (blkR16 v)))⟩
    (sealSelPrepared16_framed v.impl (blkR16 v) Short.shortFacts hs)
    (X86_64.withStackArgScratch_spSafe (sealCodeP_spSafe v.impl (blkR16 v)))
    (StreamTo.framed_xdepth (sealCodeP_xdepth v.impl (blkR16 v))) (StreamTo.framed_mx (sealCodeP_mx v.impl (blkR16 v)))

/-- The instance of `vg_aes_gcm_seal_split_prepared16` of a variant. -/
def splitFnR16 (v : GcmVariant) (hz : ∀ n, v.impl.onePass = some n → n ≠ .z) : Gather.SplitFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 :=
  .ofPrepared16 ⟨Spec.Gcm.sealSplitPrepared16Api.name ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2616 5
        (Impl.AesGcm.X86_64.SealSplit.«seal» (v.impl.splitMidR (v.impl.withBlk (blkR16 v)) (blkToR16 v).fn))⟩
    (Split.sealSplitPrepared16_framed v.impl (blkR16 v) (blkToR16 v) Short.shortFacts hz)
    (X86_64.withStackArgScratch_spSafe (Split.sealSplitR_spSafe v.impl (blkR16 v) (blkToR16 v)))
    (StreamTo.framed_xdepth (Split.sealSplitR_xdepth v.impl (blkR16 v) (blkToR16 v)))
    (StreamTo.framed_mx (Split.sealSplitR_mx v.impl (blkR16 v) (blkToR16 v)))

/-- The short path of `vg_aes_gcm_seal_gather_prepared16` of a variant. -/
def shortFnR16 (v : GcmVariant) (hs : v.impl.short = false) (hz : ∀ n, v.impl.onePass = some n → n ≠ .z) : Gather.ShortFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 :=
  .ofBoth (sealFnR16 v hs) (splitFnR16 v hz) (copyBelow_lt v) (splitFrom_pos v) (splitFrom_le v)

end VG.Proof.AesGcm.X86_64
