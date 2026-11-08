module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Verified
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.Gcm.Prepared8Contract
public import VerifiedGarbage.Impl.AesGcm.AArch64.Fast
public import VerifiedGarbage.Proof.AesGcm.AArch64.Frame
public import VerifiedGarbage.Proof.AesGcm.AArch64.OneShot
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Verified
public import VerifiedGarbage.Proof.AesGcm.AArch64.OpenTo.Fn
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenVerified
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Instances
public import VerifiedGarbage.Proof.AesGcm.AArch64.OpenTo.Split
public import VerifiedGarbage.Proof.AesGcm.AArch64.OpenSplit.Verified
import VerifiedGarbage.Impl.AesGcm.AArch64.Stitch

/-!
# The instances of `seal` and `open` that `seal_gather` and `open_to` call

`sealFn` and `openFn`: the code of `seal` and of `open` for a variant, with
its proof (given that of GHASH's multiplication by the key, `MulKey`) and
stack depth, for `Generic/AesGcm/AArch64/AesGcm.lean`; `openPwFn`, that
of `open_with_powers`, which `open_to_with_powers` calls; and
`openSplitFn`, that of `open_split_with_powers`, which it calls in one pass.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64

open VG.Proof.AesGcm.AArch64

/-- The instance of `vg_aes_gcm_seal` calling the implementations `v`. -/
def sealFn (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) : Proof.AesGcm.AArch64.Gather.SealFn .plain :=
  .plain ⟨Spec.Gcm.sealApi.name ++ { v with stitch := false }.suffix, Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (sealCode v)⟩
    (sealCode_framed v hMK) (sealCode_depth v)

/-- The instance of `vg_aes_gcm_open` calling the implementations `v`, which
`vg_aes_gcm_open_to` calls. -/
def openFn (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Proof.AesGcm.AArch64.OpenTo.OpenFn Proof.AesGcm.AArch64.OpenTo.openShape :=
  ⟨⟨Spec.Gcm.openApi.name ++ { v with stitch := false }.suffix, Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (openCode v)⟩,
    openCode_framed v hMK, openCode_depth v⟩

open VG.Proof.AesGcm.AArch64.Gather in
open VG.Impl.AesGcm.AArch64 in
/-- The frames of `openPwCode v g`, in its frame of 2592 bytes, use at most those. -/
theorem openPwCode_depth (v : GcmImpl) (g : GhashWithImpl) :
    16 * (Impl.StackScratch.AArch64.withStackArgScratch 2592 3 (openPwCode v g)).aarch64Depth ≤ 2592 := by
  have hcl : (Fast.pwSel v.callees 16 g.fn).aarch64Depth = 0 := by
    simp only [Fast.pwSel, Fast.pwCall, Code.aarch64Depth, GcmImpl.callees, depth_of_noFrames v.gh.noFrames,
      depth_of_noFrames g.noFrames, Nat.max_self]
  have h0 : (openPwCode v g).aarch64Depth = 0 := by
    unfold openPwCode
    split
    · simp only [Stitch.openWithPw, Stitch.openWithS, Stitch.openFastS, Stitch.openRunWithS, Stitch.decPart, cond, Stitch.openShortF,
        Stitch.openShort, Stitch.shortPre, Stitch.textIn, Stitch.copyQ, Stitch.ctToB2, Stitch.aadIn,
        Stitch.plainOut, Stitch.stitched, Fast.pwSel, Fast.pwCall, Impl.AesGcm.AArch64.Fast.openFastP,
        Impl.AesGcm.AArch64.Fast.openRunWithP, Impl.AesGcm.AArch64.Fast.front, Impl.AesGcm.AArch64.Fast.cond,
        Impl.AesGcm.AArch64.Fast.padMul, Impl.AesGcm.AArch64.Fast.padMulT, Impl.AesGcm.AArch64.Fast.oneCryptT,
        Impl.AesGcm.AArch64.Tail.cryptAlT, Impl.AesGcm.AArch64.Tail.crSeg2T, Impl.AesGcm.AArch64.Tail.crTailT,
        openRest, openMain, oneCrypt, cryptAl, crArgs, tagLenOk, tagIn, cmpSeg, cmp, cmp16, j0, j0hash, oneAad,
        absorbAl, decAbs, fo, textAbs, finBody, tag, crSeg2, crTail, ctrCall, ghCall, absorb, absSeg1, absTail,
        minK, copy, copyB, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, SealGather.copyBlocks, GcmImpl.callees,
        Code.aarch64Depth, depth_of_noFrames v.ctr.noFrames, depth_of_noFrames v.gh.noFrames,
        depth_of_noFrames g.noFrames, ite_true, Nat.max_self, Nat.max_zero, Nat.zero_max]
      decide
    · exact fastOpenWithE_depth0 v (.inr rfl) hcl
  simp only [Impl.StackScratch.AArch64.withStackArgScratch, Code.aarch64Depth, AArch64.Instr.frameUnits, h0]
  decide

/-- The instance of `vg_aes_gcm_open_with_powers` calling the implementations
`v` and `g`, which `vg_aes_gcm_open_to_with_powers` calls. -/
def openPwFn (v : GcmImpl) (g : GhashWithImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
    (gh : Proof.Gcm.AArch64.Stitch.Gh8Ok) :
    Proof.AesGcm.AArch64.OpenTo.OpenFn Proof.AesGcm.AArch64.OpenTo.pwShape :=
  ⟨⟨Spec.Gcm.openWithPowersApi.name ++ v.suffix, Impl.StackScratch.AArch64.withStackArgScratch 2592 3 (openPwCode v g)⟩,
    openPwCode_framed v hMK gh g, openPwCode_depth v g⟩

open VG.Proof.AesGcm.AArch64.Gather in
open VG.Impl.AesGcm.AArch64 in
/-- The frames of `vg_aes_gcm_open_split_with_powers`, in its frame of 2608 bytes, use at most those. -/
theorem openSplitCode_depth (v : GcmImpl) (g : GhashWithImpl) :
    16 * (Impl.StackScratch.AArch64.withStackArgScratch 2608 5 (Stitch.openSplitWithPw v.callees g.fn)).aarch64Depth ≤
      2608 := by
  have h0 : (Stitch.openSplitWithPw v.callees g.fn).aarch64Depth = 0 := by
    simp only [Stitch.openSplitWithPw, Stitch.openFastS, Stitch.openRunWithS, Stitch.decPart, cond,
      Stitch.tailTo, Stitch.stitched, Fast.pwSel, Fast.pwCall, Impl.AesGcm.AArch64.Fast.front,
      Impl.AesGcm.AArch64.Fast.padMul, Impl.AesGcm.AArch64.Fast.padMulT, Impl.AesGcm.AArch64.Tail.cryptAlT,
      Impl.AesGcm.AArch64.Tail.crSeg2T, Impl.AesGcm.AArch64.Tail.crTailT, crArgs, tagLenOk, tagIn, cmpSeg, cmp,
      cmp16, crTail, ctrCall, copy, copyB, Impl.AesGcm.AArch64.xor, GcmImpl.callees, Code.aarch64Depth,
      depth_of_noFrames v.ctr.noFrames, depth_of_noFrames v.gh.noFrames, depth_of_noFrames g.noFrames,
      Nat.max_self, Nat.max_zero, Nat.zero_max]
    decide
  simp only [Impl.StackScratch.AArch64.withStackArgScratch, Code.aarch64Depth, AArch64.Instr.frameUnits, h0]
  decide

/-- The instance of `vg_aes_gcm_open_split_with_powers` calling the
implementations `v` and `g`, which `vg_aes_gcm_open_to_with_powers` calls in
one pass. -/
def openSplitFn (v : GcmImpl) (g : GhashWithImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
    (gh : Proof.Gcm.AArch64.Stitch.Gh8Ok) : Proof.AesGcm.AArch64.OpenTo.SplitFn :=
  ⟨⟨"vg_aes_gcm_open_split_with_powers" ++ v.suffix,
      Impl.StackScratch.AArch64.withStackArgScratch 2608 5 (Impl.AesGcm.AArch64.Stitch.openSplitWithPw v.callees g.fn)⟩,
    OpenSplit.openSp_framed v g hMK gh, openSplitCode_depth v g⟩

end VG.Proof.AesGcm.AArch64
