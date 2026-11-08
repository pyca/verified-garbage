module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Verified
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.Gcm.Prepared8Contract
public import VerifiedGarbage.Impl.AesGcm.AArch64.Fast
public import VerifiedGarbage.Proof.AesGcm.AArch64.Frame
public import VerifiedGarbage.Proof.AesGcm.AArch64.OneShot
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Verified
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenVerified
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Instances
import VerifiedGarbage.Impl.AesGcm.AArch64.Stitch
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenTo

/-!
# The instance of `seal` that `seal_gather` calls

`sealFn`: the code of `seal` for a variant, with its proof (given that of
GHASH's multiplication by the key, `MulKey`) and stack depth, for
`Generic/AesGcm/AArch64/AesGcm.lean`; and the stack depth of
`open_to_with_powers` (`openToPwCode_depth`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64

open VG.Proof.AesGcm.AArch64

/-- The instance of `vg_aes_gcm_seal` calling the implementations `v`. -/
def sealFn (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) : Proof.AesGcm.AArch64.Gather.SealFn .plain :=
  .plain ⟨Spec.Gcm.sealApi.name ++ { v with stitch := false }.suffix, Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (sealCode v)⟩
    (sealCode_framed v hMK) (sealCode_depth v)

open VG.Proof.AesGcm.AArch64.Gather in
open VG.Impl.AesGcm.AArch64 in
/-- The frames of `openToPwCode v g`, in its frame of 2608 bytes, use at most those. -/
theorem openToPwCode_depth (v : GcmImpl) (g : GhashWithImpl) :
    16 * (Impl.StackScratch.AArch64.withStackArgScratch 2608 5 (openToPwCode v g)).aarch64Depth ≤ 2608 := by
  unfold openToPwCode
  split
  · have h0 : (Stitch.openToWithPw v.callees g.fn).aarch64Depth = 0 := by
      simp only [Stitch.openToWithPw, Stitch.openWithSG, Stitch.openFastSG, Stitch.openRunWithSG, Stitch.decPre,
        Stitch.failS, Stitch.okS, Stitch.openShortFG, Stitch.openShortG, Stitch.shortPre, Stitch.textIn,
        Stitch.copyQ, Stitch.ctToB2, Stitch.aadIn, Stitch.plainOutG, Stitch.stitched, Fast.pwSel, Fast.pwCall,
        Fast.openFastPG, Fast.openRunWithPG, Fast.oneCryptTG, Fast.front, Fast.cond, Fast.padMul, Fast.padMulT,
        Impl.AesGcm.AArch64.Tail.cryptAlT, Impl.AesGcm.AArch64.Tail.crSeg2T, Impl.AesGcm.AArch64.Tail.crTailT,
        openEntryG, openRestG, openMainG, oneCryptG, cryptAlG, crArgsG, ctrCallG, crTailG, wipeG, wipeLoop, crArgs,
        tagLenOk, tagIn, cmpSeg, cmp, cmp16, j0, j0hash, oneAad, absorbAl, decAbs, fo, textAbs, finBody, tag,
        crSeg2, crTail, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, Impl.AesGcm.AArch64.xor,
        padSeg, flush, lens, SealGather.copyBlocks, GcmImpl.callees, Bool.cond_true, ite_true,
        Code.aarch64Depth, depth_of_noFrames v.ctr.noFrames, depth_of_noFrames v.ctr.toNoFrames,
        depth_of_noFrames v.gh.noFrames, depth_of_noFrames g.noFrames, Nat.max_self, Nat.max_zero, Nat.zero_max]
      decide
    simp only [Impl.StackScratch.AArch64.withStackArgScratch, Code.aarch64Depth, AArch64.Instr.frameUnits, h0]
    decide
  · exact Fast.openToPw_depth v g

end VG.Proof.AesGcm.AArch64
