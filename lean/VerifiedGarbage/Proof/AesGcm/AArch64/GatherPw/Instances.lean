module

public import VerifiedGarbage.Proof.AesGcm.AArch64.GatherPw.Callee
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Instances
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Verified
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Verified

/-!
# The instances of `seal_with_powers` that `seal_gather_with_powers` calls

`sealPwFn`: the code of `seal_with_powers` for a variant, with or without the
interleaved loops, with its proof and stack depth (`sealPwCode_depth`: it has
no frames but its own), for `Generic/AesGcm/AArch64/AesGcm.lean`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64.Gather (depth_of_noFrames)
open VG.Proof.Gcm.AArch64.Pmull (MulKey)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

/-- The frames of `sealPwCode v g`, in its frame of 2592 bytes, use at most those. -/
theorem sealPwCode_depth (v : GcmImpl) (g : GhashWithImpl) :
    16 * (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (sealPwCode v g)).aarch64Depth ≤ 2592 := by
  have hcl : (Impl.AesGcm.AArch64.Fast.pwCall 8 g.fn).aarch64Depth = 0 := by
    simp only [Impl.AesGcm.AArch64.Fast.pwCall, Code.aarch64Depth, depth_of_noFrames g.noFrames]; rfl
  have h0 : (sealPwCode v g).aarch64Depth = 0 := by
    unfold sealPwCode
    split
    · simp only [Impl.AesGcm.AArch64.Stitch.sealWithPw, Impl.AesGcm.AArch64.Stitch.sealWithS, Code.aarch64Depth,
        hcl, depth_of_noFrames v.ctr.noFrames, depth_of_noFrames v.gh.noFrames, ite_true, copyLoop, copyW,
        xorLoop, xorW, copyB, xorB, SealGather.copyBlocks, Impl.Gcm.AArch64.Stitch.byRounds,
        Impl.Gcm.AArch64.Stitch.enc, Impl.Gcm.AArch64.Stitch.encLoop, Impl.AesGcm.AArch64.Fast.runWithP,
        Impl.AesGcm.AArch64.Fast.front, Impl.AesGcm.AArch64.Fast.cond, Impl.AesGcm.AArch64.Fast.padMul,
        Impl.AesGcm.AArch64.Fast.padMulT, Impl.AesGcm.AArch64.Tail.cryptAlT, Impl.AesGcm.AArch64.Tail.crSeg2T,
        Impl.AesGcm.AArch64.Tail.crTailT, crSeg2, crTail, sealRest, j0, j0hash, oneAad, absorbAl, encBody, fo,
        textAbs, finBody, tag, crypt, crSeg1, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy,
        Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Impl.AesGcm.AArch64.Stitch.thr,
        Impl.AesGcm.AArch64.Stitch.runWithS, Impl.AesGcm.AArch64.Stitch.shortThr,
        Impl.AesGcm.AArch64.Stitch.shortMin, Impl.AesGcm.AArch64.Stitch.sealShort,
        Impl.AesGcm.AArch64.Stitch.whole, Impl.AesGcm.AArch64.Stitch.stitched, Impl.AesGcm.AArch64.Stitch.tbl,
        Impl.AesGcm.AArch64.Stitch.pwTbl, Impl.AesGcm.AArch64.Stitch.minLen, Impl.AesGcm.AArch64.Stitch.b1O,
        Impl.AesGcm.AArch64.Stitch.b2O, Impl.AesGcm.AArch64.Stitch.shortMax, Impl.AesGcm.AArch64.Stitch.shortLen,
        Impl.AesGcm.AArch64.Stitch.atP, Impl.AesGcm.AArch64.Stitch.zeroBufs, Impl.AesGcm.AArch64.Stitch.shortPre,
        Impl.AesGcm.AArch64.Stitch.copyQ, Impl.AesGcm.AArch64.Stitch.textIn, Impl.AesGcm.AArch64.Stitch.shortCtr,
        Impl.AesGcm.AArch64.Stitch.ctToB2, Impl.AesGcm.AArch64.Stitch.textOut, Impl.AesGcm.AArch64.Stitch.aadIn,
        Impl.AesGcm.AArch64.Stitch.lensB, Impl.AesGcm.AArch64.Stitch.shortGh,
        Impl.AesGcm.AArch64.Stitch.shortTagAt, Impl.AesGcm.AArch64.Stitch.shortTag]
      decide
    · exact fastSealWithE_depth0 v (.inr rfl) hcl
  simp only [Impl.StackScratch.AArch64.withStackArgScratch, Code.aarch64Depth, Instr.frameUnits, h0]
  decide

/-- The instance of `vg_aes_gcm_seal_with_powers` calling the implementations
`v`, and `g` on the path for TLS records. -/
def sealPwFn (v : GcmImpl) (g : GhashWithImpl) (hMK : MulKey) (gh : Gh8Ok) : GatherPw.SealPwFn :=
  .ofSpec ⟨Spec.Gcm.sealWithPowersApi.name ++ v.suffix,
      Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (sealPwCode v g)⟩
    (sealPwCode_framed v hMK gh g) (sealPwCode_depth v g)

end VG.Proof.AesGcm.AArch64
