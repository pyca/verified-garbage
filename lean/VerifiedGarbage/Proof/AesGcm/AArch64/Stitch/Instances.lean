module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenPw

/-!
# AES-GCM on AArch64: the code of each function, with or without the interleaved loops

Untrusted: everything here is checked by Lean. For the implementations `v`,
the code of `seal`, `open` and the functions with the powers: with the loops
that interleave counter mode and GHASH (`Impl/AesGcm/AArch64/Stitch.lean`)
if `v.stitch`, and otherwise as before, each `Verified` against its contract,
for `Generic/AesGcm/AArch64/AesGcm.lean`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull (MulKey PrepPow)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

/-- The CPU features of the functions that may run the interleaved loops:
`v`'s, and `FEAT_SHA3` for `eor3` with them. -/
def GcmImpl.stitchFeatures (v : GcmImpl) : List String := v.features ++ if v.stitch then ["sha3"] else []

/-- `vg_aes_gcm_seal` for the implementations `v`. -/
def sealCodeS (v : GcmImpl) : Prog isa := if v.stitch then Impl.AesGcm.AArch64.Stitch.«seal» v.callees else sealCode v

/-- `vg_aes_gcm_open` for the implementations `v`. -/
def openCodeS (v : GcmImpl) : Prog isa := if v.stitch then Impl.AesGcm.AArch64.Stitch.«open» v.callees else openCode v

/-- `vg_aes_gcm_seal_with_powers`, calling `g`. -/
def sealPwCode (v : GcmImpl) (g : GhashWithImpl) : Prog isa :=
  if v.stitch then Impl.AesGcm.AArch64.Stitch.sealWithPw v.callees g.fn else Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn

/-- `vg_aes_gcm_open_with_powers`, calling `g`. -/
def openPwCode (v : GcmImpl) (g : GhashWithImpl) : Prog isa :=
  if v.stitch then Impl.AesGcm.AArch64.Stitch.openWithPw v.callees g.fn else Impl.AesGcm.AArch64.Fast.openWithPw v.callees g.fn

/-- `vg_aes_gcm_seal_store_powers`, calling `g`. -/
def sealStCode (v : GcmImpl) (g : GhashStoreImpl) : Prog isa :=
  if v.stitch then Impl.AesGcm.AArch64.Stitch.sealStorePw v.callees g.fn
  else Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn

/-- `vg_aes_gcm_open_store_powers`, calling `g`. -/
def openStCode (v : GcmImpl) (g : GhashStoreImpl) : Prog isa :=
  if v.stitch then Impl.AesGcm.AArch64.Stitch.openStorePw v.callees g.fn
  else Impl.AesGcm.AArch64.Fast.openWithPw v.callees g.fn

section
variable (v : GcmImpl) (hMK : MulKey) (hP : PrepPow) (gh : Gh8Ok)
include hMK hP gh

theorem sealCodeS_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (sealCodeS v))
      (Spec.Gcm.sealContract AArch64.abi 2576) := by
  unfold sealCodeS
  split
  · exact AArch64.Verified.stackArgScratch (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64)
      (n := 320) (pre := Spec.Gcm.sealPre AArch64.abi.ptrBits)
      (post := Spec.Gcm.sealPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2576)
      (stitchSeal_verified v hMK hP gh) (by decide) (by decide) (sealPre_local _) (sealPost_local _) sealFrameSat_pre
  · exact sealCode_framed v hMK

theorem openCodeS_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (openCodeS v))
      (Spec.Gcm.openContract AArch64.abi 2592) := by
  unfold openCodeS
  split
  · exact AArch64.Verified.stackArgScratch (sig := Spec.Gcm.openSig) (nm := "work") (e := .u64)
      (n := 320) (pre := Spec.Gcm.openPre AArch64.abi.ptrBits)
      (post := Spec.Gcm.openPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
      (leak := some (Spec.Gcm.openLeak AArch64.abi.ptrBits))
      (stitchOpen_verified v hMK hP gh) (by decide) (by decide) (openPre_local _) (openPost_local _)
      openFrameSat_pre (hleak := openLeak_local _)
  · exact openCode_framed v hMK

omit hP in
theorem sealPwCode_framed (g : GhashWithImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (sealPwCode v g))
      (Spec.Gcm.sealWithPowersContract AArch64.abi 2592) := by
  unfold sealPwCode
  split
  · exact Fast.sealPwS_framed v g hMK gh
  · exact Fast.sealPw_framed v g hMK

omit hP in
theorem openPwCode_framed (g : GhashWithImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 2592 3 (openPwCode v g))
      (Spec.Gcm.openWithPowersContract AArch64.abi 2592) := by
  unfold openPwCode
  split
  · exact Fast.openPwS_framed v g hMK gh
  · exact Fast.openPw_framed v g hMK

theorem sealStCode_framed (g : GhashStoreImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (sealStCode v g))
      (Spec.Gcm.sealStorePowersContract AArch64.abi 2592) := by
  unfold sealStCode
  split
  · exact Fast.sealStS_framed v g hMK hP gh
  · exact Fast.sealSt_framed v g hMK

theorem openStCode_framed (g : GhashStoreImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 2592 3 (openStCode v g))
      (Spec.Gcm.openStorePowersContract AArch64.abi 2592) := by
  unfold openStCode
  split
  · exact Fast.openStS_framed v g hMK hP gh
  · exact Fast.openSt_framed v g hMK

end

open VG.Proof.AesGcm.AArch64.Gather in
/-- `Stitch.seal` has no frames of its own. -/
theorem stitchSeal_depth0 (v : GcmImpl) : (Impl.AesGcm.AArch64.Stitch.«seal» v.callees).aarch64Depth = 0 := by
  simp only [Impl.AesGcm.AArch64.Stitch.«seal», Impl.AesGcm.AArch64.Stitch.sealWithS,
    Impl.AesGcm.AArch64.Stitch.runWithS, Impl.AesGcm.AArch64.Stitch.stitched, Impl.Gcm.AArch64.Stitch.enc,
    Impl.Gcm.AArch64.Stitch.byRounds, Impl.Gcm.AArch64.Stitch.encLoop, Impl.AesGcm.AArch64.Fast.front,
    Impl.AesGcm.AArch64.Fast.cond, Impl.AesGcm.AArch64.Fast.padMul, cryptAl, crSeg2, crTail, sealRest, j0, j0hash,
    oneAad, absorbAl, encBody, fo, textAbs, finBody, tag, crypt, crSeg1, ctrCall, ghCall, absorb, absSeg1, absTail,
    minK, copy, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.aarch64Depth,
    depth_of_noFrames v.ctr.noFrames, depth_of_noFrames v.gh.noFrames]
  decide

open VG.Proof.AesGcm.AArch64.Gather in
/-- The frames of `sealCodeS v`, in its frame of 2576 bytes, use at most those. -/
theorem sealCodeS_depth (v : GcmImpl) :
    16 * (Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (sealCodeS v)).aarch64Depth ≤ 2576 := by
  unfold sealCodeS
  split
  · simp only [Impl.StackScratch.AArch64.withStackArgScratch, Code.aarch64Depth, Instr.frameUnits,
      stitchSeal_depth0 v]
    decide
  · exact sealCode_depth v

end VG.Proof.AesGcm.AArch64
