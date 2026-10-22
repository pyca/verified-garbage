module

import VerifiedGarbage.Proof.AesGcmSiv.AArch64.FnCT
import VerifiedGarbage.Proof.GcmSiv.Polyval
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Verified
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.CT
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Fn

/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: `Verified`

Untrusted: everything here is checked by Lean. As
`Proof/AesGcmSiv/AArch64/Verified.lean`, for the interleaved `seal` and
`open` (`Impl.AesGcmSiv.AArch64.Stitch`), which keep `v8`–`v15` too; and,
for `Generic/AesGcm/AArch64/AesGcmSiv.lean`, the code of each function: the
interleaved one if `v.stitch`, and the other otherwise.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64 VG.Impl.AesGcmSiv.AArch64
open VG.Proof.AesGcm.AArch64 (GcmImpl)
open VG.Proof.AesGcmSiv.AArch64 (tagInput_eq sealSat openSat sealFrameSat_pre openFrameSat_pre sealAArch64
  openAArch64 oneLay onePub args rounds openResult openPost sealPre openPre)
open VG.Proof.Gcm.AArch64.Pmull (PrepPow)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

/-! ## v8–v15 -/

theorem seal_keepsV (v : GcmImpl) : (Stitch.«seal» v.callees).allInstrs keepsV = true := by
  simp only [Stitch.«seal», keys, derive, expand, Stitch.polyval, Stitch.polyData, Stitch.ifBatch, absorb, absTail,
    absTailPre, chunk, chunkPre, chunkLen, revLoop, lens, tag, tagOut, Stitch.crypt, Stitch.cryptRest, cryptBlock,
    cryptTail, callCtr, callKey, callGh, Impl.AesGcm.AArch64.copyLoop, Impl.AesGcm.AArch64.xorLoop,
    Stitch.ghLoop, Stitch.ctrLoop, Impl.Gcm.AArch64.Stitch.byRounds, GcmImpl.callees, Code.allInstrs,
    v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]
  decide +kernel

theorem open_keepsV (v : GcmImpl) : (Stitch.«open» v.callees).allInstrs keepsV = true := by
  simp only [Stitch.«open», keys, derive, expand, Stitch.openData, Stitch.ifBatch, absorb, absTail, absTailPre, chunk,
    chunkPre, chunkLen, revLoop, lens, tag, recv, Stitch.cryptRest, cryptBlock, cryptTail, mask, callCtr, callKey,
    callGh, Impl.AesGcm.AArch64.copyLoop, Impl.AesGcm.AArch64.xorLoop, Stitch.openLoop,
    Impl.Gcm.AArch64.Stitch.byRounds, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]
  decide +kernel

/-! ## Correctness -/

theorem seal_correct (hP : PrepPow) (gh : Gh8Ok) (v : GcmImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa (Stitch.«seal» v.callees) s t s' ∧ abiPreserved s s' ∧ sealAArch64.post s s' :=
  WP.withPreservedV (seal_wp hP gh v tagInput_eq hs) (seal_keepsV v)

theorem open_correct (hP : PrepPow) (gh : Gh8Ok) (v : GcmImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa (Stitch.«open» v.callees) s t s' ∧ abiPreserved s s' ∧ openAArch64.post s s' :=
  WP.withPreservedV (open_wp hP gh v tagInput_eq hs) (open_keepsV v)

/-! ## The shared contracts, with the working space as an argument -/

theorem seal_verified (hP : PrepPow) (gh : Gh8Ok) (v : GcmImpl) :
    Verified AArch64.target (Stitch.«seal» v.callees) (Proof.AesGcmSiv.sealScratchContract AArch64.abi 476) :=
  Verified.of_correct (seal_correct hP gh v) (seal_ct hP gh v) (by
    sig_implies [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
      Spec.GcmSiv.sealPost, sealAArch64, sealPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs,
      AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat] using sealSat)

theorem open_verified (hP : PrepPow) (gh : Gh8Ok) (v : GcmImpl) :
    Verified AArch64.target (Stitch.«open» v.callees) (Proof.AesGcmSiv.openScratchContract AArch64.abi 476) :=
  Verified.of_correct (open_correct hP gh v) (open_ct hP gh v)
    { pre := by sig_implies_pre [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
        openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      -- `h` and the goal match on the same outcome of `decryptWith` with
      -- different matchers (`openPost`'s and `openContract`'s): split on it
      -- rather than have `exact h` unfold both to unify them.
      post := by
        intro s s' _ h
        sig_post [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
          openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
          AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
        sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
          openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
          AArch64.stackArgAddr, List.getD, List.range, List.range.loop] at h
        intro _
        split at h <;> rename_i heq <;> rw [heq] <;> exact h
      pub := by sig_implies_pub [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
        openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      sat := by sig_implies_sat [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
        openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop] [openSat, sealSat] using openSat }

theorem seal_framed (hP : PrepPow) (gh : Gh8Ok) (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 3824 0 (Stitch.«seal» v.callees))
      (Spec.GcmSiv.sealContract AArch64.abi 3824) :=
  AArch64.Verified.stackArgScratch (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64)
    (n := 476) (pre := Spec.GcmSiv.sealPre AArch64.abi.ptrBits)
    (post := Spec.GcmSiv.sealPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 3824)
    (seal_verified hP gh v) (by decide) (by decide) (sealPre_local _) (sealPost_local _) sealFrameSat_pre

theorem open_framed (hP : PrepPow) (gh : Gh8Ok) (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 3824 0 (Stitch.«open» v.callees))
      (Spec.GcmSiv.openContract AArch64.abi 3824) :=
  AArch64.Verified.stackArgScratch (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64)
    (n := 476) (pre := Spec.GcmSiv.openPre AArch64.abi.ptrBits)
    (post := Spec.GcmSiv.openPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 3824)
    (leak := some (Spec.GcmSiv.openLeak AArch64.abi.ptrBits))
    (Proof.AesGcmSiv.Verified.of_openScratch (open_verified hP gh v)) (by decide) (by decide) (openPre_local _)
    (openPost_local _) openFrameSat_pre
    (hleak := openLeak_local _)

/-! ## The code of each function -/

/-- `vg_aes_gcm_siv_seal`: interleaved if `v.stitch`. -/
def sealCode (v : GcmImpl) : Prog isa := if v.stitch then Stitch.«seal» v.callees else «seal» v.callees

/-- `vg_aes_gcm_siv_open`: interleaved if `v.stitch`. -/
def openCode (v : GcmImpl) : Prog isa := if v.stitch then Stitch.«open» v.callees else «open» v.callees

theorem sealCode_framed (hP : PrepPow) (gh : Gh8Ok) (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 3824 0 (sealCode v))
      (Spec.GcmSiv.sealContract AArch64.abi 3824) := by
  unfold sealCode
  split
  · exact seal_framed hP gh v
  · exact Proof.AesGcmSiv.AArch64.seal_framed v

theorem openCode_framed (hP : PrepPow) (gh : Gh8Ok) (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 3824 0 (openCode v))
      (Spec.GcmSiv.openContract AArch64.abi 3824) := by
  unfold openCode
  split
  · exact open_framed hP gh v
  · exact Proof.AesGcmSiv.AArch64.open_framed v

end VG.Proof.AesGcmSiv.AArch64.Stitch
