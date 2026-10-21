module
public import Mathlib.Data.List.Dedup
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.AesGcm.Scratch
public import VerifiedGarbage.Impl.AesGcm.AArch64.Fast
public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups

import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Frame
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/-!
# AES-GCM on AArch64: `vg_aes_gcm_open`, with the path for TLS records where PMULL is there

Untrusted: everything here is checked by Lean. `openCode v` is `open` with
the path for TLS records (`Impl/AesGcm/AArch64/Fast.lean`) for the
implementations whose CPUs have PMULL (`GhashImpl.pmull`), which the path
runs inline, and `open` otherwise; both are `Verified` against `open`'s
contract (`openCode_framed`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64

/-- `vg_aes_gcm_open` for the implementations `v`. -/
def openCode (v : GcmImpl) : Prog isa :=
  if v.gh.pmull then Impl.AesGcm.AArch64.Fast.«open» v.callees else «open» v.callees

theorem fastOpenWithE_keepsV (v : GcmImpl) {k : Nat} (hk : k = 16 ∨ k = 24) {cl : Prog isa}
    (hcl : cl.allInstrs keepsV = true) :
    (Impl.AesGcm.AArch64.Fast.openWithE v.callees k cl).allInstrs keepsV = true := by
  rcases hk with rfl | rfl <;>
  simp only [Impl.AesGcm.AArch64.Fast.openWithE, Impl.AesGcm.AArch64.Fast.openFastP,
    Impl.AesGcm.AArch64.Fast.openRunWithP, Impl.AesGcm.AArch64.Fast.front, Impl.AesGcm.AArch64.Fast.cond,
    Impl.AesGcm.AArch64.Fast.padMul, Impl.AesGcm.AArch64.Fast.padMulT, Impl.AesGcm.AArch64.Fast.oneCryptT, Impl.AesGcm.AArch64.Tail.cryptAlT,
    Impl.AesGcm.AArch64.Tail.crSeg2T, Impl.AesGcm.AArch64.Tail.crTailT, openRest, openMain, oneCrypt, cryptAl, crArgs, tagLenOk,
    tagIn, cmpSeg, cmp, cmp16, j0, j0hash, oneAad, absorbAl, decAbs, fo, textAbs, finBody, tag,
    crSeg2, crTail, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, Impl.AesGcm.AArch64.xor,
    padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.gh.keepsV, hcl] <;>
  decide +kernel

theorem fastOpenWith_keepsV (v : GcmImpl) {gh : Fn} (hgh : gh.code.allInstrs keepsV = true) :
    (Impl.AesGcm.AArch64.Fast.openWith v.callees gh).allInstrs keepsV = true :=
  fastOpenWithE_keepsV v (.inl rfl) (by simp only [Code.allInstrs, hgh])

theorem fastOpen_correct (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Fast.«open» v.callees) s t s' ∧ abiPreserved s s' ∧
      openAArch64.post s s' :=
  WP.withPreservedV (Fast.openWith_wp v.gh.fn v hMK hs fun _ _ _ _ _ hc _ _ _ _ _ => gh_call v.gh hc)
    (fastOpenWith_keepsV v v.gh.keepsV)

theorem fastOpen_verified (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target (Impl.AesGcm.AArch64.Fast.«open» v.callees)
      (Proof.AesGcm.openScratchContract AArch64.abi) :=
  Verified.of_correct (fastOpen_correct v hMK) (Fast.open_fast_ct v hMK) (by
    sig_implies [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
      Spec.Gcm.openPost, Spec.Gcm.openLeak, openAArch64, openPre, openPreX, List.append_nil, onePub, openRes, openLeakOf, args, rounds,
      AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
      List.range.loop]
      [openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat)

theorem openCode_verified (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target (openCode v) (Proof.AesGcm.openScratchContract AArch64.abi) := by
  unfold openCode
  split
  · exact fastOpen_verified v hMK
  · exact open_verified v

theorem openCode_framed (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (openCode v))
      (Spec.Gcm.openContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Gcm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openPre AArch64.abi.ptrBits)
    (post := Spec.Gcm.openPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (leak := some (Spec.Gcm.openLeak AArch64.abi.ptrBits))
    (openCode_verified v hMK) (by decide) (by decide) (openPre_local _) (openPost_local _) openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.AesGcm.AArch64
