module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.CT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Frame
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Verified
import VerifiedGarbage.Spec.Gcm.Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM on AArch64: `vg_aes_gcm_seal`, with the path for TLS records where PMULL is there

Untrusted: everything here is checked by Lean. `sealCode v` is `seal` with
the path for TLS records (`Impl/AesGcm/AArch64/Fast.lean`) for the
implementations whose CPUs have PMULL (`GhashImpl.pmull`), which the path
runs inline, and `seal` otherwise; both are `Verified` against `seal`'s
contract (`sealCode_framed`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64

/-- `vg_aes_gcm_seal` for the implementations `v`. -/
def sealCode (v : GcmImpl) : Prog isa :=
  if v.gh.pmull then Impl.AesGcm.AArch64.Fast.«seal» v.callees else «seal» v.callees

theorem fastSealWithE_keepsV (v : GcmImpl) {k : Nat} (hk : k = 8 ∨ k = 16) {cl : Prog isa}
    (hcl : cl.allInstrs keepsV = true) :
    (Impl.AesGcm.AArch64.Fast.sealWithE v.callees k cl).allInstrs keepsV = true := by
  rcases hk with rfl | rfl <;>
  simp only [Impl.AesGcm.AArch64.Fast.sealWithE, Impl.AesGcm.AArch64.Fast.runWithP, Impl.AesGcm.AArch64.Fast.front,
    Impl.AesGcm.AArch64.Fast.cond, Impl.AesGcm.AArch64.Fast.padMul, cryptAl, crSeg2, crTail,
    sealRest, j0, j0hash, oneAad, absorbAl, encBody, fo, textAbs, finBody, tag, crypt, crSeg1,
    ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees,
    Code.allInstrs, v.ctr.keepsV, v.gh.keepsV, hcl] <;> decide +kernel

theorem fastSealWith_keepsV (v : GcmImpl) {gh : Fn} (hgh : gh.code.allInstrs keepsV = true) :
    (Impl.AesGcm.AArch64.Fast.sealWith v.callees gh).allInstrs keepsV = true :=
  fastSealWithE_keepsV v (.inl rfl) (by simp only [Code.allInstrs, hgh])

theorem fastSeal_keepsV (v : GcmImpl) : (Impl.AesGcm.AArch64.Fast.«seal» v.callees).allInstrs keepsV = true :=
  fastSealWith_keepsV v v.gh.keepsV

theorem fastSeal_correct (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Fast.«seal» v.callees) s t s' ∧ abiPreserved s s' ∧
      sealAArch64.post s s' :=
  WP.withPreservedV (Fast.seal_wp v hMK hs) (fastSeal_keepsV v)

theorem fastSeal_verified (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target (Impl.AesGcm.AArch64.Fast.«seal» v.callees)
      (Proof.AesGcm.sealScratchContract AArch64.abi) :=
  Verified.of_correct (fastSeal_correct v hMK) (Fast.seal_ct v hMK) (by
    sig_implies [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre,
      Spec.Gcm.sealPost, sealAArch64, sealPre, sealPreX, List.append_nil, onePub, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem sealCode_verified (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target (sealCode v) (Proof.AesGcm.sealScratchContract AArch64.abi) := by
  unfold sealCode
  split
  · exact fastSeal_verified v hMK
  · exact seal_verified v

theorem sealCode_framed (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (sealCode v))
      (Spec.Gcm.sealContract AArch64.abi 2576) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.sealPre AArch64.abi.ptrBits)
    (post := Spec.Gcm.sealPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2576)
    (sealCode_verified v hMK) (by decide) (by decide) (sealPre_local _) (sealPost_local _) sealFrameSat_pre

open VG.Proof.AesGcm.AArch64.Gather in
/-- `sealWithE` has no frames of its own. -/
theorem fastSealWithE_depth0 (v : GcmImpl) {k : Nat} (hk : k = 8 ∨ k = 16) {cl : Prog isa}
    (hcl : cl.aarch64Depth = 0) : (Impl.AesGcm.AArch64.Fast.sealWithE v.callees k cl).aarch64Depth = 0 := by
  rcases hk with rfl | rfl <;>
  simp only [Impl.AesGcm.AArch64.Fast.sealWithE, Impl.AesGcm.AArch64.Fast.runWithP, Impl.AesGcm.AArch64.Fast.front,
    Impl.AesGcm.AArch64.Fast.cond, Impl.AesGcm.AArch64.Fast.padMul, cryptAl, crSeg2, crTail, sealRest, j0, j0hash,
    oneAad, absorbAl, encBody, fo, textAbs, finBody, tag, crypt, crSeg1, ctrCall, ghCall, absorb, absSeg1, absTail,
    minK, copy, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.aarch64Depth,
    depth_of_noFrames v.ctr.noFrames, depth_of_noFrames v.gh.noFrames, hcl] <;> decide

open VG.Proof.AesGcm.AArch64.Gather in
/-- The frames of `sealWith v gh`, in its frame of 2576 bytes, use at most those. -/
theorem fastSealWith_depth (v : GcmImpl) {gh : Fn} (hgh : gh.code.noFrames = true) :
    16 * (Impl.StackScratch.AArch64.withStackArgScratch 2576 1
      (Impl.AesGcm.AArch64.Fast.sealWith v.callees gh)).aarch64Depth ≤ 2576 := by
  simp only [Impl.StackScratch.AArch64.withStackArgScratch, Impl.AesGcm.AArch64.Fast.sealWith, Code.aarch64Depth,
    Instr.frameUnits, fastSealWithE_depth0 v (.inl rfl) (cl := .call gh.name gh.code)
      (by simp only [Code.aarch64Depth, depth_of_noFrames hgh])]
  decide

open VG.Proof.AesGcm.AArch64.Gather in
/-- The frames of `sealCode v`, in its frame of 2576 bytes, use at most those. -/
theorem sealCode_depth (v : GcmImpl) :
    16 * (Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (sealCode v)).aarch64Depth ≤ 2576 := by
  unfold sealCode
  split
  · exact fastSealWith_depth v v.gh.noFrames
  · exact seal_depth v

end VG.Proof.AesGcm.AArch64
