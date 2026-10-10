import VerifiedGarbage.Proof.P521.X86_64.TaintSumsBase

/-!
# P-521 on x86-64 with BMI2 and ADX: summaries of ECDH's window method

As `TaintSumsWin.lean`, for `p521x`.
-/

namespace VG.Proof.P521.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64

/-- ECDH's window method in Jacobian coordinates. -/
def winBuildJX : Prog isa := WinCfg.build winKX
def winLoopJX : Prog isa := .loop (WinCfg.stepJ winKX) .ne
def winLastJX : Prog isa := WinCfg.stepLast winKX

materialize_code winBuildJX

taint_summary winBuildJXSum : taintS τB winBuildJX
taint_summary_map winLoopJXSum : taintS τL winLoopJX via taintS_eraseInv
  (by simp only [winLoopJX, WinCfg.stepJ, WinCfg.quadJ, WinCfg.jacPairOn, WinCfg.sumJ, Code.mapBlocks,
    winKX_ok.fprogB]; rfl : Code.mapBlocks Instr.erase winLoopJX = _)
taint_summary_map winLastJXSum : taintS τL winLastJX via taintS_eraseInv
  (by simp only [winLastJX, WinCfg.stepLast, WinCfg.quadJ, WinCfg.jacPairOn, WinCfg.toProjR, Code.mapBlocks,
    winKX_ok.fprogB]; rfl : Code.mapBlocks Instr.erase winLastJX = _)

end VG.Proof.P521.X86_64
