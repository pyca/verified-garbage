import VerifiedGarbage.Proof.P521.X86_64.TaintSumsBase

/-!
# P-521 on x86-64: summaries of ECDH's window method, for constant time

See `TaintSums`.
-/

namespace VG.Proof.P521.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64

/-- ECDH's window method in Jacobian coordinates: the table, its
normalization, the loop and its last iteration. -/
def winBuildJ : Prog isa := WinCfg.build winK
def winNormJ : Prog isa := WinCfg.normTbl winK (InvCfg.inv (Impl.Ecdh.X86_64.Cfg.invWin p521))
def winLoopJ : Prog isa := .loop (WinCfg.stepJ winK) .ne
def winLastJ : Prog isa := WinCfg.stepLast winK

materialize_code winBuildJ

theorem winK_ok : p521T.Ok winK.M := p521T_ok

taint_summary winBuildJSum : taintS τB winBuildJ
taint_summary_map winNormJSum : taintS τB winNormJ via taintS_eraseInv
  (by simp only [winNormJ, WinCfg.normTbl, Code.mapBlocks, winK_ok.fprogB]; rfl :
    Code.mapBlocks Instr.erase winNormJ = _)
taint_summary_map winLoopJSum : taintS τL winLoopJ via taintS_eraseInv
  (by simp only [winLoopJ, WinCfg.stepJ, WinCfg.quadJ, WinCfg.jacPairOn, WinCfg.sumJ, Code.mapBlocks,
    winK_ok.fprogB]; rfl : Code.mapBlocks Instr.erase winLoopJ = _)
taint_summary_map winLastJSum : taintS τL winLastJ via taintS_eraseInv
  (by simp only [winLastJ, WinCfg.stepLast, WinCfg.quadJ, WinCfg.jacPairOn, WinCfg.toProjR, Code.mapBlocks,
    winK_ok.fprogB]; rfl : Code.mapBlocks Instr.erase winLastJ = _)

end VG.Proof.P521.X86_64
