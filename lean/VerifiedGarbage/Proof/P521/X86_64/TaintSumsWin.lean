import VerifiedGarbage.Proof.P521.X86_64.TaintSumsBase

/-!
# P-521 on x86-64: summaries of ECDH's window method, for constant time

See `TaintSums`.
-/

namespace VG.Proof.P521.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64

/-- ECDH's window method in Jacobian coordinates: the table, the loop and
its last iteration (the table's normalization: `TaintSumsWinNorm`). -/
def winBuildJ : Prog isa := WinCfg.build winK
def winLoopJ : Prog isa := .loop (WinCfg.stepJ winK) .ne
def winLastJ : Prog isa := WinCfg.stepLast winK

materialize_code winBuildJ

taint_summary winBuildJSum : taintS τB winBuildJ
taint_summary_map winLoopJSum : taintS τL winLoopJ via taintS_eraseInv
  (by simp only [winLoopJ, WinCfg.stepJ, WinCfg.quadJ, WinCfg.jacPairOn, WinCfg.sumJ, Code.mapBlocks,
    winK_ok.fprogB]; rfl : Code.mapBlocks Instr.erase winLoopJ = _)
taint_summary_map winLastJSum : taintS τL winLastJ via taintS_eraseInv
  (by simp only [winLastJ, WinCfg.stepLast, WinCfg.quadJ, WinCfg.jacPairOn, WinCfg.toProjR, Code.mapBlocks,
    winK_ok.fprogB]; rfl : Code.mapBlocks Instr.erase winLastJ = _)

end VG.Proof.P521.X86_64
