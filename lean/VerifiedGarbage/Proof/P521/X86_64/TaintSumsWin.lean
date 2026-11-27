module

public import VerifiedGarbage.Proof.P521.X86_64.TaintSumsBase
public import VerifiedGarbage.Proof.P521.X86_64.FieldTmpl
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.P521.X86_64.TaintSumsBase
meta import VerifiedGarbage.Proof.P521.X86_64.FieldTmpl
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# P-521 on x86-64: summaries of ECDH's window method, for constant time

See `TaintSums`.
-/

@[expose] public section

namespace VG.Proof.P521.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64

/-- ECDH's window method in Jacobian coordinates: the table, its
normalization, the loop and its last iteration. -/
def winBuildJ : Prog isa := WinCfg.build winK
def winNormJ : Prog isa := WinCfg.normTbl winK (Impl.Ecdh.X86_64.Cfg.invWinProg p521)
def winLoopJ : Prog isa := .loop (WinCfg.stepJ winK) .ne
def winLastJ : Prog isa := WinCfg.stepLast winK

materialize_code winBuildJ

theorem winK_ok : p521T.Ok winK.M := p521HT_ok

theorem winK_lazy : WinCfg.lazyOk winK = false := by decide +kernel
theorem winK_quad : WinCfg.quadJ winK = WinCfg.quadG winK := by rw [WinCfg.quadJ, winK_lazy]; rfl
theorem winK_madd : WinCfg.maddP winK = fprogB winK.M (maddJ winK.S winK.R winK.E winK.D) := by
  rw [WinCfg.maddP, winK_lazy]; rfl

taint_summary winBuildJSum : taintS τB winBuildJ
taint_summary_map winNormJSum : taintS τB winNormJ via taintS_eraseInv
  (by simp only [winNormJ, WinCfg.normTbl, WinCfg.seqRange, WinCfg.prodStep, WinCfg.backStep,
    WinCfg.backOne, WinCfg.mulTb, WinCfg.mulTx, Code.mapBlocks, winK_ok.fprogB]; rfl :
    Code.mapBlocks Instr.erase winNormJ = _)
taint_summary_map winLoopJSum : taintS τL winLoopJ via taintS_eraseInv
  (by simp only [winLoopJ, WinCfg.stepJ, winK_quad, WinCfg.quadG, WinCfg.jacPairOn, WinCfg.sumJ, winK_madd, Code.mapBlocks,
    winK_ok.fprogB]; rfl : Code.mapBlocks Instr.erase winLoopJ = _)
taint_summary_map winLastJSum : taintS τL winLastJ via taintS_eraseInv
  (by simp only [winLastJ, WinCfg.stepLast, winK_quad, WinCfg.quadG, WinCfg.jacPairOn, WinCfg.toProjR, Code.mapBlocks,
    winK_ok.fprogB]; rfl : Code.mapBlocks Instr.erase winLastJ = _)

end VG.Proof.P521.X86_64
