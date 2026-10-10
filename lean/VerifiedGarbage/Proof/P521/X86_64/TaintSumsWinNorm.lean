import VerifiedGarbage.Proof.P521.X86_64.TaintSumsBase

/-!
# P-521 on x86-64: the summary of ECDH's table normalization

The normalization of the window method's table (an inversion by divsteps,
whose code the kernel builds here), in its own module so that it is checked
in parallel with the rest of `TaintSumsWin`. See `TaintSums`.
-/

namespace VG.Proof.P521.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64

/-- ECDH's window method in Jacobian coordinates: the table's normalization. -/
def winNormJ : Prog isa := WinCfg.normTbl winK (InvCfg.inv (Impl.Ecdh.X86_64.Cfg.invWin p521))

taint_summary_map winNormJSum : taintS τB winNormJ via taintS_eraseInv
  (by simp only [winNormJ, WinCfg.normTbl, Code.mapBlocks, winK_ok.fprogB]; rfl :
    Code.mapBlocks Instr.erase winNormJ = _)

end VG.Proof.P521.X86_64
