import VerifiedGarbage.Proof.P521.X86_64.TaintSumsBase

/-!
# P-521 on x86-64 with BMI2 and ADX: the summary of ECDH's table normalization

The normalization of the window method's table (an inversion by divsteps,
whose code the kernel builds here), in its own module so that it is checked
in parallel with the rest of `TaintSumsWinAdx`. See `TaintSums`.
-/

namespace VG.Proof.P521.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64

/-- ECDH's window method in Jacobian coordinates: the table's normalization. -/
def winNormJX : Prog isa := WinCfg.normTbl winKX (InvCfg.inv (Impl.Ecdh.X86_64.Cfg.invWin p521x))

taint_summary_map winNormJXSum : taintS τB winNormJX via taintS_eraseInv
  (by simp only [winNormJX, WinCfg.normTbl, Code.mapBlocks, winKX_ok.fprogB]; rfl :
    Code.mapBlocks Instr.erase winNormJX = _)

end VG.Proof.P521.X86_64
