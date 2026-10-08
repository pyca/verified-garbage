import VerifiedGarbage.Proof.P521.X86_64.TaintSums

/-!
# P-521 on x86-64 with BMI2 and ADX: summaries of the shared loops

As `TaintSums.lean`, for `p521x` (P-521 multiplying modulo `p` with BMI2 and
ADX), whose loops are the same but for their multiplications.
-/

namespace VG.Proof.P521.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

/-- The comb's loop. -/
def combGX : Prog isa := .loop (p521x.combCfg p521d).step .ne

/-- The inversion's batches mod `p`. -/
def invPX : Prog isa := .loop p521x.invP.batch .ne

taint_summary combGXSum : (taintSym ["VG_P521_COMB"]) τL combGX
taint_summary invPXSum : (taintSym ["VG_P521_COMB"]) τI invPX

/-- ECDH's window method. -/
abbrev winKX : WinCfg := p521x.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP

/-- ECDH's window method in Jacobian coordinates. -/
def winBuildJX : Prog isa := WinCfg.build winKX
def winNormJX : Prog isa := WinCfg.normTbl winKX (InvCfg.inv (Impl.Ecdh.X86_64.Cfg.invWin p521x))
def winLoopJX : Prog isa := .loop (WinCfg.stepJ winKX) .ne
def winLastJX : Prog isa := WinCfg.stepLast winKX

materialize_code winBuildJX
materialize_code winNormJX
materialize_code winLoopJX
materialize_code winLastJX

taint_summary winBuildJXSum : taintS τB winBuildJX
taint_summary winNormJXSum : taintS τB winNormJX
taint_summary winLoopJXSum : taintS τL winLoopJX
taint_summary winLastJXSum : taintS τL winLastJX

end VG.Proof.P521.X86_64
