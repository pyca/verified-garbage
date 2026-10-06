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

/-- ECDH's window method, which verification runs too. -/
abbrev winKX : WinCfg := p521x.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP

/-- The window method's table. -/
def winBuildX : Prog isa := WinCfg.build winKX

/-- The window method's loop. -/
def winLoopX : Prog isa := .loop (WinCfg.step winKX) .ne

materialize_code winBuildX
materialize_code winLoopX

taint_summary winBuildXSum : taintS τB winBuildX
taint_summary winLoopXSum : taintS τL winLoopX
taint_summary winBuildXSymSum : (taintSym ["VG_P521_COMB"]) τB winBuildX
taint_summary winLoopXSymSum : (taintSym ["VG_P521_COMB"]) τL winLoopX

end VG.Proof.P521.X86_64
