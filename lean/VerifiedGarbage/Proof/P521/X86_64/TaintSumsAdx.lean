import VerifiedGarbage.Proof.P521.X86_64.TaintSumsBase

/-!
# P-521 on x86-64 with BMI2 and ADX: summaries of the shared loops

As `TaintSums.lean`, for `p521x` (P-521 multiplying modulo `p` with BMI2 and
ADX), whose loops are the same but for their multiplications; ECDH's are in
`TaintSumsWinAdx`.
-/

namespace VG.Proof.P521.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64

/-- The comb's loop. -/
def combGX : Prog isa := .loop (p521x.combCfg p521d).step .ne

/-- The inversion's batches mod `p`. -/
def invPX : Prog isa := .loop p521x.invP.batch .ne

taint_summary combGXSum : (taintSym ["VG_P521_COMB"]) τL combGX
taint_summary invPXSum : (taintSym ["VG_P521_COMB"]) τI invPX

end VG.Proof.P521.X86_64
