import VerifiedGarbage.Proof.P384.X86_64.TaintSums

/-!
# P-384 on x86-64 with BMI2 and ADX: summaries of the shared loops

As `TaintSums.lean`, for `p384x` (P-384 multiplying modulo `p` with BMI2 and
ADX), whose loops are the same but for their multiplications.
-/

namespace VG.Proof.P384.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

/-- The ladder from `G`. -/
def ladderGX : Prog isa := .loop (ladderBody p384x.ladderCfg) .ne

/-- The power mod `p`. -/
def powPX : Prog isa := .loop (powBody p384x.powP) .ne

taint_summary ladderGXSum : taintS τL ladderGX
taint_summary powPXSum : taintS τL powPX

end VG.Proof.P384.X86_64
