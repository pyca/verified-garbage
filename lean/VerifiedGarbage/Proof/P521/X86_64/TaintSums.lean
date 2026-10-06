import VerifiedGarbage.Proof.Framework.X86_64.TaintSym
import VerifiedGarbage.Impl.Ecdsa.P521.X86_64

/-!
# P-521 on x86-64: summaries of the shared loops, for constant time

The signature, the public key and signature verification all run the
signature's code around their own: the comb from `G` and the batches of
the inversion of `Z` by divsteps. Their constant-time checks
(`taint_decide_sum`, with the address of the comb's static public:
`taintSym`) use these summaries (`taint_summary`), analysed once here, in
place of analysing the loops again in each check. Only the registers matter
(the analysis knows nothing about memory): the working space `rdi`, the
loop counter (`rbx` for the comb, `r14` for the batches) and `out` in `rsi`,
which every caller has public there and needs afterwards.

ECDH runs the inversion too, but without the comb's static its check is by
`taintS`, and the power mod `n` and ECDH's ladder are run by only two of the
functions: a summary costs more than their analysis in one more check (the
kernel builds the code here, while the callers' checks read it from their
literals), so they are analysed in full.
-/

namespace VG.Proof.P521.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

/-- P-521's comb. -/
abbrev p521d : CombData := ⟨7, Impl.P521.p521Comb7, Impl.P521.p521Comb7Start, "VG_P521_COMB"⟩

/-- The comb's loop. -/
def combG : Prog isa := .loop (p521.combCfg p521d).step .ne

/-- The inversion's batches mod `p`. -/
def invP : Prog isa := .loop p521.invP.batch .ne

/-- What is public at the comb's loop. -/
def τL : VG.X86_64.Taint.T := Taint.ofRegs [.rdi, .rbx, .rsi]

/-- What is public at the batches' loop. -/
def τI : VG.X86_64.Taint.T := Taint.ofRegs [.rdi, .r14, .rsi]

taint_summary combGSum : (taintSym ["VG_P521_COMB"]) τL combG
taint_summary invPSum : (taintSym ["VG_P521_COMB"]) τI invP

end VG.Proof.P521.X86_64
