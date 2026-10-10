import VerifiedGarbage.Proof.P521.X86_64.TaintSumsBase

/-!
# P-521 on x86-64: summaries of the shared loops, for constant time

The signature and the public key both run the signature's code around
their own: the comb from `G` and the batches of the inversion of `Z` by
divsteps. Their constant-time checks
(`taint_decide_sum`, with the address of the comb's static public:
`taintSym`) use these summaries (`taint_summary`), analysed once here, in
place of analysing the loops again in each check. Only the registers matter
(the analysis knows nothing about memory): the working space `rdi`, the
loop counter (`rbx` for the comb, `r14` for the batches), `out` in `rsi`
and `rsp` (for the calls of the field products), which every caller has
public there and needs afterwards.

ECDH runs the inversion too, but without the comb's static its check is by
`taintS`, and the power mod `n` is run by only two of the functions: a
summary costs more than its analysis in one more check (the kernel builds
the code here, while the callers' checks read it from their literals), so it
is analysed in full.

ECDH runs the window method in Jacobian coordinates (`WinCfg.windowJ`), whose
table of `[1 … 8]P` (seven complete additions), its normalization (an
inversion, by divsteps), loop and last iteration are each more than one check
can analyse along with the rest: they have summaries in `taintS`, with what
ECDH has public there (`rdi`, `rsi` and `rsp`, and the loop's counter `rbx`,
which is set after the table). The normalization, the loop and the last
iteration are analysed without their displacements (`taint_summary_map`),
their field products of slots past the functions' as one template each
(`FieldTmpl`), which the kernel neither builds nor analyses again per
product; the table's products are calls, whose code is shared already.

The summaries of the comb and the inversion are here; those of ECDH's window
method in `TaintSumsWin` and `TaintSumsWinNorm`, checked in parallel.
-/

namespace VG.Proof.P521.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64

/-- The comb's loop. -/
def combG : Prog isa := .loop (p521.combCfg p521d).step .ne

/-- The inversion's batches mod `p`. -/
def invP : Prog isa := .loop p521.invP.batch .ne

taint_summary combGSum : (taintSym ["VG_P521_COMB"]) τL combG
taint_summary invPSum : (taintSym ["VG_P521_COMB"]) τI invP

end VG.Proof.P521.X86_64
