import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Impl.Ecdsa.P521.X86_64

/-!
# P-521 on x86-64: summaries of the shared loops, for constant time

The signature, the public key, ECDH and signature verification all run the
signature's code around their own: the ladder from `G` (all but ECDH) and
the power `Z^(p-2)` (all four). Their constant-time checks
(`taint_decide_sum`) use these summaries (`taint_summary`), analysed once
here, in place of analysing the loops again in each check. Only the
registers matter (the analysis knows nothing about memory): the working
space `rdi`, the loop counter `rbx` and `out` in `rsi`, which every caller
has public there and needs afterwards.

ECDH's ladder and the power mod `n` are run by only two of the four: a
summary costs more than their analysis in one more check (the kernel
builds the code here, while the callers' checks read it from their
literals), so they are analysed in full.
-/

namespace VG.Proof.P521.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

/-- The ladder from `G`. -/
def ladderG : Prog isa := .loop (ladderBody p521.ladderCfg) .ne

/-- The power mod `p`. -/
def powP : Prog isa := .loop (powBody p521.powP) .ne

/-- What is public at both loops. -/
def τL : VG.X86_64.Taint.T := Taint.ofRegs [.rdi, .rbx, .rsi]

taint_summary ladderGSum : taintS τL ladderG
taint_summary powPSum : taintS τL powP

end VG.Proof.P521.X86_64
