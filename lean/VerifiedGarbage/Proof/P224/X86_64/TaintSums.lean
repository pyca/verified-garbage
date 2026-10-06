import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Impl.Ecdsa.P224.X86_64

/-!
# P-224 on x86-64: a summary of the shared ladder, for constant time

The signature, the public key and signature verification all run the
signature's ladder from `G`. Their constant-time checks (`taint_decide_sum`)
use this summary (`taint_summary`), analysed once here, in place of
analysing the loop again in each check. Only the registers matter (the
analysis knows nothing about memory): the working space `rdi`, the loop
counter `rbx` and `out` in `rsi`, which every caller has public there and
needs afterwards.
-/

namespace VG.Proof.P224.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

/-- The ladder from `G`. -/
def ladderG : Prog isa := .loop (ladderBody p224.ladderCfg) .ne

/-- What is public at the loop. -/
def τL : VG.X86_64.Taint.T := Taint.ofRegs [.rdi, .rbx, .rsi]

taint_summary ladderGSum : taintS τL ladderG

end VG.Proof.P224.X86_64
