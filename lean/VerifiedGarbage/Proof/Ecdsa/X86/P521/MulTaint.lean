import VerifiedGarbage.Proof.Ecdsa.X86.P521.Lit
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.TaintMono

/-!
# ECDSA over P-521 on x86 (32-bit): what the multiplications' summaries start from

The summaries of the multiplications modulo `p` (`MulSumP`) and `n`
(`MulSumN`), each checked in a module of its own, in parallel, for the
signature's constant-time check (`Verified`).
-/

namespace VG.Proof.Ecdsa.X86.P521

open VG VG.X86

/-- What is public on entry to every call of the multiplications: the stack
pointer and the four words of its arguments' frame, below the return
address. Their calls are entered from several taints (with more public:
registers, the flags, or the slots of a table in the working space), each
analysing the body again in full; the summaries analyse each once. -/
def τMul : VG.X86.Taint.T :=
  { regs := ⟨215⟩, flags := false, lens := [16, 132, 8192], bases := [(.edi, 2, 0), (.esp, 0, 4)],
    slots := [(0, 12, 4), (0, 8, 4), (0, 4, 4), (0, 0, 4)], wbases := [(0, 0, 2)], argLen := 24,
    argBases := [(4, 1), (20, 2)], stk := [none, some 16], room := 20 }

end VG.Proof.Ecdsa.X86.P521
