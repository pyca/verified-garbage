import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.X86.TaintMono

/-!
# ECDSA verification on x86 (32-bit): what the field functions' summaries start from

Verification calls its curve's field functions 224 times (95 products
modulo `p`, 87 sums, 31 differences and 11 calls modulo `n`), from taints
that all have at least `τV` public on entry to the function: the stack
pointer, the four words of the call's arguments and the working space's
base. The summaries of the functions (`<curve>/CallSumsP`,
`<curve>/CallSumsN`, each checked in a module of its own, in parallel)
analyse each function once, in place of every call (`verify_ct`).
-/

namespace VG.Proof.Ecdsa.Verify.X86

open VG VG.X86

/-- What is public on entry to every call of the field functions. -/
def τV : VG.X86.Taint.T :=
  { regs := ⟨215⟩, flags := false, lens := [16, 8192], bases := [(.edi, 1, 0), (.esp, 0, 4)],
    slots := [(0, 12, 4), (0, 8, 4), (0, 4, 4), (0, 0, 4)], wbases := [(0, 0, 1)], argLen := 20,
    argBases := [(16, 1)], stk := [none, some 16], room := 20 }

end VG.Proof.Ecdsa.Verify.X86
