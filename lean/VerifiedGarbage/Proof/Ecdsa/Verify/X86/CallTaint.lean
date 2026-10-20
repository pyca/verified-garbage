module

public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintSum

/-!
# ECDSA verification on x86 (32-bit): what the field functions' summaries start from

Verification calls its curve's field functions 224 times (95 products
modulo `p`, 87 sums, 31 differences and 11 calls modulo `n`), from taints
that all have at least `τV` public on entry to the function: the stack
pointer, the four words of the call's arguments and the working space's
base. For P-521 and brainpoolP512r1, whose field functions are the
largest, the summaries of the functions (`<curve>/CallSumsP`,
`<curve>/CallSumsN`, each checked in a module of its own, in parallel)
analyse each function once, in place of every call (`verify_ct`). The other
curves' checks analyse every call, with the hint computed in compiled code
(`native_taint_decide`), which costs less than computing the hint with
summaries in the interpreter.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86

open VG VG.X86

/-- What is public on entry to every call of the field functions. -/
def τV : VG.X86.Taint.T :=
  { regs := ⟨215⟩, flags := false, lens := [16, 8192], bases := [(.edi, 1, 0), (.esp, 0, 4)],
    slots := [(0, 12, 4), (0, 8, 4), (0, 4, 4), (0, 0, 4)], wbases := [(0, 0, 1)], argLen := 20,
    argBases := [(16, 1)], stk := [none, some 16], room := 20 }

/-- `τV` where the whole-function checks (`verify_ct`) call the field
functions from the verifier's own code: their stack below uses 28 bytes. -/
def τVTop : VG.X86.Taint.T := { τV with room := 28 }

/-- On entry to a field function that a point function
(`vg_<curve>_point_double`, `vg_<curve>_point_add`) calls, one frame below
the verifier's: that frame's return address and 4-byte argument are on the
stack too. -/
def τVPoint : VG.X86.Taint.T :=
  { regs := ⟨215⟩, flags := false, lens := [16, 4, 8192],
    bases := [(.edi, 2, 0), (.esp, 1, 24), (.esp, 0, 4)],
    slots := ⟨[65535]⟩, wbases := [(0, 0, 2)], argLen := 20, argBases := [(16, 2)],
    stk := [none, some 16, none, some 4], room := 28 }

end VG.Proof.Ecdsa.Verify.X86
