module
public import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Framework.X86.Taint


/-!
# ECDH on x86 (32-bit): what the field functions' summaries start from

The ladder calls the field functions modulo `p` from its own code and from
the point functions (`vg_<curve>_point_double`, `vg_<curve>_point_add`),
one frame deeper. On entry to either kind of call, the stack pointer, the
four words of the call's arguments and the working space's base are
public, with the output (`len` bytes, the first argument) and the working
space as the regions: `callτ len` and `nestedCallτ len`. A summary of each
field function from each of them applies at every call but the first of
each kind, whose taint also knows public slots of the working space
(summaries compare what the taints know of memory exactly).
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86

open VG VG.X86

/-- On entry to a field function the ladder's own code calls. -/
def callτ (len : Nat) : VG.X86.Taint.T :=
  { regs := ⟨215⟩, flags := false, lens := [16, len, 8192], bases := [(.edi, 2, 0), (.esp, 0, 4)],
    slots := ⟨[65535]⟩, wbases := [(0, 0, 2)], argLen := 20, argBases := [(4, 1), (16, 2)],
    stk := [none, some 16], room := 28 }

/-- On entry to a field function a point function calls. -/
def nestedCallτ (len : Nat) : VG.X86.Taint.T :=
  { regs := ⟨215⟩, flags := false, lens := [16, 4, len, 8192],
    bases := [(.edi, 3, 0), (.esp, 1, 24), (.esp, 0, 4)],
    slots := ⟨[65535]⟩, wbases := [(0, 0, 3)], argLen := 20, argBases := [(4, 2), (16, 3)],
    stk := [none, some 16, none, some 4], room := 28 }

end VG.Proof.Ecdh.X86
