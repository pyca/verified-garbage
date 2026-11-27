module

public import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintSum

/-!
# ECDSA verification over P-256 on x86 (32-bit): what the comb's calls start from

The comb verifier's checks of the scalars (`CombMidCT`) and of the final
comparison (`CombFinalCT`) start from `scratchArgτ`, from which every call of
a field function has the stack pointer, the four words of its arguments and
the working space's base public (`τV`), but neither `esi` nor the
stack argument's base. `τComb` is `τV` without them, so that a summary from
it applies at every one of those calls: `taint_decide_sum` analyses a call in
full when its taint is not at least the summary's.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86

open VG VG.X86

/-- What is public on entry to every call of the field functions. -/
def τV : VG.X86.Taint.T :=
  { regs := ⟨215⟩, flags := false, lens := [16, 8192], bases := [(.edi, 1, 0), (.esp, 0, 4)],
    slots := [(0, 12, 4), (0, 8, 4), (0, 4, 4), (0, 0, 4)], wbases := [(0, 0, 1)], argLen := 20,
    argBases := [(16, 1)], stk := [none, some 16], room := 20 }

/-- `τV` with `eax`, `ecx`, `edx`, `esp` and `edi` public, and no base of a
stack argument. -/
def τComb : VG.X86.Taint.T := { τV with regs := ⟨151⟩, argBases := [] }

/-- What is public on entry to every call of the field functions from ECDH's
windows, which `VerifyLadderCT.ladder` checks from `scratchArgτ`: `τV`
without the base of a stack argument. A summary from it applies at each of
those calls. -/
def τWin : VG.X86.Taint.T := { τV with argBases := [] }

end VG.Proof.Ecdsa.Verify.X86
