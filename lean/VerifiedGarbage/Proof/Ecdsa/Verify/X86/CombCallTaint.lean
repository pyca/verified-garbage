module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.TaintMono

/-!
# ECDSA verification over P-256 on x86 (32-bit): what the comb's calls start from

The comb verifier's checks of the scalars (`CombMidCT`) and of the final
comparison (`CombFinalCT`) start from `scratchArgτ`, from which every call of
a field function has the stack pointer, the four words of its arguments and
the working space's base public, as `τV` says, but neither `esi` nor the
stack argument's base. `τComb` is `τV` without them, so that a summary from
it applies at every one of those calls: `taint_decide_sum` analyses a call in
full when its taint is not at least the summary's.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86

open VG VG.X86

/-- `τV` with `eax`, `ecx`, `edx`, `esp` and `edi` public, and no base of a
stack argument. -/
def τComb : VG.X86.Taint.T := { τV with regs := ⟨151⟩, argBases := [] }

end VG.Proof.Ecdsa.Verify.X86
