module

public import VerifiedGarbage.Proof.Framework.X86.TaintMono
public import VerifiedGarbage.Impl.Camellia.X86.Prepared
import VerifiedGarbage.Proof.Camellia.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Impl.Camellia.X86.Prepared
meta import VerifiedGarbage.Proof.Camellia.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# The constant-time analysis of the x86 modes' calls of Camellia, once

Every mode (`Impl/Camellia/X86/Modes.lean`, `Ctr.lean`) calls
`vg_camellia_crypt_prepared` from the same stack, at the same taint
(`τCrypt`): the call's frame of arguments the first writable region (its
words public, the second the base address of the scratch buffer), then the
data, the IV and the scratch buffer, `esp`, `ecx` and `edi` public, the
scratch buffer's base in `edi` and `ecx`, and the modes' data pointer and
steps left public in their slots. The analysis of the call is a summary
(`taint_summary`), which the modes' checks use (`taint_decide_sum`) in place
of the analysis of the function in each.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86

/-- What the modes have public at their calls of `vg_camellia_crypt_prepared`. -/
def τCrypt : VG.X86.Taint.T :=
  { regs := .ofList [.ecx, .esp, .edi], flags := false, lens := [12, 0, 16, 2728],
    bases := [(.edi, 3, 0), (.ecx, 3, 0), (.esp, 0, 0)], slots := .ofList [(0, 0, 12), (3, 2704, 8)],
    wbases := [(0, 4, 3)], argLen := 28, argBases := [(16, 1), (12, 2), (24, 3)], stk := [some 12], room := 16 }

taint_summary cryptCallSum : VG.X86.taint τCrypt
  (.call (Spec.Camellia.Prepared.cryptApi Impl.Camellia.X86.layout).name Impl.Camellia.X86.cryptPrepared)

end VG.Proof.Camellia.X86
