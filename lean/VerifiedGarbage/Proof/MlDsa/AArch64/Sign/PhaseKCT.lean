module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseK
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Rel
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseD
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Rel
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseK
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Rel
meta import VerifiedGarbage.Proof.MlDsa.Sign.Mem
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseD

/-!
# ML-DSA signing on AArch64: pieces of the checks that leak only their pointers

The comparison of the number of 1s of the hint with `ω` (`onesOk_taint`) and
the update of `κ` (`kapAdd_taint`) leak only their pointers.
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params}
include hP

/-! ## The checks -/

omit hP in
theorem onesOk_taint (p : Params) :
    (taint.check (AArch64.Taint.ofRegs bases) (.block (onesOk p)) (.block [])).isSome = true := by
  dsimp only [onesOk]; rfl

omit hP in
theorem kapAdd_taint (p : Params) :
    (taint.check (AArch64.Taint.ofRegs bases) (.block (kapAdd p)) (.block [])).isSome = true := by
  dsimp only [kapAdd]; rfl

end

end VG.Proof.MlDsa.AArch64.Sign
