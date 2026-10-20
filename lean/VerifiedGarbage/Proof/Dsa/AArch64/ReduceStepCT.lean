module

import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
public import VerifiedGarbage.Proof.Dsa.AArch64.ProductCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
meta import VerifiedGarbage.Proof.Dsa.AArch64.ProductCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Timing of the multiply-and-add reduction step -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Impl.Dsa.AArch64

/-- The accumulator is reduced; its value need not agree between runs. -/
theorem reduceStep_ct (M : Mont) : RelCT isa (Two (Reduced [aY]))
    (Arithmetic.reduceStep M.mm) (fun _ _ => True) := by
  unfold Arithmetic.reduceStep
  refine RelCT.seq (mont_step_ct M (by unfold MmUse; decide) [aY] (by decide) (by decide)) ?_
  exact two_map (fun p : ProductPublic => p.layout.ws)
    (fun p _ h => ⟨_, h.1.good, p.fits⟩)
    (addMod_ct (by decide) (by decide) (by decide) (by taint_decide))

end VG.Proof.Dsa.AArch64
