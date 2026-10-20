module

import VerifiedGarbage.Proof.Dsa.X86_64.AddCT
public import VerifiedGarbage.Proof.Dsa.X86_64.ProductCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.AddCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ProductCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Timing of the multiply-and-add reduction step -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Dsa.X86_64

/-- The accumulator is reduced; its value need not agree between runs. -/
theorem reduceStep_ct (M : Mont) : RelCT isa (Two (Reduced [aY]))
    (Arithmetic.reduceStep M.mm) (fun _ _ => True) := by
  unfold Arithmetic.reduceStep
  refine RelCT.seq (mont_step_ct M (by unfold MmUse; decide) [aY] (by decide) (by decide)) ?_
  exact two_map (fun p : ProductPublic => p.layout.ws)
    (fun p _ h => ⟨⟨_, h.1.good, p.fits⟩, by change 1 ≤ p.layout.w; have := p.lower; omega, p.upper⟩)
    (addCode_ct (by decide) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide) (by taint_decide) (by taint_decide))

end VG.Proof.Dsa.X86_64
