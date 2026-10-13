module

public import VerifiedGarbage.Proof.Dsa.AArch64.AddCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.AddCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ProductCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ProductCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Timing of the multiply-and-add reduction step -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Impl.Dsa.AArch64

/-- The accumulator is reduced; its value need not agree between runs. -/
theorem reduceStep_ct (M : Mont) : RelCT isa (Two (Reduced [aY]))
    (Arithmetic.reduceStep M.mm) (fun _ _ => True) := by
  unfold Arithmetic.reduceStep
  refine RelCT.seq (two_post (Ψ := fun p s => GoodL p.layout s)
    (two_map (fun p : ProductPublic => p.layout.ws) (fun p _ h => ⟨_, h.1.good, p.fits⟩)
      (M.ct (o := aY) (a := aXm) (b := aY) (by unfold MmUse; decide))) ?_) ?_
  · intro p s ⟨hm, hred⟩
    exact WP.mono (M.mm_ok hm.good p.fits p.lower p.upper (o := aY) (a := aXm) (b := aY)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hm.inverse (by rw [hm.modulus]; exact hred aY (List.mem_singleton_self _)))
      fun t ⟨hg, _⟩ => ⟨hg, p.fits⟩
  exact two_map (fun p : ProductPublic => p.layout.ws)
    (fun p _ h => ⟨⟨_, h.1, p.fits⟩, by change 1 ≤ p.layout.w; have := p.lower; omega, p.upper⟩)
    (addCode_ct (by decide) (by decide) (by decide) (by taint_decide))

end VG.Proof.Dsa.AArch64
