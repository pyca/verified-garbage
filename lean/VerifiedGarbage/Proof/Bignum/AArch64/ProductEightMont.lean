module

import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightGuardCT
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCallMont
public import VerifiedGarbage.Impl.Bignum.AArch64.ProductDispatch
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightGuard
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightGuardCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCallMont
meta import VerifiedGarbage.Impl.Bignum.AArch64.ProductDispatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightGuard
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section
namespace VG.Proof.Bignum.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum

/-- The existing Montgomery contract with eight-limb non-square products.
The shared five-bit CRT window uses this interface; other callers retain
their existing multiplication. -/
def Mont.productEight : Mont where
  mm := VG.Impl.Bignum.AArch64.ProductDispatch.mm
  ok := by
    intro s B Z w minv hg hz hw hw' o a b ho ha hb d1 d2 d3 d4 d5 d6 hinv hB
    by_cases heq : a ≠ b ∧ o ≠ aN
    · unfold VG.Impl.Bignum.AArch64.ProductDispatch.mm
      rw [ite_eq_left heq]
      exact ProductDispatch.guarded_ok hg hz hw hw' ho ha hb d1 d2 heq.2 d3 d4 d5 d6 hinv hB
    · simpa only [VG.Impl.Bignum.AArch64.ProductDispatch.mm, ite_eq_right heq, Mont.calledSquareEight] using
        (Mont.calledSquareEight.ok hg hz hw hw' ho ha hb d1 d2 d3 d4 d5 d6 hinv hB)
  ct := by
    have slow (o a b : Nat) (h : MmUse o a b) :
        RelCT isa (Two GoodW) (VG.Impl.Bignum.AArch64.SquareEightCall.mm o a b) (fun _ _ => True) :=
      Mont.calledSquareEight.ct (o := o) (a := a) (b := b) h
    intro o a b h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    all_goals
      unfold VG.Impl.Bignum.AArch64.ProductDispatch.mm
      first
      | rw [ite_eq_left (by decide)]
        exact ProductDispatch.guarded_ct (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by simp [MmUse])
          (by taint_decide) (by taint_decide) (by taint_decide)
          (by taint_decide) (by taint_decide) (by taint_decide)
      | rw [ite_eq_right (by decide)]
        exact slow _ _ _ (by simp [MmUse])

end VG.Proof.Bignum.AArch64
