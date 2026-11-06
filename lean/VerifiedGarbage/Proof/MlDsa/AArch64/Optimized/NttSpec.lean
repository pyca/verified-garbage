module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
public import VerifiedGarbage.Proof.MlDsa.Arith.Ntt
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Arithmetic
import Std.Data.DTreeMap.Internal.Operations
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith

/-- Butterflies acting on disjoint coefficient pairs commute. This is the
only reordering needed to fuse independent outer and inner NTT slices. -/
theorem bfly_comm (w : Poly) {j len k step : Nat} (hl : 0 < len) (hm : 0 < step)
    (hj : j + len < n) (hk : k + step < n)
    (h00 : j ≠ k) (h01 : j ≠ k + step) (h10 : j + len ≠ k) (h11 : j + len ≠ k + step)
    (z t : Zq) :
    bfly (bfly w j len z) k step t = bfly (bfly w k step t) j len z := by
  apply ext_getElem!
  intro i hi
  rw [bfly_get (bfly w j len z) hm hk t hi, bfly_get (bfly w k step t) hl hj z hi,
    bfly_get w hl hj z (by omega : k < n), bfly_get w hl hj z hk,
    bfly_get w hl hj z hi, bfly_get w hm hk t (by omega : j < n),
    bfly_get w hm hk t hj, bfly_get w hm hk t hi]
  simp only [h00, h01, h10, h11, Ne.symm h00, Ne.symm h01, Ne.symm h10,
    Ne.symm h11, ite_false]
  by_cases h0 : i=k <;> by_cases h1 : i=k+step <;>
    by_cases h2 : i=j <;> by_cases h3 : i=j+len <;> simp_all

end VG.Proof.MlDsa.AArch64.Optimized
