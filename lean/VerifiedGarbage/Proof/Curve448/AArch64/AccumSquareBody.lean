module

import VerifiedGarbage.Proof.Curve448.AArch64.Bounds
public import VerifiedGarbage.Impl.X448.AArch64.Symmetric
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Proof.X448.Wide.CacheRegs
public import VerifiedGarbage.Proof.X448.Wide.Word
public import VerifiedGarbage.Proof.X448.Wide.Product
public import VerifiedGarbage.Proof.X448.Wide.Representation
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.Wide.Term
public import VerifiedGarbage.Impl.X448.AArch64.Wide
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `X448.Wide.DoubleTerm`, which this module and modules that import it used -/

section

/-! Untrusted: one doubled cross product in symmetric X448 squaring. -/

@[expose] public section

namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64 (mulHi read_x)
open VG.Proof.X448.AArch64 (Keeps)
open VG.Impl.X448.AArch64.Wide

theorem termFromDouble_ok (s : State) (a b : Reg) (hb : b ≠ .x10) (hb11 : b ≠ .x11)
    (ha : (s.gpr a).toNat < 2 ^ 63)
    (h : 2 * ((s.gpr a).toNat * (s.gpr b).toNat) + pair (s.gpr .x4) (s.gpr .x5) < 2 ^ 128) :
    WP isa (.block (termFromDouble a b)) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) =
        2 * ((s.gpr a).toNat * (s.gpr b).toNat) + pair (s.gpr .x4) (s.gpr .x5) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x10, .x11] s t := by
  apply WP.of_runBlock
  simp only [termFromDouble, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hb, hb11,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, (fun r hr => ?_), rfl, rfl⟩
  · have doubled : (s.gpr a + s.gpr a).toNat = 2 * (s.gpr a).toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega_using [ha])]
      omega_using []
    have cap : (s.gpr a + s.gpr a).toNat * (s.gpr b).toNat +
        pair (s.gpr .x4) (s.gpr .x5) < 2 ^ 128 := by
      rw [doubled, Nat.mul_assoc]; exact h
    have hv := madd128 (s.gpr a + s.gpr a) (s.gpr b) (s.gpr .x4) (s.gpr .x5) cap
    rw [doubled, Nat.mul_assoc] at hv
    dsimp only [addCarry, carryOut, mulHi, Size.bits] at hv ⊢
    exact hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr, ite_false]

end VG.Proof.X448.Wide

end

end

/-! Untrusted: accumulate a square diagonal into an existing coefficient. -/

@[expose] public section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64.Wide VG.Impl.X448.AArch64.Cached VG.Proof.X448.AArch64
theorem accumSquareBody_ok {s : State} {f : Nat → Nat} {k : Nat} (hk : k < 16)
    (fc : ∀ i < 8, (s.gpr (cacheReg i)).toNat = f i)
    (fb : ∀ i < 8, f i < weakBound) {c : Nat} (hc : c < 2 ^ 118)
    (hz : pair (s.gpr .x4) (s.gpr .x5) = c) :
    WP isa (.block (Impl.X448.AArch64.Symmetric.body k)) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) = c + rows f f 8 k ∧ t.mem = s.mem ∧ Keeps termRegs s t := by
  let inv := fun n (t : State) =>
    pair (t.gpr .x4) (t.gpr .x5) = c + sqrSum f k n ∧ t.mem = s.mem ∧ Keeps termRegs s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (if n ≤ k ∧ k < n + 8 ∧ n ≤ k - n then
      if n = k - n then termFrom (cacheReg n) (cacheReg (k - n))
      else termFromDouble (cacheReg n) (cacheReg (k - n)) else [])) t (inv (n + 1)) := by
    intro n t hn ⟨tv, tm, tk⟩
    by_cases h : n ≤ k ∧ k < n + 8 ∧ n ≤ k - n
    · rw [ite_eq_left h]
      have hj : k - n < 8 := by omega_using [h]
      have av : (t.gpr (cacheReg n)).toNat = f n := by rw [tk.1 _ (cacheReg_kept hn), fc n hn]
      have bv : (t.gpr (cacheReg (k - n))).toNat = f (k - n) := by
        rw [tk.1 _ (cacheReg_kept hj), fc (k - n) hj]
      have next := VG.Proof.Curve448.AArch64.sqrSum_bound fb (n := n + 1) (by omega_using [hn]) hk
      by_cases diag : n = k - n
      · rw [ite_eq_left diag]
        have sum : (t.gpr (cacheReg n)).toNat * (t.gpr (cacheReg (k - n))).toNat +
            pair (t.gpr .x4) (t.gpr .x5) < 2 ^ 128 := by
          rw [av, bv, tv]
          simp only [sqrSum, ite_eq_left h, ite_eq_left diag] at next
          omega_using [hc, next]
        refine WP.mono (termFrom_ok t _ _ (cacheReg_ne10 hn) (cacheReg_ne10 hj) sum) fun u ⟨uv, um, uk⟩ => ?_
        refine ⟨?_, um.trans tm, tk.trans uk⟩
        rw [uv, av, bv, tv, sqrSum, ite_eq_left h, ite_eq_left diag]
        omega_using []
      · rw [ite_eq_right diag]
        have sum : 2 * ((t.gpr (cacheReg n)).toNat * (t.gpr (cacheReg (k - n))).toNat) +
            pair (t.gpr .x4) (t.gpr .x5) < 2 ^ 128 := by
          rw [av, bv, tv]
          simp only [sqrSum, ite_eq_left h, ite_eq_right diag] at next
          omega_using [hc, next]
        refine WP.mono (termFromDouble_ok t _ _ (cacheReg_ne10 hj) (cacheReg_ne11 hj)
          (by rw [av]; exact Nat.lt_trans (fb n hn) (by decide : weakBound < 2 ^ 63)) sum) fun u ⟨uv, um, uk⟩ => ?_
        refine ⟨?_, um.trans tm, tk.trans uk⟩
        rw [uv, av, bv, tv, sqrSum, ite_eq_left h, ite_eq_right diag]
        omega_using []
    · rw [ite_eq_right h]
      apply WP.block_nil
      exact ⟨by rw [sqrSum, ite_eq_right h, Nat.add_zero]; exact tv, tm, tk⟩
  rw [Impl.X448.AArch64.Symmetric.body]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨by simpa only [sqrSum, Nat.add_zero] using hz, rfl, Keeps.refl _ _⟩) fun t ⟨tv, tm, tk⟩ => ?_
  rw [sqrSum_eq f hk] at tv
  exact ⟨tv, tm, tk⟩

end VG.Proof.Curve448.AArch64
