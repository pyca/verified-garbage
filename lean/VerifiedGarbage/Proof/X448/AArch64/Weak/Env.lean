module

import VerifiedGarbage.Proof.Curve448.AArch64.Swap
public import VerifiedGarbage.Proof.X448.AArch64.Env
public import VerifiedGarbage.Proof.Curve448.AArch64.Normalize
public import VerifiedGarbage.Impl.Curve448.AArch64
import VerifiedGarbage.Proof.Curve448.AArch64.Stage
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Impl.X448.AArch64.Weak
public import VerifiedGarbage.Proof.X448.AArch64.Mul
public import VerifiedGarbage.Proof.X448.Wide.Representation
public import VerifiedGarbage.Proof.X448.Wide.Word
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Curve448.AArch64.Bounds
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.X448.AArch64.Symmetric
public import VerifiedGarbage.Proof.X448.Wide.CacheRegs
public import VerifiedGarbage.Proof.X448.Wide.Memory
public import VerifiedGarbage.Proof.X448.Wide.Product
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Impl.X448.AArch64.Wide
import VerifiedGarbage.Proof.X448.Wide.Term
public import VerifiedGarbage.Proof.X448.Wide.Column
import VerifiedGarbage.Proof.X448.Wide.CoefficientIO
import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Ed25519.Word64
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! ### `Curve448.AArch64.SymmetricColumn`, which this module and modules that import it used -/

section

/-! ### `Curve448.AArch64.AccumSquareBody`, which this module and modules that import it used -/

section

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

end

end

/-! Untrusted: store a symmetric square diagonal. -/

@[expose] public section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ACC)
open VG.Impl.X448.AArch64.Wide VG.Impl.X448.AArch64.Cached VG.Proof.X448.AArch64

theorem symmetricColumn_ok {s : State} {base : Addr} (hs : Scr s base) {f : Nat → Nat} {k : Nat}
    (hk : k < 16) (fc : ∀ i < 8, (s.gpr (cacheReg i)).toNat = f i)
    (fb : ∀ i < 8, f i < weakBound) :
    WP isa (.block (Impl.X448.AArch64.Symmetric.column k)) s fun t =>
      coeff t.mem base ACC k = rows f f 8 k ∧
      Outside base (ACC + 16 * k) 16 s.mem t.mem ∧ Keeps termRegs s t := by
  rw [Impl.X448.AArch64.Symmetric.column, List.append_assoc, WP.block_append_iff]
  refine WP.mono (zero_ok s) fun u ⟨uz, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  have uk' : Keeps termRegs s u := uk.mono (by decide)
  refine WP.mono (accumSquareBody_ok hk (by
    intro i hi; rw [uk'.1 _ (cacheReg_kept hi)]; exact fc i hi) fb (by decide) uz)
    fun v ⟨vv, vm, vk⟩ => ?_
  have vs := (hs.of_keeps uk (by decide)).of_keeps vk (by decide)
  refine WP.mono (store_ok vs hk) fun t ⟨tm, tk⟩ => ?_
  refine ⟨?_, ?_, uk'.trans (vk.trans (tk.mono (by decide)))⟩
  · rw [tm, coeff_put _ base _ _ (by simp only [ACC]; omega_using [hk])
      (by simp only [ACC]; omega_using [hk]), ite_eq_left rfl, vv, Nat.zero_add]
  · rw [tm, vm, um]
    exact putCoeff_outside _ _ _ _ (by simp only [ACC]; omega_using [hk])
end VG.Proof.Curve448.AArch64

end

end

/-! ### `X448.Wide.LoadCached`, which this module and modules that import it used -/

section

/-! Untrusted: load eight wide limbs into the cached operand registers. -/

@[expose] public section

namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld)
open VG.Impl.X448.AArch64.Cached VG.Proof.X448.AArch64

theorem cacheLoadStep_ok {s : State} {base : Addr} (hs : Scr s base) {a i : Nat}
    (ha : a + 64 ≤ 8192) (ha8 : a % 8 = 0) (hi : i < 8) :
    WP isa (.block [ld (cacheReg i) (a + 8 * i)]) s fun t =>
      t.gpr (cacheReg i) = word s.mem base (a + 8 * i) ∧
      t.mem = s.mem ∧ Keeps [cacheReg i] s t := by
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := ⟨by omega_using [ha8], by omega_using [ha, hi]⟩
  have al := hs.read (d := a + 8 * i) (n := 8) (by omega_using [ha, hi])
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, and_self, State.load, hs.x3, al, ite_true, Option.map_some,
    Option.bind_some, BitVec.setWidth_eq, read8_eq, RegUpd.gpr_write,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem loadCached_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat}
    (ha : a + 64 ≤ 8192) (ha8 : a % 8 = 0) :
    WP isa (.block (loadCached a)) s fun t =>
      (∀ i < 8, t.gpr (cacheReg i) = word s.mem base (a + 8 * i)) ∧
      t.mem = s.mem ∧ Keeps sqrRegs s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, t.gpr (cacheReg i) = word s.mem base (a + 8 * i)) ∧
    t.mem = s.mem ∧ Keeps sqrRegs s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block [ld (cacheReg n) (a + 8 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (cacheLoadStep_ok (hs.of_keeps tk (by decide)) ha ha8 hn) fun u ⟨uf, um, uk⟩ => ?_
    refine ⟨?_, um.trans tm, tk.trans (uk.mono (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact cacheReg_member hn))⟩
    intro i hi
    by_cases h : i = n
    · subst i; rw [uf, tm]
    · rw [uk.1 _ (by
        simp only [List.mem_singleton]
        intro e; exact h ((cacheReg_inj (by omega_using [hn, hi]) hn).1 e))]
      exact tf i (by omega_using [hi, h])
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, rfl, Keeps.refl _ _⟩

end VG.Proof.X448.Wide

end

end

/-! ### `Curve448.AArch64.Product`, which this module and modules that import it used -/

section

/-! ### `X448.Wide.Reduce`, which this module and modules that import it used -/

section

/-! ### `X448.Wide.AddCoefficient`, which this module and modules that import it used -/

section

/-! Untrusted: wide coefficient addition for reduction modulo the X448 prime. -/

@[expose] public section

namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st ACC TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64 (read_x)

theorem addRegs_ok (s : State)
    (h : pair (s.gpr .x4) (s.gpr .x5) + pair (s.gpr .x6) (s.gpr .x9) < 2 ^ 128) :
    WP isa (.block [.adds .x .x4 .x4 .x6, .adcs .x .x5 .x5 .x9]) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) =
        pair (s.gpr .x4) (s.gpr .x5) + pair (s.gpr .x6) (s.gpr .x9) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, (fun r hr => ?_), rfl, rfl⟩
  · have hv := addPair128 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x9) h
    dsimp only [addCarry, carryOut, Size.bits] at hv ⊢
    exact hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_addWithCarry, hr, ite_false]

theorem addCoeff_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 16)
    (h : pair (s.gpr .x4) (s.gpr .x5) + coeff s.mem base ACC i < 2 ^ 128) :
    WP isa (.block (addCoeff i)) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) = pair (s.gpr .x4) (s.gpr .x5) + coeff s.mem base ACC i ∧
      t.mem = s.mem ∧ Keeps colRegs s t := by
  rw [show addCoeff i = [ld .x6 (ACC + 16 * i), ld .x9 (ACC + 16 * i + 8)] ++
    [.adds .x .x4 .x4 .x6, .adcs .x .x5 .x5 .x9] from rfl, WP.block_append_iff]
  have load := loadTerm_ok hs (a := ACC + 16 * i) (b := ACC + 16 * i + 8)
    (i := 0) (j := 0) (by simp only [ACC]; omega_using [hi]) (by simp only [ACC]; omega_using [hi])
    (by simp only [ACC]; omega_using []) (by simp only [ACC]; omega_using []) (by decide) (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at load
  refine WP.mono load fun u ⟨u6, u9, um, uk⟩ => ?_
  have uv : pair (u.gpr .x4) (u.gpr .x5) = pair (s.gpr .x4) (s.gpr .x5) := by
    rw [uk.1 .x4 (by decide), uk.1 .x5 (by decide)]
  have up : pair (u.gpr .x6) (u.gpr .x9) = coeff s.mem base ACC i := by rw [u6, u9]
  refine WP.mono (addRegs_ok u (by rw [uv, up]; exact h)) fun t ⟨tv, tm, tk⟩ => ?_
  exact ⟨by rw [tv, uv, up], tm.trans um, (uk.mono (by decide)).trans (tk.mono (by decide))⟩

theorem addCoeffs_ok {s : State} {base : Addr} (hs : Scr s base) (xs : List Nat)
    (hx : ∀ i ∈ xs, i < 16)
    (h : pair (s.gpr .x4) (s.gpr .x5) + (xs.map (coeff s.mem base ACC)).sum < 2 ^ 128) :
    WP isa (.block (xs.flatMap addCoeff)) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) =
        pair (s.gpr .x4) (s.gpr .x5) + (xs.map (coeff s.mem base ACC)).sum ∧
      t.mem = s.mem ∧ Keeps colRegs s t := by
  induction xs generalizing s with
  | nil =>
    simp only [List.flatMap_nil, List.map_nil, List.sum_nil, Nat.add_zero]
    exact WP.block_nil ⟨rfl, rfl, Keeps.refl _ _⟩
  | cons i xs ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    have hi := hx i List.mem_cons_self
    have hc : pair (s.gpr .x4) (s.gpr .x5) + coeff s.mem base ACC i < 2 ^ 128 := by
      simp only [List.map_cons, List.sum_cons] at h
      omega_using [h]
    refine WP.mono (addCoeff_ok hs hi hc) fun u ⟨uv, um, uk⟩ => ?_
    refine WP.mono (ih (hs.of_keeps uk (by decide))
      (fun j hj => hx j (List.mem_cons_of_mem _ hj)) (by
        rw [uv, um]
        simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using h)) fun t ⟨tv, tm, tk⟩ => ?_
    refine ⟨?_, tm.trans um, uk.trans tk⟩
    rw [tv, uv, um]
    simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

end VG.Proof.X448.Wide

end

end

/-! Untrusted: fold wide product coefficients with 2⁴⁴⁸ = 2²²⁴ + 1. -/

@[expose] public section

namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st ACC TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem reduction_sum (f : Nat → Nat) (k : Nat) :
    f k + ((reduceIndices k).map f).sum = reduced f k := by
  by_cases hk : k < 4
  · simp only [reduceIndices, hk, ite_true, List.singleton_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, reduced, Nat.add_assoc]
  · simp only [reduceIndices, hk, ite_false, List.singleton_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, reduced,
      Nat.add_assoc]

theorem reduceCol_ok {s : State} {base : Addr} (hs : Scr s base) {k : Nat} (hk : k < 8)
    (hb : ∀ i < 16, coeff s.mem base ACC i < 2 ^ 116) :
    WP isa (.block (reduceCol k)) s fun t =>
      coeff t.mem base TMP k = reduced (coeff s.mem base ACC) k ∧
      Outside base (TMP + 16 * k) 16 s.mem t.mem ∧ Keeps colRegs s t := by
  rw [reduceCol, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadAt_ok hs (o := ACC) (k := k) (by simp only [ACC]; omega_using [hk]) (by decide))
    fun u ⟨uv, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  have ids : ∀ i ∈ reduceIndices k, i < 16 := by
    intro i hi
    by_cases h : k < 4 <;> simp only [reduceIndices, h, ite_true, ite_false,
      List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hi <;>
      rcases hi with rfl | rfl | rfl <;> omega_arith
  have cap : pair (u.gpr .x4) (u.gpr .x5) +
      ((reduceIndices k).map (coeff u.mem base ACC)).sum < 2 ^ 128 := by
    rw [uv, um, reduction_sum]
    exact Nat.lt_trans (reduced_bound hb k hk) (by decide)
  refine WP.mono (addCoeffs_ok (hs.of_keeps uk (by decide)) (reduceIndices k) ids cap)
    fun v ⟨vv, vm, vk⟩ => ?_
  have vs := (hs.of_keeps uk (by decide)).of_keeps vk (by decide)
  refine WP.mono (storeAt_ok vs (o := TMP) (k := k) (by simp only [TMP]; omega_using [hk]) (by decide))
    fun t ⟨tm, tk⟩ => ?_
  refine ⟨?_, ?_, (uk.mono (by decide)).trans (vk.trans (tk.mono (by decide)))⟩
  · rw [tm, coeff_put _ base _ _ (by simp only [TMP]; omega_using [hk])
      (by simp only [TMP]; omega_using [hk]), ite_eq_left rfl, vv, uv, um, reduction_sum]
  · rw [tm, vm, um]
    exact putCoeff_outside _ _ _ _ (by simp only [TMP]; omega_using [hk])

theorem reduce_ok {s : State} {base : Addr} (hs : Scr s base)
    (hb : ∀ i < 16, coeff s.mem base ACC i < 2 ^ 116) :
    WP isa (.block ((List.range 8).flatMap reduceCol)) s fun t =>
      (∀ k < 8, coeff t.mem base TMP k = reduced (coeff s.mem base ACC) k) ∧
      Outside base TMP 128 s.mem t.mem ∧ Keeps colRegs s t := by
  let f := coeff s.mem base ACC
  let inv := fun n (t : State) =>
    (∀ k < n, coeff t.mem base TMP k = reduced f k) ∧
    Outside base TMP 128 s.mem t.mem ∧ Keeps colRegs s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (reduceCol n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have av : ∀ i < 16, coeff t.mem base ACC i = f i := by
      intro i hi
      exact outside_coeff tm (by simp only [ACC, TMP]; omega_using [hi]) (by simp only [ACC]; omega_using [hi])
    have tb : ∀ i < 16, coeff t.mem base ACC i < 2 ^ 116 := by
      intro i hi
      rw [av i hi]
      exact hb i hi
    refine WP.mono (reduceCol_ok (hs.of_keeps tk (by decide)) hn tb) fun u ⟨uv, um, uk⟩ => ?_
    refine ⟨?_, tm.trans (um.mono (by omega_using []) (by omega_using [hn])), tk.trans uk⟩
    intro k hk
    by_cases h : k = n
    · subst k
      rw [uv]
      simp only [reduced]
      rw [av n (by omega_using [hn]), av (n + 8) (by omega_using [hn])]
      split
      · rename_i hn'
        rw [av (n + 12) (by omega_using [hn'])]
      · rw [av (n + 4) (by omega_using [hn])]
    · change pair (word u.mem base (TMP + 16 * k)) (word u.mem base (TMP + 16 * k + 8)) = _
      rw [outside_coeff um (by omega_using [h]) (by simp only [TMP]; omega_using [hn, hk])]
      exact tf k (by omega_using [hk, h])
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.Wide

end

end

/-! ### `Curve448.AArch64.Columns`, which this module and modules that import it used -/

section

/-! ### `Curve448.AArch64.Column`, which only this module used -/

section

/-! Untrusted: a diagonal of an eight-by-eight product, accumulated in registers. -/

@[expose] public section

namespace VG.Proof.Curve448.AArch64

open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

/-- Load one pair of operands without changing the coefficient registers. -/
theorem loadTerm_ok {s : State} {base : Addr} (hs : Scr s base) {a b i j : Nat}
    (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hi : i < 8) (hj : j < 8) :
    WP isa (.block [ld .x6 (a + 8 * i), ld .x9 (b + 8 * j)]) s fun t =>
      t.gpr .x6 = word s.mem base (a + 8 * i) ∧
      t.gpr .x9 = word s.mem base (b + 8 * j) ∧
      t.mem = s.mem ∧ Keeps [.x6, .x9] s t := by
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := ⟨by omega_arith, by omega_arith⟩
  have be : (b + 8 * j) % 8 = 0 ∧ b + 8 * j < 32768 := ⟨by omega_arith, by omega_arith⟩
  have al := hs.read (d := a + 8 * i) (n := 8) (by omega_arith)
  have bl := hs.read (d := b + 8 * j) (n := 8) (by omega_arith)
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, be, and_self, State.load, hs.x3, al, bl, ite_true, Option.map_some,
    Option.bind_some, BitVec.setWidth_eq, read8_eq, RegUpd.gpr_write,
    ite_false, reduceCtorEq, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- Initialize a register coefficient to zero. -/
theorem zero_ok (s : State) :
    WP isa (.block [.movz .x .x4 0 0, .movz .x .x5 0 0]) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) = 0 ∧ t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits from by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, ite_false,
    reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- Write the two coefficient words. -/
theorem store_ok {s : State} {base : Addr} (hs : Scr s base) {k : Nat} (hk : k < 16) :
    WP isa (.block [st .x4 (ACC + 16 * k), st .x5 (ACC + 16 * k + 8)]) s fun t =>
      t.mem = putCoeff s.mem base ACC k (s.gpr .x4) (s.gpr .x5) ∧ Keeps [] s t := by
  have ae : (ACC + 16 * k) % 8 = 0 ∧ ACC + 16 * k < 32768 := by simp only [ACC]; omega_arith
  have be : (ACC + 16 * k + 8) % 8 = 0 ∧ ACC + 16 * k + 8 < 32768 := by simp only [ACC]; omega_arith
  have aw := hs.write (d := ACC + 16 * k) (n := 8) (by simp only [ACC]; omega_arith)
  have bw := hs.write (d := ACC + 16 * k + 8) (n := 8) (by simp only [ACC]; omega_arith)
  apply WP.of_runBlock
  simp only [st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, be, and_self, State.read, State.store, hs.x3, aw, bw, ite_true,
    Option.bind_some, BitVec.setWidth_eq, write8_eq,
    Option.some.injEq, exists_eq_left']
  exact ⟨rfl, (fun _ _ => rfl), rfl, rfl⟩

def colRegs : List Reg := [.x4, .x5, .x6, .x9, .x10, .x11]

theorem columnBody_ok {s : State} {base : Addr} (hs : Scr s base) {a b k : Nat}
    (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (fa : ∀ i < 8, limbs s.mem base a i < weakBound)
    (fb : ∀ i < 8, limbs s.mem base b i < weakBound)
    (hz : pair (s.gpr .x4) (s.gpr .x5) = 0) :
    WP isa (.block ((List.range 8).flatMap (fun i => if i ≤ k ∧ k < i + 8 then
      [ld .x6 (a + 8 * i), ld .x9 (b + 8 * (k - i))] ++ term else []))) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) = rows (limbs s.mem base a) (limbs s.mem base b) 8 k ∧
      t.mem = s.mem ∧ Keeps colRegs s t := by
  let f := limbs s.mem base a
  let g := limbs s.mem base b
  let inv := fun n (t : State) =>
    pair (t.gpr .x4) (t.gpr .x5) = colSum f g k n ∧
    t.mem = s.mem ∧ Keeps colRegs s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block (if n ≤ k ∧ k < n + 8 then
        [ld .x6 (a + 8 * n), ld .x9 (b + 8 * (k - n))] ++ term else [])) t (inv (n + 1)) := by
    intro n t hn ⟨tv, tm, tk⟩
    by_cases h : n ≤ k ∧ k < n + 8
    · rw [ite_eq_left h, WP.block_append_iff]
      have ts := hs.of_keeps tk (by decide)
      refine WP.mono (loadTerm_ok ts ha hb ha8 hb8 hn (by omega_arith)) fun u ⟨u6, u9, um, uk⟩ => ?_
      have uv : pair (u.gpr .x4) (u.gpr .x5) = colSum f g k n := by
        rw [uk.1 .x4 (by decide), uk.1 .x5 (by decide), tv]
      have av : (u.gpr .x6).toNat = f n := by rw [u6, tm]
      have bv : (u.gpr .x9).toNat = g (k - n) := by rw [u9, tm]
      have prod : f n * g (k - n) ≤ (weakBound - 1) ^ 2 := by
        rw [Nat.pow_two]
        exact Nat.mul_le_mul (by have fh : f n < weakBound := fa n hn; omega_arith) (by have gh : g (k - n) < weakBound := fb (k - n) (by omega_arith); omega_arith)
      have cb := VG.Proof.Curve448.AArch64.rows_bound fa fb (n := n) (by omega_arith) k
      rw [← colSum_eq] at cb
      change colSum f g k n ≤ n * (weakBound - 1) ^ 2 at cb
      have sum : (u.gpr .x6).toNat * (u.gpr .x9).toNat + pair (u.gpr .x4) (u.gpr .x5) < 2 ^ 128 := by
        rw [av, bv, uv]
        have bd : (n + 1) * (weakBound - 1) ^ 2 ≤ 8 * (weakBound - 1) ^ 2 :=
          Nat.mul_le_mul_right _ (by omega_arith)
        have cap : 8 * (weakBound - 1) ^ 2 < 2 ^ 128 := by decide +kernel
        rw [Nat.add_mul, Nat.one_mul] at bd
        omega_arith
      refine WP.mono (term_ok u sum) fun v ⟨vv, vm, vk⟩ => ?_
      refine ⟨?_, vm.trans (um.trans tm), ?_⟩
      · rw [vv, av, bv, uv, colSum, ite_eq_left h]
        omega_arith
      · exact tk.trans ((uk.mono (by decide)).trans (vk.mono (by decide)))
    · rw [ite_eq_right h]
      apply WP.block_nil
      exact ⟨by rw [colSum, ite_eq_right h, Nat.add_zero]; exact tv, tm, tk⟩
  have init : inv 0 s := ⟨hz, rfl, Keeps.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s init)
    fun t ⟨tv, tm, tk⟩ => ?_
  exact ⟨tv.trans (colSum_eq f g k 8), tm, tk⟩

theorem column_ok {s : State} {base : Addr} (hs : Scr s base) {a b k : Nat}
    (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hk : k < 16)
    (fa : ∀ i < 8, limbs s.mem base a i < weakBound)
    (fb : ∀ i < 8, limbs s.mem base b i < weakBound) :
    WP isa (.block (column a b k)) s fun t =>
      coeff t.mem base ACC k = rows (limbs s.mem base a) (limbs s.mem base b) 8 k ∧
      Outside base (ACC + 16 * k) 16 s.mem t.mem ∧ Keeps colRegs s t := by
  rw [column, List.append_assoc, WP.block_append_iff]
  refine WP.mono (zero_ok s) fun u ⟨uz, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (columnBody_ok (hs.of_keeps uk (by decide)) ha hb ha8 hb8
    (by rw [um]; exact fa) (by rw [um]; exact fb) uz) fun v ⟨vv, vm, vk⟩ => ?_
  have vs := (hs.of_keeps uk (by decide)).of_keeps vk (by decide)
  refine WP.mono (store_ok vs hk) fun t ⟨tm, tk⟩ => ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [tm, coeff_put _ base _ _ (by simp only [ACC]; omega_arith)
      (by simp only [ACC]; omega_arith), ite_eq_left rfl, vv, um]
  · rw [tm, vm, um]
    exact putCoeff_outside _ _ _ _ (by simp only [ACC]; omega_arith)
  · exact (uk.mono (by decide)).trans (vk.trans (tk.mono (by decide)))

end VG.Proof.Curve448.AArch64

end

end


/-! Untrusted: the complete two-word coefficient array of a wide product. -/

@[expose] public section

namespace VG.Proof.Curve448.AArch64

open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ACC)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem columns_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat}
    (ha : a + 64 ≤ ACC ∨ ACC + 256 ≤ a) (hb : b + 64 ≤ ACC ∨ ACC + 256 ≤ b)
    (ha' : a + 64 ≤ 8192) (hb' : b + 64 ≤ 8192) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (fa : ∀ i < 8, limbs s.mem base a i < weakBound)
    (fb : ∀ i < 8, limbs s.mem base b i < weakBound) :
    WP isa (.block ((List.range 16).flatMap (column a b))) s fun t =>
      (∀ k < 16, coeff t.mem base ACC k = rows (limbs s.mem base a) (limbs s.mem base b) 8 k) ∧
      Outside base ACC 256 s.mem t.mem ∧ Keeps colRegs s t := by
  let f := limbs s.mem base a
  let g := limbs s.mem base b
  let inv := fun n (t : State) =>
    (∀ k < 16, coeff t.mem base ACC k = if k < n then rows f g 8 k else coeff s.mem base ACC k) ∧
    Outside base ACC 256 s.mem t.mem ∧ Keeps colRegs s t
  have step : ∀ n t, n < 16 → inv n t → WP isa (.block (column a b n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have av : ∀ i < 8, limbs t.mem base a i = f i := by
      intro i hi
      exact congrArg BitVec.toNat (tm.word (by omega_using [ha, hi]) (by omega_using [ha', hi]))
    have bv : ∀ i < 8, limbs t.mem base b i = g i := by
      intro i hi
      exact congrArg BitVec.toNat (tm.word (by omega_using [hb, hi]) (by omega_using [hb', hi]))
    refine WP.mono (column_ok (hs.of_keeps tk (by decide)) ha' hb' ha8 hb8 hn
      (by intro i hi; rw [av i hi]; exact fa i hi)
      (by intro i hi; rw [bv i hi]; exact fb i hi)) fun u ⟨uv, um, uk⟩ => ?_
    refine ⟨?_, tm.trans (um.mono (by omega_using []) (by omega_using [hn])), tk.trans uk⟩
    intro k hk
    by_cases h : k = n
    · subst k
      rw [ite_eq_left (by omega_using []), uv]
      exact rows_congr av bv (by decide) n
    · have hsep : ACC + 16 * k + 16 ≤ ACC + 16 * n ∨
          ACC + 16 * n + 16 ≤ ACC + 16 * k := by omega_using [h]
      change pair (word u.mem base (ACC + 16 * k)) (word u.mem base (ACC + 16 * k + 8)) = _
      rw [outside_coeff um hsep (by simp only [ACC]; omega_using [hk])]
      change coeff t.mem base ACC k = _
      rw [tf k hk]
      have e : (k < n) = (k < n + 1) := propext (by omega_using [h])
      simp only [e]
  have init : inv 0 s := ⟨by intro k _; rw [ite_eq_right (by omega_using [])], Outside.refl _ _ _ _, Keeps.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) s init)
    fun t ⟨tf, tm, tk⟩ => ?_
  exact ⟨fun k hk => (tf k hk).trans (ite_eq_left hk), tm, tk⟩

end VG.Proof.Curve448.AArch64

end

end

@[expose] public section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ACC TMP)
open VG.Proof.X448.AArch64

theorem product_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0)
    (hb : Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (Impl.Curve448.AArch64.product o a b) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a * F s.mem base b := by
  let f := limbs s.mem base a
  let g := limbs s.mem base b
  rw [Impl.Curve448.AArch64.product, List.append_assoc, WP.block_append_iff]
  refine WP.mono (columns_ok hs (Or.inl (by omega)) (Or.inl (by omega))
    (by have := ha; change a + 128 ≤ 3584 at this; omega_using [this])
    (by have := hb; change b + 128 ≤ 3584 at this; omega_using [this]) ha8 hb8 ab bb) fun s₁ ⟨c₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have raw : ∀ i < 16, coeff s₁.mem base ACC i < 2 ^ 116 := by
    intro i hi
    rw [c₁ i hi]
    exact Nat.lt_of_le_of_lt (VG.Proof.Curve448.AArch64.rows_bound ab bb (by decide) i) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.reduce_ok hs₁ raw) fun s₂ ⟨r₂, m₂, k₂⟩ => ?_
  have red := reduced_bound raw
  refine WP.mono (normalize_ok (hs₁.of_keeps k₂ (by decide)) ho ho8 r₂ red) fun t ⟨tf, tm, tk⟩ => ?_
  have val : fe t.mem base o % Spec.X448.P = (fe s.mem base a * fe s.mem base b) % Spec.X448.P := by
    rw [show fe t.mem base o = VG.Proof.X448.Wide.valN
        (folded (folded (reduced (coeff s₁.mem base ACC)))) 8 from
        VG.Proof.X448.Wide.valN_congr tf, twice_mod, reduced_mod,
      VG.Proof.X448.Wide.valN_congr c₁, rows_val f g (by decide)]
  refine ⟨⟨?_, ?_⟩, ?_, VG.Proof.X448.toFe_mul val⟩
  · exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans (tk.mono (by decide)))
  · exact (FieldMem.work m₁ (by decide) (by decide)).trans
      ((FieldMem.work m₂ (by decide) (by decide)).trans tm)
  · intro i hi; rw [tf i hi]; exact twice_weak red i hi
end VG.Proof.Curve448.AArch64

end

end

/-! ### `Curve448.AArch64.AddEval`, which this module and modules that import it used -/

section

/-! Untrusted: pointwise coefficient in registers, without an intermediate store. -/

@[expose] public section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.AArch64
open VG.Impl.Curve448.AArch64

theorem addEval_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (ha : Slot a) (ha8 : a % 8 = 0) (hb : Slot b) (hb8 : b % 8 = 0) (hi : i < 8)
    (ab : limbs s.mem base a i < weakBound) (bb : limbs s.mem base b i < weakBound) :
    WP isa (.block (Impl.Curve448.AArch64.addEval a b i)) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) = limbs s.mem base a i + limbs s.mem base b i ∧ t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega_using [hi, ha])
  have lb := hs.read (d := b + 8 * i) (n := 8) (by change b + 128 ≤ 3584 at hb; omega_using [hi, hb])
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega_using [ha8, hi, ha]
  have be : (b + 8 * i) % 8 = 0 ∧ b + 8 * i < 32768 := by
    change b + 128 ≤ 3584 at hb; omega_using [hb8, hi, hb]
  apply WP.of_runBlock
  simp only [Impl.Curve448.AArch64.addEval, ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    State.read, State.load, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, ae, be, and_self,
    hs.x3, la, lb, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · simp only [pair, show (BitVec.setWidth 64 (0 : BitVec 16)).toNat = 0 from rfl,
      Nat.mul_zero, Nat.add_zero, BitVec.toNat_add]
    change (limbs s.mem base a i + limbs s.mem base b i) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by simp only [weakBound, radix] at ab bb; omega_using [ab, bb])
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.Curve448.AArch64

end

end

/-! ### `Curve448.AArch64.Square`, which this module and modules that import it used -/

section

/-! ### `Curve448.AArch64.SymmetricColumns`, which this module and modules that import it used -/

section

/-! Untrusted: the complete two-word coefficient array of a wide product. -/

@[expose] public section

namespace VG.Proof.Curve448.AArch64

open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ACC)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem symmetricColumns_ok {s : State} {base : Addr} (hs : Scr s base) {f : Nat → Nat}
    (fc : ∀ i < 8, (s.gpr (Impl.X448.AArch64.Cached.cacheReg i)).toNat = f i)
    (fb : ∀ i < 8, f i < weakBound) :
    WP isa (.block ((List.range 16).flatMap (Impl.X448.AArch64.Symmetric.column))) s fun t =>
      (∀ k < 16, coeff t.mem base ACC k = rows f f 8 k) ∧
      Outside base ACC 256 s.mem t.mem ∧ Keeps termRegs s t := by
  let inv := fun n (t : State) =>
    (∀ k < 16, coeff t.mem base ACC k = if k < n then rows f f 8 k else coeff s.mem base ACC k) ∧
    Outside base ACC 256 s.mem t.mem ∧ Keeps termRegs s t
  have step : ∀ n t, n < 16 → inv n t → WP isa (.block (Impl.X448.AArch64.Symmetric.column n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (symmetricColumn_ok (hs.of_keeps tk (by decide)) hn (by
      intro i hi; rw [tk.1 _ (cacheReg_kept hi)]; exact fc i hi) fb) fun u ⟨uv, um, uk⟩ => ?_
    refine ⟨?_, tm.trans (um.mono (by omega_using []) (by omega_using [hn])), tk.trans uk⟩
    intro k hk
    by_cases h : k = n
    · subst k
      rw [ite_eq_left (by omega_using []), uv]

    · have hsep : ACC + 16 * k + 16 ≤ ACC + 16 * n ∨
          ACC + 16 * n + 16 ≤ ACC + 16 * k := by omega_using [h]
      change pair (word u.mem base (ACC + 16 * k)) (word u.mem base (ACC + 16 * k + 8)) = _
      rw [outside_coeff um hsep (by simp only [ACC]; omega_using [hk])]
      change coeff t.mem base ACC k = _
      rw [tf k hk]
      have e : (k < n) = (k < n + 1) := propext (by omega_using [h])
      simp only [e]
  have init : inv 0 s := ⟨by intro k _; rw [ite_eq_right (by omega_using [])], Outside.refl _ _ _ _, Keeps.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) s init)
    fun t ⟨tf, tm, tk⟩ => ?_
  exact ⟨fun k hk => (tf k hk).trans (ite_eq_left hk), tm, tk⟩

end VG.Proof.Curve448.AArch64

end

end

@[expose] public section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ACC TMP)
open VG.Impl.X448.AArch64.Cached VG.Proof.X448.AArch64

theorem square_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0)
    (ab : Bounded s.mem base a) :
    WP isa (Impl.Curve448.AArch64.sqr o a) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a * F s.mem base a := by
  let f := limbs s.mem base a
  rw [Impl.Curve448.AArch64.sqr, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadCached_ok hs (by have := ha; change a + 128 ≤ 3584 at this; omega_using [this]) ha8)
    fun s₁ ⟨c₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have fc : ∀ i < 8, (s₁.gpr (cacheReg i)).toNat = f i := by intro i hi; rw [c₁ i hi]
  rw [WP.block_append_iff]
  refine WP.mono (symmetricColumns_ok hs₁ fc ab) fun s₂ ⟨c₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have raw : ∀ i < 16, coeff s₂.mem base ACC i < 2 ^ 116 := by
    intro i hi; rw [c₂ i hi]
    exact Nat.lt_of_le_of_lt (VG.Proof.Curve448.AArch64.rows_bound ab ab (by decide) i) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.reduce_ok hs₂ raw) fun s₃ ⟨r₃, m₃, k₃⟩ => ?_
  have red := reduced_bound raw
  refine WP.mono (normalize_ok (hs₂.of_keeps k₃ (by decide)) ho ho8 r₃ red) fun t ⟨tf, tm, tk⟩ => ?_
  have val : fe t.mem base o % Spec.X448.P = (fe s.mem base a * fe s.mem base a) % Spec.X448.P := by
    rw [show fe t.mem base o = VG.Proof.X448.Wide.valN
        (folded (folded (reduced (coeff s₂.mem base ACC)))) 8 from
        VG.Proof.X448.Wide.valN_congr tf, twice_mod, reduced_mod,
      VG.Proof.X448.Wide.valN_congr c₂, rows_val f f (by decide)]
  refine ⟨⟨?_, ?_⟩, ?_, VG.Proof.X448.toFe_mul val⟩
  · exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans
      ((k₃.mono (by decide)).trans (tk.mono (by decide))))
  · rw [m₁] at m₂
    exact (FieldMem.work m₂ (by decide) (by decide)).trans
      ((FieldMem.work m₃ (by decide) (by decide)).trans tm)
  · intro i hi; rw [tf i hi]; exact twice_weak red i hi

theorem mul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0)
    (hb : Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (Impl.Curve448.AArch64.mul o a b) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a * F s.mem base b := by
  rw [Impl.Curve448.AArch64.mul]
  by_cases h : a = b
  · rw [ite_eq_left h, ← h]; exact square_ok hs ho ho8 ha ha8 ab
  · rw [ite_eq_right h]; exact product_ok hs ho ho8 ha ha8 hb hb8 ab bb
end VG.Proof.Curve448.AArch64

end

end

/-! ### `Curve448.AArch64.Pointwise`, which this module and modules that import it used -/

section

/-! ### `Curve448.AArch64.SmallEval`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.AArch64
open VG.Proof.Ed25519.AArch64 (mulHi read_x mul_lo_hi)

theorem smallEval_ok {s : State} {base : Addr} (hs : Scr s base) {a i : Nat}
    (ha : Slot a) (ha8 : a % 8 = 0) (hi : i < 8) :
    WP isa (.block (Impl.Curve448.AArch64.smallEval a i)) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) = 39081 * limbs s.mem base a i ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x6] s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega_using [hi, ha])
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega_using [ha8, hi, ha]
  apply WP.of_runBlock
  simp only [Impl.Curve448.AArch64.smallEval, ld, runBlock_cons, runStep_some, runBlock_nil, exec,
    addr, Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    State.read, State.load, RegUpd.gpr_write, RegUpd.mem_write,
    BitVec.setWidth_eq, ae, and_self, hs.x3, la, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · have h := mul_lo_hi (word s.mem base (a + 8 * i)) (BitVec.setWidth 64 (39081 : BitVec 16))
    rw [show (BitVec.setWidth 64 (39081 : BitVec 16)).toNat = 39081 by decide, Nat.mul_comm _ 39081] at h
    dsimp only [pair, mulHi, Size.bits] at h ⊢
    exact h
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
end VG.Proof.Curve448.AArch64

end

end

/-! ### `Curve448.AArch64.SubEval`, which this module and modules that import it used -/

section

/-! Untrusted: pointwise coefficient in registers, without an intermediate store. -/

@[expose] public section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.AArch64
open VG.Impl.Curve448.AArch64

theorem subEval_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (ha : Slot a) (ha8 : a % 8 = 0) (hb : Slot b) (hb8 : b % 8 = 0) (hi : i < 8)
    (ab : limbs s.mem base a i < weakBound) (bb : limbs s.mem base b i < weakBound) :
    WP isa (.block (Impl.Curve448.AArch64.subEval a b i)) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) = difference (limbs s.mem base a) (limbs s.mem base b) i ∧ t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega_using [hi, ha])
  have lb := hs.read (d := b + 8 * i) (n := 8) (by change b + 128 ≤ 3584 at hb; omega_using [hi, hb])
  have biasb := bias_ge i
  have biashi : bias i < 2 ^ 59 := by unfold bias; split <;> decide +kernel
  have biasword : (((((BitVec.setWidth 64 (if i = 4 then (0xfff8 : BitVec 16) else 0xfffc)) &&& ~~~((0xffff : BitVec 64) <<< 16)) ||| ((BitVec.setWidth 64 (0xffff : BitVec 16)) <<< 16)) &&& ~~~((0xffff : BitVec 64) <<< 32) ||| ((BitVec.setWidth 64 (0xffff : BitVec 16)) <<< 32)) &&& ~~~((0xffff : BitVec 64) <<< 48) ||| ((BitVec.setWidth 64 (0x03ff : BitVec 16)) <<< 48)).toNat = bias i := by
    by_cases h : i = 4 <;> simp only [h, ite_true, ite_false, bias] <;> decide +kernel
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega_using [ha8, hi, ha]
  have be : (b + 8 * i) % 8 = 0 ∧ b + 8 * i < 32768 := by
    change b + 128 ≤ 3584 at hb; omega_using [hb8, hi, hb]
  apply WP.of_runBlock
  simp only [Impl.Curve448.AArch64.subEval, ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    Size.bits, Nat.reduceLT, Nat.reduceMul, BitVec.shiftLeft_zero, State.read, State.load, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, ae, be, and_self,
    hs.x3, la, lb, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · simp only [pair, show (BitVec.setWidth 64 (0 : BitVec 16)).toNat = 0 from rfl,
      Nat.mul_zero, Nat.add_zero, BitVec.toNat_sub, BitVec.toNat_add, biasword]
    change (2 ^ 64 - limbs s.mem base b i +
      (limbs s.mem base a i + bias i) % 2 ^ 64) % 2 ^ 64 =
      limbs s.mem base a i + bias i - limbs s.mem base b i
    simp only [weakBound, radix] at ab bb biasb
    omega_using [ab, bb, biasb, biashi]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.Curve448.AArch64

end

end

@[expose] public section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Proof.X448.AArch64

theorem add_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0)
    (hb : Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block (Impl.Curve448.AArch64.add o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a + F s.mem base b := by
  let f := fun i => limbs s.mem base a i + limbs s.mem base b i
  have fb : Within (radix * 6) f := by
    intro i hi; have h1 := ab i hi; have h2 := bb i hi
    change limbs s.mem base a i + limbs s.mem base b i < _
    simp only [weakBound, radix] at h1 h2 ⊢; omega_arith
  refine WP.mono (stage_point hs ho ho8 fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_add ?_⟩
  · intro i hi t ts tm
    have ea := input_limb tm ha hi
    have eb := input_limb tm hb hi
    refine WP.mono (addEval_ok ts ha ha8 hb hb8 hi (by rw [ea]; exact ab i hi) (by rw [eb]; exact bb i hi))
      fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk.mono (by decide)⟩
    rw [ea, eb] at uv; exact uv
  · rw [tv, valN_add]

theorem sub_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0)
    (hb : Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block (Impl.Curve448.AArch64.sub o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a - F s.mem base b := by
  let f := difference (limbs s.mem base a) (limbs s.mem base b)
  have fb : Within (radix * 6) f := by
    intro i hi; have h := ab i hi
    change difference (limbs s.mem base a) (limbs s.mem base b) i < _
    simp only [difference, bias, weakBound, radix] at h ⊢
    split <;> omega_arith
  refine WP.mono (stage_point hs ho ho8 fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_sub ?_⟩
  · intro i hi t ts tm
    have ea := input_limb tm ha hi
    have eb := input_limb tm hb hi
    refine WP.mono (subEval_ok ts ha ha8 hb hb8 hi (by rw [ea]; exact ab i hi) (by rw [eb]; exact bb i hi))
      fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk.mono (by decide)⟩
    simp only [difference, ea, eb] at uv; exact uv
  · rw [Nat.add_mod, tv, ← Nat.add_mod, difference_val bb,
      Nat.mul_comm 4 Spec.X448.P, Nat.add_mul_mod_self_left]

theorem small_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0)
    (ab : Bounded s.mem base a) :
    WP isa (.block (Impl.Curve448.AArch64.small o a)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = Spec.X448.a24 * F s.mem base a := by
  let f := fun i => 39081 * limbs s.mem base a i
  have fb : Within (2 ^ 118) f := by
    intro i hi
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 39081 (Nat.le_of_lt (ab i hi))) (by decide)
  refine WP.mono (stage_normalize hs ho ho8 fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_a24 ?_⟩
  · intro i hi t ts tm
    refine WP.mono (smallEval_ok ts ha ha8 hi) fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk.mono (by decide)⟩
    rw [input_limb tm ha hi] at uv; exact uv
  · rw [tv, valN_scale]
end VG.Proof.Curve448.AArch64

end

end

/-!
# X448 on AArch64: the working space as field-element slots

Untrusted: everything here is checked by Lean. Field operations update one
of twenty-two slots, preserving bounded limbs in every slot. The frame
excludes saved registers, the swap bit and the scalar's decoded bits.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64.Weak

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Proof.Curve448.AArch64
open VG.Impl.X448.AArch64.Weak
abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X448.Fe :=
  VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN (limbs m base o) 8)
abbrev Bounded := VG.Proof.Curve448.AArch64.Bounded
theorem valN_congr {f g : Nat → Nat} {n : Nat} (h : ∀ i < n, f i = g i) :
    VG.Proof.X448.Wide.valN f n = VG.Proof.X448.Wide.valN g n := VG.Proof.X448.Wide.valN_congr h

abbrev Index := Fin 22
abbrev Env := Index → Spec.X448.Fe

def E (m : Mem) (base : Addr) (i : Index) : Spec.X448.Fe := F m base (slot i.val)
def BoundedEnv (m : Mem) (base : Addr) : Prop := ∀ i : Index, Bounded m base (slot i.val)

abbrev workRegs := VG.Proof.X448.AArch64.workRegs
abbrev Keep := VG.Proof.X448.AArch64.Keep

theorem slot_bound (i : Index) : Slot (slot i.val) := by
  simp only [Slot, slot, ACC]
  have := i.isLt
  omega_using []

theorem slot_aligned (i : Index) : slot i.val % 8 = 0 := by
  simp only [slot]; omega_using []

theorem slot_sep {i j : Index} (h : i ≠ j) : slot i.val + 128 ≤ slot j.val ∨ slot j.val + 128 ≤ slot i.val := by
  have hn : i.val ≠ j.val := fun he => h (Fin.ext he)
  simp only [slot]
  omega_using [hn]

theorem E_update {base : Addr} {m m' : Mem} {o : Index} (h : FieldMem base (slot o.val) m m') :
    E m' base = Function.update (E m base) o (F m' base (slot o.val)) := by
  funext i
  by_cases hi : i = o
  · subst i; simp only [Function.update_self, E]
  · rw [Function.update_of_ne hi]
    simp only [E, F]
    exact congrArg toFe (valN_congr (fun j hj =>
      h.limbs (slot_sep hi) (slot_bound i) (by omega_using [hj] : j < 16)))

theorem bounded_update {base : Addr} {m m' : Mem} {o : Index} (h : FieldMem base (slot o.val) m m')
    (hm : BoundedEnv m base) (ho : Bounded m' base (slot o.val)) : BoundedEnv m' base := by
  intro i
  by_cases hi : i = o
  · subst i; exact ho
  · intro j hj
    rw [h.limbs (slot_sep hi) (slot_bound i) (by omega_using [hj] : j < 16)]
    exact hm i j hj

def opMul (o a b : Index) (e : Env) : Env := Function.update e o (e a * e b)
def opAdd (o a b : Index) (e : Env) : Env := Function.update e o (e a + e b)
def opSub (o a b : Index) (e : Env) : Env := Function.update e o (e a - e b)
def opA24 (o a : Index) (e : Env) : Env := Function.update e o (Spec.X448.a24 * e a)
def opCopy (o a : Index) (e : Env) : Env := Function.update e o (e a)
def opSwap (x y : Index) (sw : Bool) (e : Env) : Env :=
  Function.update (Function.update e x (if sw then e y else e x)) y (if sw then e x else e y)

theorem mulE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a b : Index) :
    WP isa (Impl.Curve448.AArch64.mul (slot o.val) (slot a.val) (slot b.val)) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opMul o a b (E s.mem base) :=
  WP.mono (VG.Proof.Curve448.AArch64.mul_ok hs (slot_bound o) (slot_aligned o) (slot_bound a) (slot_aligned a) (slot_bound b) (slot_aligned b) (hb a) (hb b)) fun t ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by
      have e' : F t.mem base (slot o.val) = F s.mem base (slot a.val) * F s.mem base (slot b.val) := e
      rw [E_update h.mem, e']; rfl⟩

theorem addE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a b : Index) :
    WP isa (.block (Impl.Curve448.AArch64.add (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opAdd o a b (E s.mem base) :=
  WP.mono (VG.Proof.Curve448.AArch64.add_ok hs (slot_bound o) (slot_aligned o) (slot_bound a) (slot_aligned a) (slot_bound b) (slot_aligned b) (hb a) (hb b)) fun t ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by
      have e' : F t.mem base (slot o.val) = F s.mem base (slot a.val) + F s.mem base (slot b.val) := e
      rw [E_update h.mem, e']; rfl⟩

theorem subE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a b : Index) :
    WP isa (.block (Impl.Curve448.AArch64.sub (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opSub o a b (E s.mem base) :=
  WP.mono (VG.Proof.Curve448.AArch64.sub_ok hs (slot_bound o) (slot_aligned o) (slot_bound a) (slot_aligned a) (slot_bound b) (slot_aligned b) (hb a) (hb b)) fun t ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by
      have e' : F t.mem base (slot o.val) = F s.mem base (slot a.val) - F s.mem base (slot b.val) := e
      rw [E_update h.mem, e']; rfl⟩

theorem a24E {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a : Index) :
    WP isa (.block (Impl.Curve448.AArch64.small (slot o.val) (slot a.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opA24 o a (E s.mem base) :=
  WP.mono (VG.Proof.Curve448.AArch64.small_ok hs (slot_bound o) (slot_aligned o) (slot_bound a) (slot_aligned a) (hb a)) fun t ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by
      have e' : F t.mem base (slot o.val) = Spec.X448.a24 * F s.mem base (slot a.val) := e
      rw [E_update h.mem, e']; rfl⟩

theorem copyE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a : Index) :
    WP isa (.block (Impl.Curve448.AArch64.copy (slot o.val) (slot a.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opCopy o a (E s.mem base) := by
  have sep : slot o.val = slot a.val ∨ slot o.val + 128 ≤ slot a.val ∨ slot a.val + 128 ≤ slot o.val := by
    by_cases h : o = a
    · subst o; exact Or.inl rfl
    · exact Or.inr (slot_sep h)
  refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hs (Nat.le_trans (slot_bound o) (by decide))
    (Nat.le_trans (slot_bound a) (by decide)) (slot_aligned o) (slot_aligned a) sep) fun t ⟨tf, tm, tk⟩ => ?_
  have op : Op base (slot o.val) s t := ⟨tk, FieldMem.output tm⟩
  refine ⟨op.keep, bounded_update op.mem hb (fun i hi => ?_), ?_⟩
  · rw [tf i hi]; exact hb a i hi
  · rw [E_update op.mem, show F t.mem base (slot o.val) = F s.mem base (slot a.val) from
      congrArg toFe (valN_congr tf)]
    rfl

theorem cswapE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (x y : Index) (hxy : x ≠ y) {sw : Bool} (hm : s.gpr .x6 = mask sw) :
    WP isa (.block (Impl.Curve448.AArch64.cswap (slot x.val) (slot y.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ t.gpr .x6 = s.gpr .x6 ∧
      E t.mem base = opSwap x y sw (E s.mem base) := by
  refine WP.mono (VG.Proof.Curve448.AArch64.cswap_ok hs (slot_bound x) (slot_bound y) (slot_aligned x) (slot_aligned y) (slot_sep hxy) hm)
    fun t ⟨tx, ty, tm, tk⟩ => ?_
  have other : ∀ i : Index, i ≠ x → i ≠ y → ∀ j < 8,
      limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i hix hiy j hj
    have ex := slot_sep hix
    have ey := slot_sep hiy
    have hi := slot_bound i
    change (word t.mem base (slot i.val + 8 * j)).toNat = _
    rw [tm.word (by omega_using [hj, ex]) (by omega_using [hj, ey]) (by change slot i.val + 128 ≤ 3584 at hi; omega_using [hj, hi])]
  have fx : E t.mem base x = if sw then E s.mem base y else E s.mem base x := by
    cases sw <;> apply congrArg toFe <;> apply valN_congr <;> exact tx
  have fy : E t.mem base y = if sw then E s.mem base x else E s.mem base y := by
    cases sw <;> apply congrArg toFe <;> apply valN_congr <;> exact ty
  refine ⟨⟨tk.mono ?_, ?_⟩, ?_, tk.1 _ (by decide), ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro p hp _
    have hx := x.isLt
    have hy := y.isLt
    apply tm p <;> simp only [slot] <;> omega_using [hp]
  · intro i j hj
    by_cases hix : i = x
    · subst i; rw [tx j hj]; cases sw <;> exact hb _ j hj
    · by_cases hiy : i = y
      · subst i; rw [ty j hj]; cases sw <;> exact hb _ j hj
      · rw [other i hix hiy j hj]; exact hb i j hj
  · funext i
    by_cases hiy : i = y
    · subst i; rw [opSwap, Function.update_self]; exact fy
    · rw [opSwap, Function.update_of_ne hiy]
      by_cases hix : i = x
      · subst i; rw [Function.update_self]; exact fx
      · rw [Function.update_of_ne hix]
        exact congrArg toFe (valN_congr (other i hix hiy))

end VG.Proof.X448.AArch64.Weak
