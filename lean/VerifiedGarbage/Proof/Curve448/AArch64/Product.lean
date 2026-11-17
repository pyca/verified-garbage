module

import VerifiedGarbage.Proof.Curve448.AArch64.Normalize
public import VerifiedGarbage.Impl.Curve448.AArch64
public import VerifiedGarbage.Proof.Curve448.AArch64.Memory
public import VerifiedGarbage.Proof.X448.AArch64.Mul
import VerifiedGarbage.Proof.X448.Wide.Reduce
import VerifiedGarbage.Proof.Curve448.AArch64.Bounds
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.X448.Wide.Memory
public import VerifiedGarbage.Impl.X448.AArch64.Wide
public import VerifiedGarbage.Proof.X448.Wide.Product
public import VerifiedGarbage.Proof.X448.Wide.Representation
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.Wide.Term
import VerifiedGarbage.Proof.Framework.AArch64.Exec

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
