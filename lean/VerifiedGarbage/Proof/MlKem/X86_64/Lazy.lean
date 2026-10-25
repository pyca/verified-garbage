module
public import VerifiedGarbage.Proof.MlKem.X86_64.VLay

import VerifiedGarbage.Proof.MlKem.X86_64.YNtt

/-!
# ML-KEM on x86-64: the layers of the NTT and its inverse on lazily reduced words

The butterflies of the lazy layers do exactly what `fwdW` and `invW` do to
the words, and those words are only congruent to the coefficients modulo `q`,
within a bound (`Rep`). Each butterfly is a step of a block of words
(`wBlockN`, which `BlkOk`, as the specification's blocks do), and a layer of
blocks of these butterflies keeps the congruence with the specification's
layer, its bound growing by `q` for `NTT` (`fwdW_rep`) and doubling for
`NTT⁻¹` (`invW_rep`), coefficient by coefficient (`layF_rep`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG.Spec.MlKem
open W (montW caddW)

/-- 256 words. -/
abbrev WPoly := Vector (BitVec 16) n

/-- The word of the zeta `ζ`, `ζ · 2¹⁶ mod q`, as `TZ` holds it. -/
def zw (ζ : Zq) : BitVec 16 := BitVec.ofNat 16 (ζ.val * 65536 % 3329)

/-- The butterfly of the lazy layers of `NTT` on words. -/
def fwdW (a b : BitVec 16) (ζ : Zq) : BitVec 16 × BitVec 16 := (a + montW b (zw ζ), a - montW b (zw ζ))

/-- The butterfly of the lazy layers of `NTT⁻¹` on words. -/
def invW (a b : BitVec 16) (ζ : Zq) : BitVec 16 × BitVec 16 := (a + b, montW (b - a) (zw ζ))

/-- `2¹⁶ mod q`: `montW d rW ≡ d (mod q)`. -/
def rW : BitVec 16 := 2285

/-! ## Blocks of butterflies on any values -/

section
variable {α : Type} [Inhabited α]

theorem vget_set_self (f : Vector α n) {i : Nat} (hi : i < n) (x : α) : (f.set! i x)[i]! = x := by
  rw [getElem!_pos _ i hi, Vector.getElem_set!, ite_eq_left rfl]

theorem vget_set_ne (f : Vector α n) {i j : Nat} (hj : j < n) (h : i ≠ j) (x : α) :
    (f.set! i x)[j]! = f[j]! := by
  rw [getElem!_pos _ j hj, getElem!_pos _ j hj, Vector.getElem_set!, ite_eq_right h]

/-- The butterfly `op` on `f[j]` and `f[j + len]`. -/
def wbfly (op : α → α → Zq → α × α) (f : Vector α n) (j len : Nat) (z : Zq) : Vector α n :=
  let r := op f[j]! f[j + len]! z
  (f.set! (j + len) r.2).set! j r.1

/-- The first `t` butterflies `op` of the block from `start` of the layer with
`len`, whose zeta is `zeta k`. -/
def wBlockN (op : α → α → Zq → α × α) (f : Vector α n) (len k start t : Nat) : Vector α n :=
  (List.range' start t).foldl (fun f j => wbfly op f j len (zeta k)) f

theorem wbfly_get (op : α → α → Zq → α × α) (f : Vector α n) {j len : Nat} (_hlen : 0 < len)
    (hj : j + len < n) (z : Zq) {i : Nat} (hi : i < n) :
    (wbfly op f j len z)[i]! = if i = j then (op f[j]! f[j + len]! z).1
      else if i = j + len then (op f[j]! f[j + len]! z).2 else f[i]! := by
  simp only [wbfly]
  by_cases h1 : i = j
  · subst h1
    rw [vget_set_self _ hi, ite_eq_left rfl]
  · rw [vget_set_ne _ hi (Ne.symm h1), ite_eq_right h1]
    by_cases h2 : i = j + len
    · subst h2; rw [vget_set_self _ hi, ite_eq_left rfl]
    · rw [vget_set_ne _ hi (Ne.symm h2), ite_eq_right h2]

theorem wBlockN_get (op : α → α → Zq → α × α) (f : Vector α n) {len k start t : Nat} (hlen : 0 < len)
    (ht : t ≤ len) (hs : start + len + t ≤ n) {i : Nat} (hi : i < n) :
    (wBlockN op f len k start t)[i]! =
      if start ≤ i ∧ i < start + t then (op f[i]! f[i + len]! (zeta k)).1
      else if start + len ≤ i ∧ i < start + len + t then (op f[i - len]! f[i]! (zeta k)).2
      else f[i]! := by
  induction t generalizing i with
  | zero => rw [wBlockN, List.range'_zero, List.foldl_nil, ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
  | succ t ih =>
    rw [wBlockN, foldl_range'_succ, ← wBlockN, wbfly_get _ _ hlen (by omega_arith) _ hi,
      ih (by omega_arith) (by omega_arith) (i := start + t) (by omega_arith), ih (by omega_arith) (by omega_arith) (i := start + t + len) (by omega_arith),
      ih (by omega_arith) (by omega_arith) hi]
    rcases (by omega_arith : i < start ∨ (start ≤ i ∧ i < start + t) ∨ i = start + t ∨
        (start + t < i ∧ i < start + len) ∨ (start + len ≤ i ∧ i < start + t + len) ∨
        i = start + t + len ∨ start + t + len < i) with h | h | rfl | h | h | rfl | h <;>
      simp (disch := omega_arith) only [↓ite_eq_left, ↓ite_eq_right, Nat.add_sub_cancel]

theorem wBlk_ok (op : α → α → Zq → α × α) : BlkOk (wBlockN op) op where
  zero _ _ _ _ := rfl
  add f len k st t t' := by simp only [wBlockN]; rw [← List.foldl_append, List.range'_append_1]
  get f _ _ _ _ hl ht hs _ hi := wBlockN_get op f hl ht hs hi

end

/-! ## Words congruent to coefficients -/

/-- The word `w` is congruent to `v` modulo `q`, and less than `b · q` in
magnitude. -/
def Rep (b : Nat) (w : BitVec 16) (v : Zq) : Prop :=
  -((b : Int) * 3329) < w.toInt ∧ w.toInt < (b : Int) * 3329 ∧ (w.toInt - (v.val : Int)) % 3329 = 0

theorem Rep.mono {b b' : Nat} {w : BitVec 16} {v : Zq} (h : Rep b w v) (hb : b ≤ b') : Rep b' w v := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by have : (b : Int) ≤ b' := Int.ofNat_le.mpr hb; omega_arith, by have : (b : Int) ≤ b' := Int.ofNat_le.mpr hb; omega_arith, h3⟩

/-- A canonical word represents its value. -/
theorem Rep.of_can {w : BitVec 16} {v : Zq} (h : w.toNat = v.val) : Rep 1 w v := by
  have hv := val_lt v
  have hi := W.toInt_of_lt (a := w) (by rw [h]; exact hv)
  rw [h] at hi
  refine ⟨by rw [hi]; omega_arith, by rw [hi]; omega_arith, by rw [hi, Int.sub_self]; rfl⟩

theorem zw_toNat (ζ : Zq) : (zw ζ).toNat = ζ.val * 65536 % 3329 := by
  rw [zw, BitVec.toNat_ofNat]
  have : ζ.val * 65536 % 3329 < 3329 := Nat.mod_lt _ (by decide)
  omega_arith

theorem zw_toInt (ζ : Zq) : (zw ζ).toInt = (ζ.val : Int) * 65536 % 3329 := by
  rw [W.toInt_of_lt (by rw [zw_toNat]; exact Nat.mod_lt _ (by decide)), zw_toNat]
  omega_arith

/-- `montW d (zw ζ)` represents `ζ · y` for any word `d ≡ y (mod q)`. -/
theorem mont_rep {d : BitVec 16} {y : Zq} (ζ : Zq) (h : (d.toInt - (y.val : Int)) % 3329 = 0) :
    Rep 1 (montW d (zw ζ)) (ζ * y) := by
  have hz := zw_toInt ζ
  have hz1 : 0 ≤ (zw ζ).toInt := by rw [hz]; omega_arith
  have hz2 : (zw ζ).toInt < 3329 := by rw [hz]; omega_arith
  have hd := W.toInt16_bounds d
  have hn : (d.toInt * (zw ζ).toInt).natAbs ≤ 32768 * 3328 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul (by omega_arith) (by omega_arith)
  have h1 := Int.le_natAbs (a := d.toInt * (zw ζ).toInt)
  have h2 := Int.le_natAbs (a := -(d.toInt * (zw ζ).toInt))
  rw [Int.natAbs_neg] at h2
  obtain ⟨m1, m2, m3⟩ := W.montW_spec (d := d) (z := zw ζ) (by omega_arith) (by omega_arith)
  have hm := W.mul_zm (ζ := (ζ.val : Int)) h hz
  have hc := W.cancel_R m3 hm
  have e1 : ((ζ * y).val : Int) = ((y.val : Int) * ζ.val) % 3329 := by
    rw [val_mul, Nat.mul_comm, Int.natCast_emod, Int.natCast_mul]; rfl
  refine ⟨by omega_using [m1], by omega_using [m2], ?_⟩
  rw [e1]
  generalize (montW d (zw ζ)).toInt = M at hc ⊢
  generalize (y.val : Int) * (ζ.val : Int) = P at hc ⊢
  omega_using [hc]

/-- `montW d rW` represents `v` for any word `d ≡ v (mod q)`. -/
theorem red_rep {d : BitVec 16} {v : Zq} (h : (d.toInt - (v.val : Int)) % 3329 = 0) : Rep 1 (montW d rW) v := by
  have hc : rW.toInt = 2285 := by decide
  have hd := W.toInt16_bounds d
  have hn : (d.toInt * rW.toInt).natAbs ≤ 32768 * 2285 := by
    rw [Int.natAbs_mul, hc]; exact Nat.mul_le_mul (by omega_arith) (by decide)
  have h1 := Int.le_natAbs (a := d.toInt * rW.toInt)
  have h2 := Int.le_natAbs (a := -(d.toInt * rW.toInt))
  rw [Int.natAbs_neg] at h2
  obtain ⟨m1, m2, m3⟩ := W.montW_spec (d := d) (z := rW) (by omega_arith) (by omega_arith)
  rw [hc] at m3
  have e := W.cancel_R (Y := (v.val : Int)) m3 (by omega_using [h])
  refine ⟨by omega_using [m1], by omega_using [m2], ?_⟩
  omega_using [e]

/-- A word in `(-q, q)` congruent to `v`, made canonical by `caddW`. -/
theorem cadd_rep {d : BitVec 16} {v : Zq} (h : Rep 1 d v) : (caddW d).toNat = v.val := by
  obtain ⟨h1, h2, h3⟩ := h
  have c := W.caddW_spec (d := d) (by omega_using [h1]) (by omega_using [h2])
  have hv := val_lt v
  have n := W.toNat_of_toInt (a := caddW d) (by rw [c]; exact Int.emod_nonneg _ (by decide))
  rw [c] at n
  omega_using [n, h3, hv]

/-- The lazy butterfly of `NTT`: the bound grows by `q`. -/
theorem fwdW_rep {k : Nat} (hk : (k + 1) * 3329 ≤ 32768) {a b : BitVec 16} {x y : Zq} (ζ : Zq)
    (ha : Rep k a x) (hb : (b.toInt - (y.val : Int)) % 3329 = 0) :
    Rep (k + 1) (fwdW a b ζ).1 (x + ζ * y) ∧ Rep (k + 1) (fwdW a b ζ).2 (x - ζ * y) := by
  obtain ⟨t1, t2, t3⟩ := mont_rep ζ hb
  obtain ⟨a1, a2, a3⟩ := ha
  have hk' : (k : Int) * 3329 + 3329 ≤ 32768 := by omega_using [hk]
  simp only [fwdW, Rep]
  generalize montW b (zw ζ) = t at t1 t2 t3 ⊢
  have t1' : -3329 < t.toInt := by omega_using [t1]
  have t2' : t.toInt < 3329 := by omega_using [t2]
  have hx := val_lt x
  have hz := val_lt (ζ * y)
  have p := W.toInt_add16 (a := a) (b := t) (by omega_using [a1, t1', hk']) (by omega_using [a2, t2', hk'])
  have m := W.toInt_sub16 (a := a) (b := t) (by omega_using [a1, t2', hk']) (by omega_using [a2, t1', hk'])
  have v1 : ((x + ζ * y).val : Int) = ((x.val : Int) + ((ζ * y).val : Int)) % 3329 := by
    rw [val_add']; simp only [q]; omega_arith
  have v2 : ((x - ζ * y).val : Int) = ((x.val : Int) + (3329 - ((ζ * y).val : Int))) % 3329 := by
    rw [val_sub']; simp only [q]; omega_arith
  rw [p, m, v1, v2]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> omega_using [a1, a2, a3, t1', t2', t3, hk', hx, hz]

/-- The lazy butterfly of `NTT⁻¹`: the bound of the sum doubles. -/
theorem invW_rep {k : Nat} (hk : 2 * k * 3329 ≤ 32768) {a b : BitVec 16} {x y : Zq} (ζ : Zq)
    (ha : Rep k a x) (hb : Rep k b y) :
    Rep (2 * k) (invW a b ζ).1 (x + y) ∧ Rep 1 (invW a b ζ).2 (ζ * (y - x)) := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  have hk' : 2 * (k : Int) * 3329 ≤ 32768 := by omega_using [hk]
  have hx := val_lt x
  have hy := val_lt y
  have p := W.toInt_add16 (a := a) (b := b) (by omega_using [a1, b1, hk']) (by omega_using [a2, b2, hk'])
  have m := W.toInt_sub16 (a := b) (b := a) (by omega_using [a2, b1, hk']) (by omega_using [a1, b2, hk'])
  have v1 : ((x + y).val : Int) = ((x.val : Int) + (y.val : Int)) % 3329 := by
    rw [val_add']; simp only [q]; omega_arith
  have v2 : ((y - x).val : Int) = ((y.val : Int) + (3329 - (x.val : Int))) % 3329 := by
    rw [val_sub']; simp only [q]; omega_arith
  refine ⟨?_, mont_rep ζ ?_⟩
  · simp only [invW, Rep]
    rw [p, v1]
    refine ⟨?_, ?_, ?_⟩ <;> omega_using [a1, a2, a3, b1, b2, b3, hk', hx, hy]
  · rw [m, v2]
    omega_using [a3, b3, hx, hy]

/-! ## Polynomials of words -/

/-- Each word of `W` represents the coefficient of `F`, within `b · q`. -/
def PolyRep (b : Nat) (W : WPoly) (F : Poly) : Prop := ∀ i < 256, Rep b W[i]! F[i]!

theorem PolyRep.mono {b b' : Nat} {W : WPoly} {F : Poly} (h : PolyRep b W F) (hb : b ≤ b') : PolyRep b' W F :=
  fun i hi => (h i hi).mono hb

/-- A layer of butterflies `wop` on words, each representing the
specification's `sop`, represents the layer of the specification. -/
theorem layF_rep {wop : BitVec 16 → BitVec 16 → Zq → BitVec 16 × BitVec 16} {sop : Zq → Zq → Zq → Zq × Zq}
    {wblk : WPoly → Nat → Nat → Nat → Nat → WPoly} {sblk : Poly → Nat → Nat → Nat → Nat → Poly}
    (hw : BlkOk wblk wop) (hs : BlkOk sblk sop) {k k' : Nat}
    (hop : ∀ a b x y ζ, Rep k a x → Rep k b y → Rep k' (wop a b ζ).1 (sop x y ζ).1 ∧ Rep k' (wop a b ζ).2 (sop x y ζ).2)
    {len : Nat} (hlen : len ∈ [2, 4, 8, 16, 32, 64, 128]) (zi : Nat → Nat) {W : WPoly} {F : Poly}
    (h : PolyRep k W F) :
    PolyRep k' (layF wblk W len zi (128 / len)) (layF sblk F len zi (128 / len)) := by
  have hl : 0 < len ∧ 2 * len * (128 / len) = 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  intro j hj
  have hj' : j < 2 * len * (128 / len) := by rw [hl.2]; exact hj
  rw [layF_get hw W hl.1 zi (by rw [hl.2]) hj, layF_get hs F hl.1 zi (by rw [hl.2]) hj,
    ite_eq_left_of_eq_true _ _ (eq_true hj'), ite_eq_left_of_eq_true _ _ (eq_true hj')]
  have hb : ∀ j < 256, (j % (2 * len) < len → j + len < 256) ∧ (¬ j % (2 * len) < len → len ≤ j) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> intro j hj <;> omega_arith
  by_cases c : j % (2 * len) < len
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c), ite_eq_left_of_eq_true _ _ (eq_true c)]
    exact (hop _ _ _ _ _ (h j hj) (h _ ((hb j hj).1 c))).1
  · rw [ite_eq_right_of_eq_false _ _ (eq_false c), ite_eq_right_of_eq_false _ _ (eq_false c)]
    exact (hop _ _ _ _ _ (h _ (by omega_arith)) (h j hj)).2

end VG.Proof.MlKem.X86_64
