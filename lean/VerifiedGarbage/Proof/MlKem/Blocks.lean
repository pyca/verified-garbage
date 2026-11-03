module

public import VerifiedGarbage.Proof.MlKem.Ntt
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-KEM: blocks and layers of butterflies on any values

What a block of butterflies `op` does, coefficient by coefficient (`BlkOk`),
for the specification's blocks (`nttBlk_ok`, `nttInvBlk_ok`) and for blocks
of butterflies on any values (`wBlockN`, `wBlk_ok`), as the lazy
implementations compute them on words; and what the first `b` blocks of a
layer leave, coefficient by coefficient (`layF`, `layF_get`), for every
target.
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-- The first `t` butterflies of a block of the specification do `op` to
`(j, j + len)`. -/
structure BlkOk {α : Type} [Inhabited α] (blk : Vector α n → Nat → Nat → Nat → Nat → Vector α n)
    (op : α → α → Zq → α × α) : Prop where
  zero : ∀ f len k st, blk f len k st 0 = f
  add : ∀ f len k st t t', blk f len k st (t + t') = blk (blk f len k st t) len k (st + t) t'
  get : ∀ f len k st t, 0 < len → t ≤ len → st + len + t ≤ n → ∀ i < n,
    (blk f len k st t)[i]! = if st ≤ i ∧ i < st + t then (op f[i]! f[i + len]! (zeta k)).1
      else if st + len ≤ i ∧ i < st + len + t then (op f[i - len]! f[i]! (zeta k)).2 else f[i]!

theorem nttBlk_ok : BlkOk nttBlockN (fun x y z => (x + z * y, x - z * y)) :=
  ⟨nttBlockN_zero, nttBlockN_add, fun f _ _ _ _ hl ht hs _ hi => nttBlockN_get' f hl ht hs hi⟩

theorem nttInvBlk_ok : BlkOk nttInvBlockN (fun x y z => (x + y, z * (y - x))) :=
  ⟨nttInvBlockN_zero, nttInvBlockN_add, fun f _ _ _ _ hl ht hs _ hi => nttInvBlockN_get' f hl ht hs hi⟩

/-- The first `b` blocks of the layer with `len`, block `c` with the zeta
`zeta (zi c)`. -/
def layF {α : Type} (blk : Vector α n → Nat → Nat → Nat → Nat → Vector α n) (F : Vector α n) (len : Nat)
    (zi : Nat → Nat) (b : Nat) : Vector α n :=
  (List.range b).foldl (fun f c => blk f len (zi c) (2 * len * c) len) F

section
variable {α : Type} [Inhabited α] {op : α → α → Zq → α × α} {blk : Vector α n → Nat → Nat → Nat → Nat → Vector α n}
  (hblk : BlkOk blk op)
include hblk

/-- Each coefficient after the first `b` blocks of the layer with `len`. -/
theorem layF_get (F : Vector α n) {len : Nat} (hl : 0 < len) (zi : Nat → Nat) {b : Nat} (hb : 2 * len * b ≤ 256)
    {j : Nat} (hj : j < 256) :
    (layF blk F len zi b)[j]! = if j < 2 * len * b then
      (if j % (2 * len) < len then (op F[j]! F[j + len]! (zeta (zi (j / (2 * len))))).1
        else (op F[j - len]! F[j]! (zeta (zi (j / (2 * len))))).2) else F[j]! := by
  induction b generalizing j with
  | zero => rw [ite_eq_right (by omega_arith)]; rfl
  | succ b ih =>
    have hb' : 2 * len * b + 2 * len ≤ 256 := by rw [Nat.mul_succ] at hb; exact hb
    rw [layF, foldl_range_succ, ← layF,
      hblk.get _ len _ _ len hl (Nat.le_refl _) (by rw [n_eq]; omega) j (by rw [n_eq]; exact hj)]
    have hd : ∀ i, 2 * len * b ≤ i → i < 2 * len * b + 2 * len → i / (2 * len) = b ∧
        i % (2 * len) = i - 2 * len * b := fun i h1 h2 => by
      have e1 : i / (2 * len) = b := by
        apply Nat.div_eq_of_lt_le
        · rw [Nat.mul_comm]; exact h1
        · rw [Nat.succ_mul, Nat.mul_comm b]; exact h2
      refine ⟨e1, ?_⟩
      have := Nat.div_add_mod i (2 * len)
      rw [e1] at this; omega
    by_cases h1 : 2 * len * b ≤ j ∧ j < 2 * len * b + len
    · obtain ⟨d1, d2⟩ := hd j h1.1 (by omega_arith)
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ih (by omega_arith) hj, ih (by omega_arith) (by omega_arith), d1,
        ite_eq_left_of_eq_true _ _ (eq_true (show j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega)),
        ite_eq_left_of_eq_true _ _ (eq_true (show j % (2 * len) < len by omega_arith)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j < 2 * len * b by omega_arith)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j + len < 2 * len * b by omega_arith))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      by_cases h2 : 2 * len * b + len ≤ j ∧ j < 2 * len * b + len + len
      · obtain ⟨d1, d2⟩ := hd j (by omega_arith) (by omega_arith)
        rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ih (by omega_arith) (by omega_arith), ih (by omega_arith) hj, d1,
          ite_eq_left_of_eq_true _ _ (eq_true (show j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j % (2 * len) < len by omega_arith)),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j - len < 2 * len * b by omega_arith)),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j < 2 * len * b by omega_arith))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ih (by omega_arith) hj]
        by_cases h3 : j < 2 * len * b
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h3),
            ite_eq_left_of_eq_true _ _ (eq_true (show j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega))]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h3),
            ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega))]

end

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

end VG.Proof.MlKem
