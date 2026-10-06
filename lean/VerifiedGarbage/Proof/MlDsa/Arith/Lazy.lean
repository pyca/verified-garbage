import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt

/-! Unsigned doubleword coefficients used between lazy forward NTT layers. -/
namespace VG.Proof.MlDsa.Arith.Lazy
open VG.Spec.MlDsa (q n Zq zetas)
open VG.Proof.MlDsa.Arith (n_eq foldl_range'_succ foldl_range_succ)
abbrev Word := Fin 4294967296
abbrev Poly := Vector Word 256
theorem getElem!_eq (f : Poly) {i : Nat} (hi : i < n) : f[i]! = f[i] := getElem!_pos f i hi

theorem getElem!_set!_self (f : Poly) {i : Nat} (hi : i < n) (x : Word) : (f.set! i x)[i]! = x := by
  rw [getElem!_eq _ hi, Vector.getElem_set!, ite_eq_left rfl]

theorem getElem!_set!_ne (f : Poly) {i j : Nat} (hj : j < n) (h : i ≠ j) (x : Word) :
    (f.set! i x)[j]! = f[j]! := by
  rw [getElem!_eq _ hj, getElem!_eq _ hj, Vector.getElem_set!, ite_eq_right h]

theorem ext_getElem! {f g : Poly} (h : ∀ i < n, f[i]! = g[i]!) : f = g :=
  Vector.ext fun i hi => by rw [← getElem!_eq f hi, ← getElem!_eq g hi]; exact h i hi


def bfly (op : Word → Word → Zq → Word × Word) (w : Poly) (j len : Nat) (z : Zq) : Poly :=
  let r := op w[j]! w[j + len]! z
  (w.set! (j + len) r.2).set! j r.1

theorem bfly_get (op : Word → Word → Zq → Word × Word) (w : Poly) {j len : Nat} (_hlen : 0 < len) (hj : j + len < n) (z : Zq)
    {i : Nat} (hi : i < n) :
    (bfly op w j len z)[i]! =
      if i = j then (op w[j]! w[j + len]! z).1
      else if i = j + len then (op w[j]! w[j + len]! z).2
      else w[i]! := by
  simp only [bfly]
  by_cases h1 : i = j
  · subst h1
    rw [getElem!_set!_self _ hi, ite_eq_left rfl]
  · rw [getElem!_set!_ne _ hi (Ne.symm h1), ite_eq_right h1]
    by_cases h2 : i = j + len
    · subst h2; rw [getElem!_set!_self _ hi, ite_eq_left rfl]
    · rw [getElem!_set!_ne _ hi (Ne.symm h2), ite_eq_right h2]

def blockN (op : Poly → Nat → Nat → Zq → Poly) (w : Poly) (len : Nat) (z : Zq) (start t : Nat) : Poly :=
  (List.range' start t).foldl (fun w j => op w j len z) w

theorem blockN_zero (op : Poly → Nat → Nat → Zq → Poly) (w : Poly) (len : Nat) (z : Zq) (start : Nat) :
    blockN op w len z start 0 = w := rfl

theorem blockN_succ (op : Poly → Nat → Nat → Zq → Poly) (w : Poly) (len : Nat) (z : Zq) (start t : Nat) :
    blockN op w len z start (t + 1) = op (blockN op w len z start t) (start + t) len z :=
  foldl_range'_succ _ _ _ _

structure BlkOk (blk : Poly → Nat → Nat → Nat → Nat → Poly) (op : Word → Word → Zq → Word × Word) : Prop where
  zero : ∀ f len k st, blk f len k st 0 = f
  add : ∀ f len k st t t', blk f len k st (t + t') = blk (blk f len k st t) len k (st + t) t'
  get : ∀ f len k st t, 0 < len → t ≤ len → st + len + t ≤ n → ∀ i < n,
    (blk f len k st t)[i]! = if st ≤ i ∧ i < st + t then (op f[i]! f[i + len]! (zetas k)).1
      else if st + len ≤ i ∧ i < st + len + t then (op f[i - len]! f[i]! (zetas k)).2 else f[i]!

theorem blockN_add (op : Poly → Nat → Nat → Zq → Poly) (f : Poly) (len : Nat) (z : Zq) (st t t' : Nat) :
    blockN op f len z st (t + t') = blockN op (blockN op f len z st t) len z (st + t) t' := by
  simp only [blockN]; rw [← List.foldl_append, List.range'_append_1]

theorem blockN_bfly_get' (op : Word → Word → Zq → Word × Word) (w : Poly) {len : Nat} {z : Zq} {start t : Nat} (hlen : 0 < len) (ht : t ≤ len)
    (hs : start + len + t ≤ n) {i : Nat} (hi : i < n) :
    (blockN (bfly op) w len z start t)[i]! =
      if start ≤ i ∧ i < start + t then (op w[i]! w[i + len]! z).1
      else if start + len ≤ i ∧ i < start + len + t then (op w[i - len]! w[i]! z).2
      else w[i]! := by
  induction t generalizing i with
  | zero =>
    rw [blockN_zero, ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ t ih =>
    rw [blockN_succ, bfly_get op _ hlen (by omega) _ hi, ih (i := start + t) (by omega) (by omega) (by omega),
      ih (i := start + t + len) (by omega) (by omega) (by omega), ih (by omega) (by omega) hi]
    rcases (by omega : i < start ∨ (start ≤ i ∧ i < start + t) ∨ i = start + t ∨
        (start + t < i ∧ i < start + len) ∨ (start + len ≤ i ∧ i < start + t + len) ∨
        i = start + t + len ∨ start + t + len < i) with h | h | rfl | h | h | rfl | h <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_cancel, ↓reduceIte]

theorem block_ok (op : Word → Word → Zq → Word × Word) :
    BlkOk (fun f len k st t => blockN (bfly op) f len (zetas k) st t) op :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => blockN_add _ _ _ _ _ _ _,
    fun f _ _ _ _ hl ht hs _ hi => blockN_bfly_get' op f hl ht hs hi⟩

def layF (blk : Poly → Nat → Nat → Nat → Nat → Poly) (F : Poly) (len : Nat) (zi : Nat → Nat) (b : Nat) :
    Poly :=
  (List.range b).foldl (fun f c => blk f len (zi c) (2 * len * c) len) F

/-- Each coefficient after the first `b` blocks of the layer with `len = 1`. -/
theorem layF1_get {blk : Poly → Nat → Nat → Nat → Nat → Poly}
    {op : Word → Word → Zq → Word × Word} (hblk : BlkOk blk op) (F : Poly) (zi : Nat → Nat) {b : Nat} (hb : b ≤ 128) {j : Nat} (hj : j < 256) :
    (layF blk F 1 zi b)[j]! = if j < 2 * b then
      (if j % 2 = 0 then (op F[j]! F[j + 1]! (zetas (zi (j / 2)))).1
        else (op F[j - 1]! F[j]! (zetas (zi (j / 2)))).2) else F[j]! := by
  induction b generalizing j with
  | zero => rw [ite_eq_right (by omega)]; rfl
  | succ b ih =>
    rw [layF, foldl_range_succ, ← layF,
      hblk.get _ 1 _ _ 1 (by decide) (by decide) (by rw [n_eq]; omega) j (by rw [n_eq]; exact hj)]
    by_cases h1 : 2 * 1 * b ≤ j ∧ j < 2 * 1 * b + 1
    · rw [ite_eq_left h1, ih (by omega) hj, ih (by omega) (by omega), show j / 2 = b by omega]
      simp (disch := omega) only [ite_eq_left, ite_eq_right]
    · rw [ite_eq_right h1]
      by_cases h2 : 2 * 1 * b + 1 ≤ j ∧ j < 2 * 1 * b + 1 + 1
      · rw [ite_eq_left h2, ih (by omega) (by omega), ih (by omega) hj, show j / 2 = b by omega]
        simp (disch := omega) only [ite_eq_left, ite_eq_right]
      · rw [ite_eq_right h2, ih (by omega) hj]
        by_cases h3 : j < 2 * b <;> simp (disch := omega) only [ite_eq_left, ite_eq_right]


/-- Each coefficient after the first `b` blocks of a length-two layer. -/
theorem layF2_get {blk : Poly → Nat → Nat → Nat → Nat → Poly}
    {op : Word → Word → Zq → Word × Word} (hblk : BlkOk blk op) (F : Poly) (zi : Nat → Nat)
    {b : Nat} (hb : b ≤ 64) {j : Nat} (hj : j < 256) :
    (layF blk F 2 zi b)[j]! = if j < 4*b then
      (if j%4 < 2 then (op F[j]! F[j+2]! (zetas (zi (j/4)))).1
       else (op F[j-2]! F[j]! (zetas (zi (j/4)))).2) else F[j]! := by
  induction b generalizing j with
  | zero => rw [ite_eq_right (by omega)]; rfl
  | succ b ih =>
    rw [layF,foldl_range_succ,← layF,
      hblk.get _ 2 _ _ 2 (by decide) (by decide) (by rw [n_eq]; omega) j (by rw [n_eq]; exact hj)]
    by_cases h1 : 2*2*b ≤ j ∧ j < 2*2*b+2
    · rw [ite_eq_left h1,ih (by omega) hj,ih (by omega) (by omega),show j/4 = b by omega]
      simp (disch := omega) only [ite_eq_left,ite_eq_right]
    · rw [ite_eq_right h1]
      by_cases h2 : 2*2*b+2 ≤ j ∧ j < 2*2*b+2+2
      · rw [ite_eq_left h2,ih (by omega) (by omega),ih (by omega) hj,show j/4 = b by omega]
        simp (disch := omega) only [ite_eq_left,ite_eq_right]
      · rw [ite_eq_right h2,ih (by omega) hj]
        by_cases h3 : j < 4*b <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]


end VG.Proof.MlDsa.Arith.Lazy
