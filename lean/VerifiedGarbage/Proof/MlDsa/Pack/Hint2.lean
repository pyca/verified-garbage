import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Pack.Mem`. -/
section

/-!
# ML-DSA: polynomials in memory, for the encodings, on every target

The coefficients of the stored representations of `Spec/MlDsa/Poly.lean`
(`coeffAt`, `polyAt`, `natPolyAt`, `PolyIs`), as the encodings read and write
them: the words of a polynomial, their frame, and `PolyIs` from what each word
holds.
-/

namespace VG.Proof.MlDsa.Pack

open VG.Spec.MlDsa

/-- The address of coefficient `i` of the polynomial at `p`. -/
abbrev coeffAddr (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (4 * i)

theorem coeffAt_eq (m : Mem) (p : Addr) (i : Nat) : coeffAt m p i = m.readW (VG.Proof.MlDsa.Pack.coeffAddr p i) 32 := rfl

/-- The 1024 bytes of a polynomial at `p`. -/
abbrev polyRegion (p : Addr) : Region := ⟨p, 1024⟩

theorem coeff_contains (p : Addr) {i : Nat} (hi : i < 256) : (VG.Proof.MlDsa.Pack.polyRegion p).Contains (VG.Proof.MlDsa.Pack.coeffAddr p i) 4 :=
  Offset.contains_base p (by omega) (by omega)

theorem n_eq : n = 256 := rfl

theorem q_eq : q = 8380417 := rfl

/-- Coefficient `i` of `polyAt`: the stored word modulo `q`. -/
theorem polyAt_getElem (m : Mem) (p : Addr) {i : Nat} (hi : i < n) :
    (polyAt m p)[i] = Fin.ofNat q (coeffAt m p i).toNat := by
  simp only [polyAt, Vector.getElem_ofFn]

theorem natPolyAt_getElem (m : Mem) (p : Addr) {i : Nat} (hi : i < n) :
    (natPolyAt m p)[i] = (coeffAt m p i).toNat := by
  simp only [natPolyAt, Vector.getElem_ofFn]

/-- Coefficient `i` of a reduced polynomial is the stored word. -/
theorem polyAt_val {m : Mem} {p : Addr} (hr : Reduced m p) {i : Nat} (hi : i < n) :
    ((polyAt m p)[i]).val = (coeffAt m p i).toNat := by
  rw [VG.Proof.MlDsa.Pack.polyAt_getElem m p hi, Fin.val_ofNat, Nat.mod_eq_of_lt (hr i hi)]

/-- `f` is stored at `p` if each of its coefficients is. -/
theorem polyIs_of_toNat {m : Mem} {p : Addr} {f : Poly}
    (h : ∀ i (hi : i < n), (coeffAt m p i).toNat = (f[i]).val) : PolyIs m p f := by
  refine ⟨fun i hi => by rw [h i hi]; exact (f[i]).isLt, Vector.ext fun i hi => ?_⟩
  rw [VG.Proof.MlDsa.Pack.polyAt_getElem _ _ hi, h i hi]
  exact Fin.ext (Nat.mod_eq_of_lt (f[i]).isLt)

/-- The coefficients of a polynomial, as a list. -/
theorem toList_ofFn {α : Type} (g : Nat → α) :
    (Vector.ofFn (n := n) fun i => g i.val).toList = (List.range 256).map g := by
  refine List.ext_getElem (by rw [Vector.length_toList, List.length_map, List.length_range]) fun i h₁ h₂ => ?_
  simp only [Vector.getElem_toList, Vector.getElem_ofFn, List.getElem_map, List.getElem_range]

theorem natPolyAt_toList (m : Mem) (p : Addr) :
    (natPolyAt m p).toList = (List.range 256).map fun i => (coeffAt m p i).toNat := by
  unfold natPolyAt; exact VG.Proof.MlDsa.Pack.toList_ofFn fun i => (coeffAt m p i).toNat

/-- A word of a region disjoint from the frame's regions is unchanged. -/
theorem coeffAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (VG.Proof.MlDsa.Pack.polyRegion p).Disjoint r) {i : Nat} (hi : i < 256) : coeffAt m' p i = coeffAt m p i :=
  hf.readW (VG.Proof.MlDsa.Pack.coeff_contains p hi) hd (by decide)

end VG.Proof.MlDsa.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Pack.Coeffs`. -/
section

/-!
# ML-DSA: coefficients written in order, for every target

A loop that writes the coefficients of a polynomial of `[u32; 256]` one after
the other: after `t` of them, coefficient `i` is `G i` for `i < t` and what it
was before otherwise (`CoeffsUpTo`), until all 256 are written; and the bytes
of the words of a polynomial, from the words.
-/

namespace VG.Proof.MlDsa.Pack

open VG.Spec.MlDsa

theorem coeffAt_writeW_self (m : Mem) (p : Addr) (i : Nat) (v : BitVec 32) :
    coeffAt (m.writeW (VG.Proof.MlDsa.Pack.coeffAddr p i) v) p i = v :=
  Mem.readW_writeW_self32 m _ v

/-- Writing coefficient `j` of the polynomial at `p`. -/
theorem coeffAt_writeW (m : Mem) (p : Addr) {i j : Nat} (hi : i < 2 ^ 62) (hj : j < 2 ^ 62) (v : BitVec 32) :
    coeffAt (m.writeW (VG.Proof.MlDsa.Pack.coeffAddr p j) v) p i = if j = i then v else coeffAt m p i := by
  split
  · subst j; exact VG.Proof.MlDsa.Pack.coeffAt_writeW_self m p i v
  · exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

/-- The coefficients at `p`: the first `t` of them are `G`'s, the others `old`'s. -/
def CoeffsUpTo (m : Mem) (p : Addr) (t : Nat) (G old : Nat → BitVec 32) : Prop :=
  ∀ i < 256, coeffAt m p i = if i < t then G i else old i

theorem CoeffsUpTo.zero {m : Mem} {p : Addr} (G : Nat → BitVec 32) :
    VG.Proof.MlDsa.Pack.CoeffsUpTo m p 0 G fun i => coeffAt m p i := fun i _ => by
  rw [ite_eq_right (Nat.not_lt_zero i)]

/-- Writing coefficient `t`. -/
theorem CoeffsUpTo.write {m : Mem} {p : Addr} {t : Nat} {G old : Nat → BitVec 32}
    (h : VG.Proof.MlDsa.Pack.CoeffsUpTo m p t G old) (ht : t < 256) {v : BitVec 32} (hv : v = G t) :
    VG.Proof.MlDsa.Pack.CoeffsUpTo (m.writeW (VG.Proof.MlDsa.Pack.coeffAddr p t) v) p (t + 1) G old := fun i hi => by
  rw [VG.Proof.MlDsa.Pack.coeffAt_writeW m p (by omega) (by omega)]
  by_cases e : t = i
  · subst e; rw [ite_eq_left rfl, ite_eq_left (by omega), hv]
  · rw [ite_eq_right e, h i hi]
    by_cases hit : i < t
    · rw [ite_eq_left hit, ite_eq_left (by omega)]
    · rw [ite_eq_right hit, ite_eq_right (by omega)]

/-- All 256 coefficients written. -/
theorem CoeffsUpTo.all {m : Mem} {p : Addr} {G old : Nat → BitVec 32} (h : VG.Proof.MlDsa.Pack.CoeffsUpTo m p 256 G old)
    {i : Nat} (hi : i < 256) : coeffAt m p i = G i := by
  rw [h i hi, ite_eq_left hi]

/-- The bytes of words that agree. -/
theorem bytes_of_words {m₁ m₂ : Mem} {p : Addr} {N : Nat}
    (h : (List.range N).map (fun i => (coeffAt m₁ p i).toNat) = (List.range N).map (fun i => (coeffAt m₂ p i).toNat))
    {a : Addr} (ha : (⟨p, N * 4⟩ : Region).Contains a 1) : m₁ a = m₂ a := by
  simp only [Region.Contains] at ha
  have hw : ∀ i < N, coeffAt m₁ p i = coeffAt m₂ p i := fun i hi =>
    BitVec.eq_of_toNat_eq (List.map_inj_left.mp h i (List.mem_range.mpr hi))
  have hi : (a - p).toNat / 4 < N := by omega
  have ht : (a - p).toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  have ea : a = VG.Proof.MlDsa.Pack.coeffAddr p ((a - p).toNat / 4) + BitVec.ofNat 64 ((a - p).toNat % 4) := by
    rw [VG.Proof.MlDsa.Pack.coeffAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ea, Mem.readW_byte m₁ (VG.Proof.MlDsa.Pack.coeffAddr p _) ht, Mem.readW_byte m₂ (VG.Proof.MlDsa.Pack.coeffAddr p _) ht, ← VG.Proof.MlDsa.Pack.coeffAt_eq, ← VG.Proof.MlDsa.Pack.coeffAt_eq,
    hw _ hi]

end VG.Proof.MlDsa.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Pack.Hint`. -/
section

/-!
# ML-DSA: `HintBitPack` and `HintBitUnpack` step by step, for every target

The spec's `hintBitPack` and `hintBitUnpack` (Algorithms 20 and 21) are nested
`for` loops in `Id`, the second with early returns. Here they are restated as
folds of one step per coefficient (`hintBitPack_eq`, `hintBitUnpack_eq`; the
latter's `optFold` stops at the first failed check), which an implementation
follows iteration by iteration; and the index of `HintBitPack` is the number
of 1s before the current coefficient, at most the number of 1s of the hint
(`hpIdx_lt`), so it stays below `ω`.
-/

namespace VG.Proof.MlDsa.Pack

open VG.Spec.MlDsa

/-- A `for` loop of `Id` whose body always continues is a fold. -/
theorem forIn_id_yield {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (g : β → α → β) (hf : ∀ a b, f a b = pure (.yield (g b a))) : forIn l init f = pure (l.foldl g init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => rw [List.forIn_cons, hf, List.foldl_cons, ← ih]; rfl

/-! ## `HintBitPack` -/

/-- The default polynomial of `List.getD`. -/
abbrev noHint : Vector Bool n := Vector.replicate n false

/-- Coefficient `j` of the polynomial `hi`: if it is 1, `y[index] ← j` and the
index is incremented. -/
def hpStep (hi : Vector Bool n) (s : Array Byte × Nat) (j : Nat) : Array Byte × Nat :=
  if hi[j]! then (s.1.set! s.2 (BitVec.ofNat 8 j), s.2 + 1) else s

/-- Polynomial `i`: its coefficients, then `y[ω + i] ← index`. -/
def hpPoly (ω : Nat) (h : List (Vector Bool n)) (s : Array Byte × Nat) (i : Nat) : Array Byte × Nat :=
  let s' := (List.range n).foldl (VG.Proof.MlDsa.Pack.hpStep (h.getD i VG.Proof.MlDsa.Pack.noHint)) s
  (s'.1.set! (ω + i) (BitVec.ofNat 8 s'.2), s'.2)

theorem hintBitPack_eq (ω k : Nat) (h : List (Vector Bool n)) :
    hintBitPack ω k h = ((List.range k).foldl (VG.Proof.MlDsa.Pack.hpPoly ω h) (Array.replicate (ω + k) 0, 0)).1.toList := by
  dsimp only [hintBitPack]
  rw [VG.Proof.MlDsa.Pack.forIn_id_yield (List.range k) _ _ (VG.Proof.MlDsa.Pack.hpPoly ω h) (fun i s => ?_)]
  · rfl
  · rw [VG.Proof.MlDsa.Pack.forIn_id_yield (List.range n) _ _ (VG.Proof.MlDsa.Pack.hpStep (h.getD i VG.Proof.MlDsa.Pack.noHint)) (fun j s => ?_)]
    · rfl
    · simp only [VG.Proof.MlDsa.Pack.hpStep]; split <;> rfl

/-- The number of 1s among the first `j` coefficients of `hi`. -/
def count (hi : Vector Bool n) (j : Nat) : Nat := ((List.range j).filter fun t => hi[t]!).length

theorem count_succ (hi : Vector Bool n) (j : Nat) : VG.Proof.MlDsa.Pack.count hi (j + 1) = VG.Proof.MlDsa.Pack.count hi j + (if hi[j]! then 1 else 0) := by
  simp only [VG.Proof.MlDsa.Pack.count, List.range_succ, List.filter_append, List.length_append]
  split <;> simp_all

theorem count_mono (hi : Vector Bool n) {j j' : Nat} (h : j ≤ j') : VG.Proof.MlDsa.Pack.count hi j ≤ VG.Proof.MlDsa.Pack.count hi j' := by
  induction j' with
  | zero => rw [Nat.le_zero.mp h]
  | succ j' ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · rw [VG.Proof.MlDsa.Pack.count_succ]; have := ih (by omega); omega
    · exact Nat.le_refl _

theorem count_n (hi : Vector Bool n) : VG.Proof.MlDsa.Pack.count hi n = (hi.toList.filter id).length := by
  have e : hi.toList = (List.range n).map fun t => hi[t]! :=
    List.ext_getElem (by simp) fun t h₁ h₂ => by
      simp only [Vector.getElem_toList, List.getElem_map, List.getElem_range]
      rw [getElem!_pos hi t (by simpa using h₁)]
  rw [VG.Proof.MlDsa.Pack.count, e, List.filter_map, List.length_map]
  rfl

theorem hpStep_idx (hi : Vector Bool n) (s : Array Byte × Nat) (j : Nat) :
    (VG.Proof.MlDsa.Pack.hpStep hi s j).2 = s.2 + (if hi[j]! then 1 else 0) := by
  unfold VG.Proof.MlDsa.Pack.hpStep; split <;> simp_all

/-- The index after the first `j` coefficients. -/
theorem hpSteps_idx (hi : Vector Bool n) (s : Array Byte × Nat) (j : Nat) :
    ((List.range j).foldl (VG.Proof.MlDsa.Pack.hpStep hi) s).2 = s.2 + VG.Proof.MlDsa.Pack.count hi j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, VG.Proof.MlDsa.Pack.count_succ, VG.Proof.MlDsa.Pack.hpStep_idx, ih]
    omega

theorem sum_range_mono (f : Nat → Nat) {a b : Nat} (h : a ≤ b) :
    ((List.range a).map f).sum ≤ ((List.range b).map f).sum := by
  induction b with
  | zero => rw [Nat.le_zero.mp h]
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · rw [List.range_succ, List.map_append, List.sum_append]; have := ih (by omega); omega
    · exact Nat.le_refl _

theorem sum_range_succ (f : Nat → Nat) (a : Nat) :
    ((List.range (a + 1)).map f).sum = ((List.range a).map f).sum + f a := by
  rw [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero]

/-- The number of 1s before coefficient `j` of polynomial `i`. -/
def onesBefore (h : List (Vector Bool n)) (i j : Nat) : Nat :=
  ((List.range i).map fun t => VG.Proof.MlDsa.Pack.count (h.getD t VG.Proof.MlDsa.Pack.noHint) n).sum + VG.Proof.MlDsa.Pack.count (h.getD i VG.Proof.MlDsa.Pack.noHint) j

theorem hpPoly_idx (ω : Nat) (h : List (Vector Bool n)) (s : Array Byte × Nat) (i : Nat) :
    (VG.Proof.MlDsa.Pack.hpPoly ω h s i).2 = s.2 + VG.Proof.MlDsa.Pack.count (h.getD i VG.Proof.MlDsa.Pack.noHint) n := by
  dsimp only [VG.Proof.MlDsa.Pack.hpPoly]; exact VG.Proof.MlDsa.Pack.hpSteps_idx _ s n

theorem hpPolys_idx (ω : Nat) (h : List (Vector Bool n)) (s : Array Byte × Nat) (i : Nat) :
    ((List.range i).foldl (VG.Proof.MlDsa.Pack.hpPoly ω h) s).2 = s.2 + VG.Proof.MlDsa.Pack.onesBefore h i 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, VG.Proof.MlDsa.Pack.hpPoly_idx, ih]
    unfold VG.Proof.MlDsa.Pack.onesBefore
    rw [VG.Proof.MlDsa.Pack.sum_range_succ]
    have : VG.Proof.MlDsa.Pack.count (h.getD (i + 1) VG.Proof.MlDsa.Pack.noHint) 0 = 0 := rfl
    have : VG.Proof.MlDsa.Pack.count (h.getD i VG.Proof.MlDsa.Pack.noHint) 0 = 0 := rfl
    omega

theorem hintOnes_eq {h : List (Vector Bool n)} {k : Nat} (hk : h.length = k) :
    hintOnes h = ((List.range k).map fun t => VG.Proof.MlDsa.Pack.count (h.getD t VG.Proof.MlDsa.Pack.noHint) n).sum := by
  subst hk
  unfold hintOnes
  congr 1
  refine List.ext_getElem (by simp) fun t h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, VG.Proof.MlDsa.Pack.count_n]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h₂), Option.getD_some]

/-- The index before a 1 is less than the number of 1s. -/
theorem hpIdx_lt {h : List (Vector Bool n)} {k i j : Nat} (hk : h.length = k) (hi : i < k) (hj : j < n)
    (h1 : (h.getD i VG.Proof.MlDsa.Pack.noHint)[j]! = true) : VG.Proof.MlDsa.Pack.onesBefore h i j < hintOnes h := by
  rw [VG.Proof.MlDsa.Pack.hintOnes_eq hk]
  have hc : VG.Proof.MlDsa.Pack.count (h.getD i VG.Proof.MlDsa.Pack.noHint) j < VG.Proof.MlDsa.Pack.count (h.getD i VG.Proof.MlDsa.Pack.noHint) n := by
    have := VG.Proof.MlDsa.Pack.count_mono (h.getD i VG.Proof.MlDsa.Pack.noHint) (show j + 1 ≤ n by omega)
    rw [VG.Proof.MlDsa.Pack.count_succ, h1] at this; simp only [ite_true] at this; omega
  have hs := VG.Proof.MlDsa.Pack.sum_range_mono (fun t => VG.Proof.MlDsa.Pack.count (h.getD t VG.Proof.MlDsa.Pack.noHint) n) (show i + 1 ≤ k by omega)
  rw [VG.Proof.MlDsa.Pack.sum_range_succ] at hs
  unfold VG.Proof.MlDsa.Pack.onesBefore
  omega

/-- The index after polynomial `i` is at most the number of 1s. -/
theorem onesBefore_n_le {h : List (Vector Bool n)} {k i : Nat} (hk : h.length = k) (hi : i < k) :
    VG.Proof.MlDsa.Pack.onesBefore h i n ≤ hintOnes h := by
  rw [VG.Proof.MlDsa.Pack.hintOnes_eq hk]
  unfold VG.Proof.MlDsa.Pack.onesBefore
  rw [← VG.Proof.MlDsa.Pack.sum_range_succ (fun t => VG.Proof.MlDsa.Pack.count (h.getD t VG.Proof.MlDsa.Pack.noHint) n)]
  exact VG.Proof.MlDsa.Pack.sum_range_mono _ (by omega)

/-! ## `HintBitUnpack` -/

theorem ite_pos' {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem ite_neg' {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

/-- A fold that stops at the first failure. -/
def optFold {α S : Type} (g : S → α → Option S) : List α → S → Option S
  | [], st => some st
  | a :: l, st => (g st a).bind (VG.Proof.MlDsa.Pack.optFold g l)

theorem forIn_opt {α S R : Type} (g : S → α → Option S) (r₀ : R)
    (f : α → Option R × S → Id (ForInStep (Option R × S)))
    (hf : ∀ a st, (g st a = none → ∃ st', f a (none, st) = pure (.done (some r₀, st'))) ∧
      (∀ st', g st a = some st' → f a (none, st) = pure (.yield (none, st')))) :
    ∀ (l : List α) (st : S), (VG.Proof.MlDsa.Pack.optFold g l st = none ∧ ∃ st', forIn l (none, st) f = pure (some r₀, st')) ∨
      (∃ st', VG.Proof.MlDsa.Pack.optFold g l st = some st' ∧ forIn l (none, st) f = pure (none, st'))
  | [], st => .inr ⟨st, rfl, rfl⟩
  | a :: l, st => by
    rw [List.forIn_cons]
    cases hg : g st a with
    | none =>
      obtain ⟨st', h⟩ := (hf a st).1 hg
      exact .inl ⟨by simp [VG.Proof.MlDsa.Pack.optFold, hg], st', by rw [h]; rfl⟩
    | some st₁ =>
      rw [(hf a st).2 st₁ hg]
      rcases VG.Proof.MlDsa.Pack.forIn_opt g r₀ f hf l st₁ with ⟨h1, st', h2⟩ | ⟨st', h1, h2⟩
      · exact .inl ⟨by simp [VG.Proof.MlDsa.Pack.optFold, hg, h1], st', by rw [← h2]; rfl⟩
      · exact .inr ⟨st', by simp [VG.Proof.MlDsa.Pack.optFold, hg, h1], by rw [← h2]; rfl⟩

/-- A `for` loop of `Id` that stops at the first failure, followed by `G`. -/
theorem forIn_opt_bind {α S R β : Type} (g : S → α → Option S) (r₀ : R)
    (f : α → Option R × S → Id (ForInStep (Option R × S)))
    (hf : ∀ a st, (g st a = none → ∃ st', f a (none, st) = pure (.done (some r₀, st'))) ∧
      (∀ st', g st a = some st' → f a (none, st) = pure (.yield (none, st'))))
    (l : List α) (st : S) (G : Option R × S → Id β) (rhs : β)
    (hn : VG.Proof.MlDsa.Pack.optFold g l st = none → ∀ st', G (some r₀, st') = rhs)
    (hs : ∀ st', VG.Proof.MlDsa.Pack.optFold g l st = some st' → G (none, st') = rhs) :
    (forIn l (none, st) f >>= G) = rhs := by
  rcases VG.Proof.MlDsa.Pack.forIn_opt g r₀ f hf l st with ⟨h1, st', h2⟩ | ⟨st', h1, h2⟩
  · rw [h2]; exact hn h1 st'
  · rw [h2]; exact hs st' h1

/-- A `for` loop of `Id` that stops at the first failure, as the body of an
enclosing one. -/
theorem forIn_opt_step {α S R R' : Type} (g : S → α → Option S) (r₀ : R) (r₀' : R')
    (f : α → Option R × S → Id (ForInStep (Option R × S)))
    (hf : ∀ a st, (g st a = none → ∃ st', f a (none, st) = pure (.done (some r₀, st'))) ∧
      (∀ st', g st a = some st' → f a (none, st) = pure (.yield (none, st'))))
    (l : List α) (st : S) (G : Option R × S → Id (ForInStep (Option R' × S)))
    (hG₁ : ∀ st', G (some r₀, st') = pure (.done (some r₀', st'))) (hG₂ : ∀ st', G (none, st') = pure (.yield (none, st'))) :
    (VG.Proof.MlDsa.Pack.optFold g l st = none → ∃ st', (forIn l (none, st) f >>= G) = pure (.done (some r₀', st'))) ∧
      (∀ st', VG.Proof.MlDsa.Pack.optFold g l st = some st' → (forIn l (none, st) f >>= G) = pure (.yield (none, st'))) := by
  rcases VG.Proof.MlDsa.Pack.forIn_opt g r₀ f hf l st with ⟨h1, st', h2⟩ | ⟨st', h1, h2⟩
  · refine ⟨fun _ => ⟨st', ?_⟩, fun _ h => ?_⟩
    · rw [h2]; exact hG₁ st'
    · rw [h1] at h; cases h
  · refine ⟨fun h => ?_, fun st'' h => ?_⟩
    · rw [h1] at h; cases h
    · rw [h1] at h; cases h; rw [h2]; exact hG₂ st'

/-- Set coefficient `b` of polynomial `i`. -/
def huSet (i b : Nat) (h : Array (Vector Bool n)) : Array (Vector Bool n) :=
  h.set! i ((h.getD i VG.Proof.MlDsa.Pack.noHint).set! b true)

/-- The index of polynomial `i` from `first`: its coefficient `y[index]`, after
checking it is greater than the previous one. -/
def huStep (y : Array Byte) (i first : Nat) (st : Array (Vector Bool n) × Nat) (_ : Nat) :
    Option (Array (Vector Bool n) × Nat) :=
  if st.2 > first ∧ (y.getD (st.2 - 1) 0).toNat ≥ (y.getD st.2 0).toNat then none
  else some (VG.Proof.MlDsa.Pack.huSet i (y.getD st.2 0).toNat st.1, st.2 + 1)

/-- Polynomial `i`: the bound `y[ω + i]`, checked, and its coefficients. -/
def huPoly (ω : Nat) (y : Array Byte) (st : Array (Vector Bool n) × Nat) (i : Nat) :
    Option (Array (Vector Bool n) × Nat) :=
  let bound := (y.getD (ω + i) 0).toNat
  if bound < st.2 ∨ bound > ω then none else VG.Proof.MlDsa.Pack.optFold (VG.Proof.MlDsa.Pack.huStep y i st.2) (List.range (bound - st.2)) st

/-- The bytes after the last index are zero. -/
def huTrail (y : Array Byte) (_ : Unit) (i : Nat) : Option Unit := if y.getD i 0 ≠ 0 then none else some ()

theorem hintBitUnpack_eq (ω k : Nat) (y : List Byte) :
    hintBitUnpack ω k y =
      match VG.Proof.MlDsa.Pack.optFold (VG.Proof.MlDsa.Pack.huPoly ω y.toArray) (List.range k) (Array.replicate k VG.Proof.MlDsa.Pack.noHint, 0) with
      | none => none
      | some (h, idx) => (VG.Proof.MlDsa.Pack.optFold (VG.Proof.MlDsa.Pack.huTrail y.toArray) (List.range' idx (ω - idx)) ()).map fun _ => h.toList := by
  dsimp only [hintBitUnpack]
  refine VG.Proof.MlDsa.Pack.forIn_opt_bind (VG.Proof.MlDsa.Pack.huPoly ω y.toArray) (none : Option (List (Vector Bool n))) _ (fun i st => ?_) _ _ _ _
    (fun h1 st' => by rw [h1]; rfl) (fun st' h1 => ?_)
  · -- A polynomial.
    obtain ⟨hh, idx⟩ := st
    dsimp only
    by_cases hc : (y.toArray.getD (ω + i) 0).toNat < idx ∨ (y.toArray.getD (ω + i) 0).toNat > ω
    · simp only [VG.Proof.MlDsa.Pack.huPoly, hc, ↓reduceIte]
      exact ⟨fun _ => ⟨_, rfl⟩, fun _ h => (by cases h)⟩
    · simp only [VG.Proof.MlDsa.Pack.huPoly, hc, ↓reduceIte]
      refine VG.Proof.MlDsa.Pack.forIn_opt_step (VG.Proof.MlDsa.Pack.huStep y.toArray i idx) (none : Option (List (Vector Bool n))) none _
        (fun x st => ?_) _ _ _ (fun _ => rfl) (fun _ => rfl)
      obtain ⟨h2, idx2⟩ := st
      dsimp only
      simp only [VG.Proof.MlDsa.Pack.huStep, VG.Proof.MlDsa.Pack.huSet, VG.Proof.MlDsa.Pack.noHint]
      by_cases e1 : idx2 > idx
      · by_cases e2 : (y.toArray.getD (idx2 - 1) 0).toNat ≥ (y.toArray.getD idx2 0).toNat
        · simp only [e1, e2, and_self, ↓reduceIte]
          exact ⟨fun _ => ⟨_, rfl⟩, fun _ h => (by cases h)⟩
        · simp only [e1, e2, and_false, ↓reduceIte]
          exact ⟨fun h => (by cases h), fun st' h => (by cases h; rfl)⟩
      · simp only [e1, false_and, ↓reduceIte]
        exact ⟨fun h => (by cases h), fun st' h => (by cases h; rfl)⟩
  · -- The trailing bytes.
    obtain ⟨hh, idx⟩ := st'
    rw [h1]
    dsimp only
    refine VG.Proof.MlDsa.Pack.forIn_opt_bind (VG.Proof.MlDsa.Pack.huTrail y.toArray) (none : Option (List (Vector Bool n))) _ (fun i st => ?_) _ _ _ _
      (fun h2 _ => by rw [h2]; rfl) (fun st' h2 => by rw [h2]; rfl)
    rw [show VG.Proof.MlDsa.Pack.huTrail y.toArray st i = if y.toArray.getD i 0 ≠ 0 then none else some () from rfl]
    by_cases hy : y.toArray.getD i 0 ≠ 0
    · rw [VG.Proof.MlDsa.Pack.ite_pos' hy, VG.Proof.MlDsa.Pack.ite_pos' hy]
      exact ⟨fun _ => ⟨(), rfl⟩, fun _ h => (by cases h)⟩
    · rw [VG.Proof.MlDsa.Pack.ite_neg' hy, VG.Proof.MlDsa.Pack.ite_neg' hy]
      exact ⟨fun h => (by cases h), fun st' h => (by cases h; rfl)⟩

theorem optFold_append {α S : Type} (g : S → α → Option S) (l₁ l₂ : List α) (st : S) :
    VG.Proof.MlDsa.Pack.optFold g (l₁ ++ l₂) st = (VG.Proof.MlDsa.Pack.optFold g l₁ st).bind (VG.Proof.MlDsa.Pack.optFold g l₂) := by
  induction l₁ generalizing st with
  | nil => rfl
  | cons a l ih =>
    simp only [List.cons_append, VG.Proof.MlDsa.Pack.optFold]
    cases g st a with
    | none => rfl
    | some st' => exact ih st'

theorem optFold_range_succ {S : Type} (g : S → Nat → Option S) (m : Nat) (st : S) :
    VG.Proof.MlDsa.Pack.optFold g (List.range (m + 1)) st = (VG.Proof.MlDsa.Pack.optFold g (List.range m) st).bind fun st' => g st' m := by
  rw [List.range_succ, VG.Proof.MlDsa.Pack.optFold_append]
  cases VG.Proof.MlDsa.Pack.optFold g (List.range m) st with
  | none => rfl
  | some st' => simp only [Option.bind_some, VG.Proof.MlDsa.Pack.optFold]; cases g st' m <;> rfl

theorem optFold_range'_succ {S : Type} (g : S → Nat → Option S) (a m : Nat) (st : S) :
    VG.Proof.MlDsa.Pack.optFold g (List.range' a (m + 1)) st = (VG.Proof.MlDsa.Pack.optFold g (List.range' a m) st).bind fun st' => g st' (a + m) := by
  rw [List.range'_concat, VG.Proof.MlDsa.Pack.optFold_append]
  cases VG.Proof.MlDsa.Pack.optFold g (List.range' a m) st with
  | none => rfl
  | some st' => simp only [Option.bind_some, VG.Proof.MlDsa.Pack.optFold, Nat.one_mul]; cases g st' (a + m) <;> rfl

/-- Once a fold fails, it stays failed. -/
theorem optFold_range_none {S : Type} (g : S → Nat → Option S) {t m : Nat} (h : t ≤ m) {st : S}
    (hn : VG.Proof.MlDsa.Pack.optFold g (List.range t) st = none) : VG.Proof.MlDsa.Pack.optFold g (List.range m) st = none := by
  induction m with
  | zero => rw [Nat.le_zero.mp h] at hn; exact hn
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · rw [VG.Proof.MlDsa.Pack.optFold_range_succ, ih (by omega)]; rfl
    · exact hn

theorem optFold_range'_none {S : Type} (g : S → Nat → Option S) (a : Nat) {t m : Nat} (h : t ≤ m) {st : S}
    (hn : VG.Proof.MlDsa.Pack.optFold g (List.range' a t) st = none) : VG.Proof.MlDsa.Pack.optFold g (List.range' a m) st = none := by
  induction m with
  | zero => rw [Nat.le_zero.mp h] at hn; exact hn
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · rw [VG.Proof.MlDsa.Pack.optFold_range'_succ, ih (by omega)]; rfl
    · exact hn

theorem huSet_size (i b : Nat) (h : Array (Vector Bool n)) : (VG.Proof.MlDsa.Pack.huSet i b h).size = h.size := by
  simp [VG.Proof.MlDsa.Pack.huSet]

/-- Coefficient `j` of polynomial `i'` after setting coefficient `b` of
polynomial `i`. -/
theorem huSet_get {i b : Nat} {h : Array (Vector Bool n)} (hi : i < h.size) {i' j : Nat}
    (hj : j < n) :
    ((VG.Proof.MlDsa.Pack.huSet i b h).getD i' VG.Proof.MlDsa.Pack.noHint)[j]! = if i' = i ∧ j = b then true else (h.getD i' VG.Proof.MlDsa.Pack.noHint)[j]! := by
  simp only [VG.Proof.MlDsa.Pack.huSet, Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases e : i = i'
  · subst e
    simp only [ite_true, hi, Option.getD_some]
    rw [getElem!_pos _ j hj, getElem!_pos _ j hj, Vector.set!_eq_setIfInBounds, Vector.getElem_setIfInBounds]
    by_cases e2 : b = j
    · subst e2; simp
    · simp [e2, Ne.symm e2]
  · simp [e, Ne.symm e]

end VG.Proof.MlDsa.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Pack.HintMem`. -/
section

/-!
# ML-DSA: hints in memory, for every target

The parameters `(ω, k)` of the hint encodings, the coefficients of a hint
stored as words (`hintAt`), and facts the proofs of `HintBitPack` and
`HintBitUnpack` share on every target.
-/

namespace VG.Proof.MlDsa.Pack

open VG.Spec.MlDsa

theorem mem_hintParams {ω k : Nat} (h : (ω, k) ∈ hintParams) : 4 ≤ k ∧ k ≤ 8 ∧ ω ≤ 80 := by
  simp only [hintParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  omega

/-- Coefficient `j` of polynomial `i` of the hint at `p`. -/
theorem hintAt_get {m : Mem} {p : Addr} {k i j : Nat} (hi : i < k) (hj : j < n) :
    ((hintAt m p k).getD i VG.Proof.MlDsa.Pack.noHint)[j]! = decide (coeffAt m p (256 * i + j) ≠ 0) := by
  rw [hintAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some, getElem!_pos _ j hj, Vector.getElem_ofFn]

theorem hintAt_length (m : Mem) (p : Addr) (k : Nat) : (hintAt m p k).length = k := by simp [hintAt]

theorem coeffAt_zeroMem (p : Addr) (i : Nat) : coeffAt (fun _ => 0#8) p i = 0#32 := by
  simp only [coeffAt, Mem.readW, Mem.read]
  rfl

theorem filter_false : ((Vector.ofFn fun _ : Fin n => false).toList.filter id) = [] := by
  rw [List.filter_eq_nil_iff]; intro a ha; simp at ha; simp [ha]

theorem sum_zero : ∀ l : List Nat, (l.map fun _ => 0).sum = 0
  | [] => rfl
  | _ :: l => by rw [List.map_cons, List.sum_cons, VG.Proof.MlDsa.Pack.sum_zero l]

/-- The hint in memory of zeros has no 1s. -/
theorem hintOnes_zero (p : Addr) (k : Nat) : hintOnes (hintAt (fun _ => 0) p k) = 0 := by
  simp [hintOnes, hintAt, VG.Proof.MlDsa.Pack.coeffAt_zeroMem, Function.comp_def, VG.Proof.MlDsa.Pack.filter_false, VG.Proof.MlDsa.Pack.sum_zero]

theorem map_toNat_inj : ∀ {b₁ b₂ : List Byte}, b₁.map (·.toNat) = b₂.map (·.toNat) → b₁ = b₂
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, VG.Proof.MlDsa.Pack.map_toNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- A byte of the words of a region of zero words. -/
theorem byte_of_zero_words {m : Mem} {p : Addr} {N : Nat} (hz : ∀ t < N, coeffAt m p t = 0) {a : Addr}
    (ha : (⟨p, N * 4⟩ : Region).Contains a 1) : m a = 0 := by
  simp only [Region.Contains] at ha
  have ht : (a - p).toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  have ea : a = VG.Proof.MlDsa.Pack.coeffAddr p ((a - p).toNat / 4) + BitVec.ofNat 64 ((a - p).toNat % 4) := by
    rw [VG.Proof.MlDsa.Pack.coeffAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ea, Mem.readW_byte m (VG.Proof.MlDsa.Pack.coeffAddr p _) ht, ← VG.Proof.MlDsa.Pack.coeffAt_eq, hz _ (by omega)]
  simp

/-- `a - b` in 64 bits, for `a, b < 2⁶³`: its sign bit says whether `a < b`. -/
theorem sub_lsr63 {a b : BitVec 64} (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63) :
    ((a - b) >>> 63).toNat = if a.toNat < b.toNat then 1 else 0 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
  split <;> omega

end VG.Proof.MlDsa.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Pack.Hint2`. -/
section

/-!
# ML-DSA: `HintBitPack` and `HintBitUnpack` in memory, for every target

What an implementation of `HintBitPack` and `HintBitUnpack` that follows the
folds of `Pack/Hint.lean` needs about memory and the parameters, on any
target: the parameters of `hintParams`, the coefficients of `hintAt` and when
two memories give the same hint (`hintAt_congr`, from equal leaks:
`coeffAt_of_leak`), the state of the fold of `HintBitPack` after `i`
polynomials and `j` more coefficients (`hpS`, `hpT`), and the words of a hint
that `HintBitUnpack` fills in (`HArr`).
-/

namespace VG.Proof.MlDsa.Pack

open VG.Spec.MlDsa

/-- The hint is a function of its words. -/
theorem hintAt_congr {m m' : Mem} {p : Addr} {k : Nat}
    (h : ∀ t < 256 * k, coeffAt m p t = coeffAt m' p t) : hintAt m p k = hintAt m' p k := by
  unfold hintAt
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  refine Vector.ext fun j hj => ?_
  simp only [Vector.getElem_ofFn]
  rw [h _ (by rw [VG.Proof.MlDsa.Pack.n_eq] at hj; omega)]

/-- Words whose values are the same numbers are equal. -/
theorem coeffAt_of_leak {m m' : Mem} {p : Addr} {N : Nat}
    (h : (List.range N).map (fun i => (coeffAt m p i).toNat) = (List.range N).map (fun i => (coeffAt m' p i).toNat)) :
    ∀ t < N, coeffAt m p t = coeffAt m' p t := fun t ht =>
  BitVec.eq_of_toNat_eq (List.map_inj_left.mp h t (List.mem_range.mpr ht))

/-! ## Memory of zeros -/

theorem read_zero (a : Addr) : ∀ k, Mem.read (fun _ => 0) a k = 0
  | 0 => rfl
  | k + 1 => by
    rw [Mem.read, VG.Proof.MlDsa.Pack.read_zero (a + 1) k]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_append]
    have (w : Nat) : (0 : BitVec w).toNat = 0 := BitVec.toNat_zero
    rw [this, this, this]
    rfl

theorem coeffAt_zero (p : Addr) (i : Nat) : coeffAt (fun _ => 0) p i = 0 := by
  simp only [coeffAt, Mem.readW, VG.Proof.MlDsa.Pack.read_zero]
  rfl

theorem coeffAt_zero' (p : Addr) (i : Nat) : coeffAt (fun _ => 0#8) p i = 0#32 := VG.Proof.MlDsa.Pack.coeffAt_zero p i

/-- A hint of zero words has no 1s. -/
theorem hintOnes_of_zero {m : Mem} {p : Addr} {k : Nat} (h : ∀ t < 256 * k, coeffAt m p t = 0) :
    hintOnes (hintAt m p k) = 0 := by
  rw [VG.Proof.MlDsa.Pack.hintAt_congr (m' := fun _ => 0) fun t ht => by rw [h t ht, VG.Proof.MlDsa.Pack.coeffAt_zero]]
  simp [hintOnes, hintAt, VG.Proof.MlDsa.Pack.coeffAt_zero', Function.comp_def, VG.Proof.MlDsa.Pack.filter_false, VG.Proof.MlDsa.Pack.sum_zero]

/-! ## `HintBitPack` -/

/-- The spec's state after `i` polynomials. -/
def hpS (ω k : Nat) (h : List (Vector Bool n)) (i : Nat) : Array Byte × Nat :=
  (List.range i).foldl (VG.Proof.MlDsa.Pack.hpPoly ω h) (Array.replicate (ω + k) 0, 0)

/-- ... and `j` coefficients of polynomial `i`. -/
def hpT (ω k : Nat) (h : List (Vector Bool n)) (i j : Nat) : Array Byte × Nat :=
  (List.range j).foldl (VG.Proof.MlDsa.Pack.hpStep (h.getD i VG.Proof.MlDsa.Pack.noHint)) (VG.Proof.MlDsa.Pack.hpS ω k h i)

theorem hpS_zero (ω k : Nat) (h : List (Vector Bool n)) : VG.Proof.MlDsa.Pack.hpS ω k h 0 = (Array.replicate (ω + k) 0, 0) := rfl

theorem hpT_zero (ω k : Nat) (h : List (Vector Bool n)) (i : Nat) : VG.Proof.MlDsa.Pack.hpT ω k h i 0 = VG.Proof.MlDsa.Pack.hpS ω k h i := rfl

theorem hpS_idx (ω k : Nat) (h : List (Vector Bool n)) (i : Nat) : (VG.Proof.MlDsa.Pack.hpS ω k h i).2 = VG.Proof.MlDsa.Pack.onesBefore h i 0 := by
  rw [VG.Proof.MlDsa.Pack.hpS, VG.Proof.MlDsa.Pack.hpPolys_idx]; exact Nat.zero_add _

theorem hpT_idx (ω k : Nat) (h : List (Vector Bool n)) (i j : Nat) : (VG.Proof.MlDsa.Pack.hpT ω k h i j).2 = VG.Proof.MlDsa.Pack.onesBefore h i j := by
  rw [VG.Proof.MlDsa.Pack.hpT, VG.Proof.MlDsa.Pack.hpSteps_idx, VG.Proof.MlDsa.Pack.hpS_idx]; unfold VG.Proof.MlDsa.Pack.onesBefore; rfl

theorem hpT_succ (ω k : Nat) (h : List (Vector Bool n)) (i j : Nat) :
    VG.Proof.MlDsa.Pack.hpT ω k h i (j + 1) = VG.Proof.MlDsa.Pack.hpStep (h.getD i VG.Proof.MlDsa.Pack.noHint) (VG.Proof.MlDsa.Pack.hpT ω k h i j) j := by
  rw [VG.Proof.MlDsa.Pack.hpT, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]; rfl

theorem hpS_succ (ω k : Nat) (h : List (Vector Bool n)) (i : Nat) :
    VG.Proof.MlDsa.Pack.hpS ω k h (i + 1) = ((VG.Proof.MlDsa.Pack.hpT ω k h i n).1.set! (ω + i) (BitVec.ofNat 8 (VG.Proof.MlDsa.Pack.hpT ω k h i n).2), (VG.Proof.MlDsa.Pack.hpT ω k h i n).2) := by
  rw [VG.Proof.MlDsa.Pack.hpS, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

theorem hintBitPack_hpS (ω k : Nat) (h : List (Vector Bool n)) : hintBitPack ω k h = (VG.Proof.MlDsa.Pack.hpS ω k h k).1.toList :=
  VG.Proof.MlDsa.Pack.hintBitPack_eq ω k h

/-- The index before a 1 is less than `ω`. -/
theorem hpT_idx_lt {ω k : Nat} {h : List (Vector Bool n)} (hk : h.length = k) (hω : hintOnes h ≤ ω) {i j : Nat}
    (hi : i < k) (hj : j < n) (h1 : (h.getD i VG.Proof.MlDsa.Pack.noHint)[j]! = true) : (VG.Proof.MlDsa.Pack.hpT ω k h i j).2 < ω := by
  rw [VG.Proof.MlDsa.Pack.hpT_idx]; have := VG.Proof.MlDsa.Pack.hpIdx_lt hk hi hj h1; omega

/-- The index after a polynomial is at most `ω`. -/
theorem hpT_idx_le {ω k : Nat} {h : List (Vector Bool n)} (hk : h.length = k) (hω : hintOnes h ≤ ω) {i : Nat}
    (hi : i < k) : (VG.Proof.MlDsa.Pack.hpT ω k h i n).2 ≤ ω := by
  rw [VG.Proof.MlDsa.Pack.hpT_idx]; have := VG.Proof.MlDsa.Pack.onesBefore_n_le hk hi; omega

/-! ## `HintBitUnpack` -/

/-- The `256k` words at `p` are the hint `hA`. -/
def HArr (m : Mem) (p : Addr) (k : Nat) (hA : Array (Vector Bool n)) : Prop :=
  hA.size = k ∧ ∀ i < k, ∀ j < 256, coeffAt m p (256 * i + j) = BitVec.ofNat 32 ((hA.getD i VG.Proof.MlDsa.Pack.noHint)[j]!).toNat

/-- Setting coefficient `b` of polynomial `i`. -/
theorem harr_set {m : Mem} {p : Addr} {k : Nat} (hk : k ≤ 8) {hA : Array (Vector Bool n)} (hh : VG.Proof.MlDsa.Pack.HArr m p k hA)
    {i b : Nat} (hi : i < k) (hb : b < 256) :
    VG.Proof.MlDsa.Pack.HArr (m.writeW (VG.Proof.MlDsa.Pack.coeffAddr p (256 * i + b)) (1 : BitVec 32)) p k (VG.Proof.MlDsa.Pack.huSet i b hA) := by
  refine ⟨by rw [VG.Proof.MlDsa.Pack.huSet_size, hh.1], fun i' hi' j hj => ?_⟩
  rw [VG.Proof.MlDsa.Pack.huSet_get (by rw [hh.1]; exact hi) (show j < n from hj)]
  by_cases e : i' = i ∧ j = b
  · obtain ⟨rfl, rfl⟩ := e
    rw [VG.Proof.MlDsa.Pack.coeffAt_eq, Mem.readW_writeW_self32, VG.Proof.MlDsa.Pack.ite_pos' ⟨rfl, rfl⟩]; rfl
  · rw [VG.Proof.MlDsa.Pack.ite_neg' e, VG.Proof.MlDsa.Pack.coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by
      have : 256 * i' + j ≠ 256 * i + b := fun h' => e ⟨by omega, by omega⟩
      omega) (by omega) (by omega)) (by decide), ← VG.Proof.MlDsa.Pack.coeffAt_eq, hh.2 i' hi' j hj]

/-- Zero words are the hint of zeros. -/
theorem harr_zero {m : Mem} {p : Addr} {k : Nat} (hz : ∀ t < 256 * k, coeffAt m p t = 0) :
    VG.Proof.MlDsa.Pack.HArr m p k (Array.replicate k VG.Proof.MlDsa.Pack.noHint) := by
  refine ⟨Array.size_replicate, fun i hi j hj => ?_⟩
  rw [hz _ (by omega)]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hi, ite_true, Option.getD_some, VG.Proof.MlDsa.Pack.noHint]
  rw [getElem!_pos _ j (show j < n from hj), Vector.getElem_replicate]
  rfl

theorem harr_congr {m m' : Mem} {p : Addr} {k : Nat} {hA : Array (Vector Bool n)} (hh : VG.Proof.MlDsa.Pack.HArr m p k hA)
    (h : ∀ t < 256 * k, coeffAt m' p t = coeffAt m p t) : VG.Proof.MlDsa.Pack.HArr m' p k hA :=
  ⟨hh.1, fun i hi j hj => by rw [h _ (by omega)]; exact hh.2 i hi j hj⟩

/-- The hint of the spec, from the words. -/
theorem harr_hintIs {m : Mem} {p : Addr} {k : Nat} {hA : Array (Vector Bool n)} (hh : VG.Proof.MlDsa.Pack.HArr m p k hA) :
    HintIs m p k hA.toList := by
  refine ⟨by rw [Array.length_toList, hh.1], fun i hi j hj => ?_⟩
  rw [hh.2 i hi j hj]
  congr 3
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, ← Array.getD_eq_getD_getElem?]

theorem huStep_idx {y : Array Byte} {i first : Nat} {st st' : Array (Vector Bool n) × Nat} {x : Nat}
    (h : VG.Proof.MlDsa.Pack.huStep y i first st x = some st') : st'.2 = st.2 + 1 := by
  unfold VG.Proof.MlDsa.Pack.huStep at h
  split at h
  · cases h
  · cases h; rfl

end VG.Proof.MlDsa.Pack

end
