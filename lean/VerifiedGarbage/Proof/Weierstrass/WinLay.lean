import VerifiedGarbage.Proof.Weierstrass.Layout

/-!
# The window method: where it keeps its numbers

The slots the window method reads and writes, and what it needs of them
(`WinLay`): in the working space and apart (`Lay`), the slots read only not
written, the other slots written distinct, the table of points `[1 … 8]P`
(24 consecutive slots, `winTblSlots`) apart from all of them, and the table
of bits apart from what is written. Facts about offsets, as for the comb
(`CombLay`): the complete additions' slots are apart as they need
(`WinLay.rcbApart_*`).
-/

namespace VG.Proof.Weierstrass

open VG VG.Impl.Mont VG.Impl.Weierstrass VG.Proof.Mont

/-- The slots of the table of points: coordinate `c` of `[m]P` is slot
`3 (m - 1) + c`. -/
def winTblSlots (K : WinCfg) : List Nat := (List.range 24).map fun i => K.tbl + 8 * K.M.n * i

/-- The slots it writes but the table's. -/
def winOther (K : WinCfg) : List Nat := [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.neg] ++ rcbW K.S K.D

/-- The slots it reads only: the curve's `a` and `3b`, zero and `P`. -/
def winRo (K : WinCfg) : List Nat := [K.S.a, K.S.b3, K.zero, K.P.x, K.P.y, K.P.z]

/-- The slots of the window method. -/
def winSlots (K : WinCfg) : List Nat := winRo K ++ winOther K ++ winTblSlots K

/-- The slots it writes. -/
def winWs (K : WinCfg) : List Nat := winOther K ++ winTblSlots K

/-- What it writes: its slots and the modulus's temporary area. -/
def winW (K : WinCfg) : List (Nat × Nat) :=
  (winWs K).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)]

/-- The window method's slots are in the working space and apart (`lay`),
the slots read only are not written (`ro`), the other slots written are
distinct (`nodup`), the table is apart from them all (`tbl`), and the table
of bits (`4 J` bytes) is apart from what is written. -/
structure WinLay (K : WinCfg) (size : Nat) : Prop where
  lay : Lay K.M size (· ∈ winSlots K)
  ro : ∀ x ∈ winRo K, x ∉ winOther K
  nodup : (winOther K).Nodup
  tbl : ∀ x ∈ winRo K ++ winOther K, x + 8 * K.M.n ≤ K.tbl ∨ K.tbl + 24 * (8 * K.M.n) ≤ x
  n0 : 0 < K.M.n
  J : 1 ≤ K.J ∧ K.J ≤ 4096
  bits : K.bits + 4 * K.J ≤ size
  bits4 : K.bits + 3 < 4096
  bits_w : ∀ w ∈ winW K, K.bits + 4 * K.J ≤ w.1 ∨ w.1 + w.2 ≤ K.bits

/-- `x ∈ l` for the window method's lists. -/
macro "win_mem" : tactic => `(tactic| (simp only [List.mem_cons, List.mem_append,
  List.mem_singleton, true_or, or_true, winSlots, winWs, winRo, winOther, rcbW, rcbR,
  List.cons_append, List.nil_append]))

theorem winWs_slots (K : WinCfg) : ∀ x ∈ winWs K, x ∈ winSlots K := by
  intro x hx
  simp only [winWs, winSlots, List.mem_append] at hx ⊢
  grind

theorem winRo_slots (K : WinCfg) : ∀ x ∈ winRo K, x ∈ winSlots K := by
  intro x hx
  simp only [winSlots, List.mem_append]
  exact Or.inl (Or.inl hx)

theorem winOther_ws (K : WinCfg) : ∀ x ∈ winOther K, x ∈ winWs K :=
  fun _ hx => List.mem_append_left _ hx

/-- Slot `i < 24` of the table. -/
theorem winTbl_mem (K : WinCfg) {i : Nat} (hi : i < 24) : K.tbl + 8 * K.M.n * i ∈ winTblSlots K :=
  List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem winTbl_ws (K : WinCfg) {i : Nat} (hi : i < 24) : K.tbl + 8 * K.M.n * i ∈ winWs K :=
  List.mem_append_right _ (winTbl_mem K hi)

theorem tblPt_x (K : WinCfg) (m : Nat) : (K.tblPt m).x = K.tbl + 8 * K.M.n * (3 * (m - 1)) := by
  simp only [WinCfg.tblPt]; grind

theorem tblPt_y (K : WinCfg) (m : Nat) :
    (K.tblPt m).y = K.tbl + 8 * K.M.n * (3 * (m - 1) + 1) := by
  simp only [WinCfg.tblPt]; grind

theorem tblPt_z (K : WinCfg) (m : Nat) :
    (K.tblPt m).z = K.tbl + 8 * K.M.n * (3 * (m - 1) + 2) := by
  simp only [WinCfg.tblPt]; grind

/-- The coordinates of `[m]P`, `1 ≤ m ≤ 8`, are table slots. -/
theorem tblPt_mem (K : WinCfg) {m : Nat} (h1 : 1 ≤ m) (h8 : m ≤ 8) :
    ∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z], ∃ i < 24, x = K.tbl + 8 * K.M.n * i ∧
      3 * (m - 1) ≤ i ∧ i < 3 * m := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨_, by omega, tblPt_x K m, by omega, by omega⟩
  · exact ⟨_, by omega, tblPt_y K m, by omega, by omega⟩
  · exact ⟨_, by omega, tblPt_z K m, by omega, by omega⟩

/-- Table slots `i ≠ j` are apart. -/
theorem winTbl_apart (K : WinCfg) {i j : Nat} (h : i ≠ j) :
    K.tbl + 8 * K.M.n * i + 8 * K.M.n ≤ K.tbl + 8 * K.M.n * j ∨
      K.tbl + 8 * K.M.n * j + 8 * K.M.n ≤ K.tbl + 8 * K.M.n * i := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · left; have := Nat.mul_le_mul_left (8 * K.M.n) (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at this; omega
  · right; have := Nat.mul_le_mul_left (8 * K.M.n) (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at this; omega

/-- A table slot is apart from the other slots. -/
theorem WinLay.tbl_apart {K : WinCfg} {size : Nat} (hL : WinLay K size) {x : Nat}
    (hx : x ∈ winRo K ++ winOther K) {i : Nat} (hi : i < 24) :
    x + 8 * K.M.n ≤ K.tbl + 8 * K.M.n * i ∨ K.tbl + 8 * K.M.n * i + 8 * K.M.n ≤ x := by
  have h24 : 8 * K.M.n * i + 8 * K.M.n ≤ 24 * (8 * K.M.n) := by
    rw [show 24 * (8 * K.M.n) = 8 * K.M.n * 24 from Nat.mul_comm _ _, ← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ hi
  rcases hL.tbl x hx with h | h
  · left; omega
  · right; omega

theorem WinLay.tbl_ne {K : WinCfg} {size : Nat} (hL : WinLay K size) {x : Nat}
    (hx : x ∈ winRo K ++ winOther K) {i : Nat} (hi : i < 24) : x ≠ K.tbl + 8 * K.M.n * i := by
  have := hL.n0
  rcases hL.tbl_apart hx hi with h | h <;> omega

/-- A slot not written is apart from what is written. -/
theorem WinLay.apart_w {K : WinCfg} {size : Nat} (hL : WinLay K size) {x : Nat}
    (hx : x ∈ winSlots K) (hxw : x ∉ winWs K) :
    ∀ w ∈ winW K, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro w hw
  simp only [winW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · exact hL.lay.apart x y hx (winWs_slots K y hy) fun h => hxw (h ▸ hy)
  · exact hL.lay.tmp x hx

/-- A slot read only is apart from what is written. -/
theorem WinLay.ro_w {K : WinCfg} {size : Nat} (hL : WinLay K size) {x : Nat} (hx : x ∈ winRo K) :
    ∀ w ∈ winW K, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  refine hL.apart_w (winRo_slots K x hx) fun h => ?_
  rcases List.mem_append.mp h with h | h
  · exact hL.ro x hx h
  · obtain ⟨i, hi, e⟩ := List.mem_map.mp h
    exact hL.tbl_ne (List.mem_append_left _ hx) (List.mem_range.mp hi) e.symm

/-- Two distinct slots written are apart. -/
theorem WinLay.apart₂ {K : WinCfg} {size : Nat} (hL : WinLay K size) {x y : Nat}
    (hx : x ∈ winWs K) (hy : y ∈ winWs K) (hxy : x ≠ y) :
    x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x :=
  hL.lay.apart x y (winWs_slots K x hx) (winWs_slots K y hy) hxy

/-- The other slots written, as `Nodup` gives them. -/
theorem WinLay.other_ne {K : WinCfg} {size : Nat} (hL : WinLay K size) :
    K.R.x ≠ K.R.y ∧ K.R.x ≠ K.R.z ∧ K.R.y ≠ K.R.z ∧
    (∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∉ [K.E.x, K.E.y, K.E.z, K.neg] ++ rcbW K.S K.D) ∧
    K.E.x ≠ K.E.y ∧ K.E.x ≠ K.E.z ∧ K.E.y ≠ K.E.z ∧
    (∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∉ K.neg :: rcbW K.S K.D) ∧ K.neg ∉ rcbW K.S K.D ∧
    (rcbW K.S K.D).Nodup := by
  have hnd := hL.nodup
  simp only [winOther, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or, forall_eq_or_imp, forall_eq] at hnd ⊢
  grind

/-- Table slots `i ≠ j` are distinct. -/
theorem WinLay.tbl_ne₂ {K : WinCfg} {size : Nat} (hL : WinLay K size) {i j : Nat} (h : i ≠ j) :
    K.tbl + 8 * K.M.n * i ≠ K.tbl + 8 * K.M.n * j := by
  have := hL.n0
  rcases winTbl_apart K h with h | h <;> omega

theorem rcbW_mem_other {K : WinCfg} : ∀ x ∈ [K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5],
    x ∈ winRo K ++ winOther K := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> win_mem

theorem WinLay.ab_not_rcbW {K : WinCfg} {size : Nat} (hL : WinLay K size) {o : Pt} :
    K.S.a ∉ rcbW K.S o ∧ K.S.b3 ∉ rcbW K.S o ↔ K.S.a ∉ [o.x, o.y, o.z] ∧ K.S.b3 ∉ [o.x, o.y, o.z] := by
  have ha := hL.ro K.S.a (by simp [winRo])
  have hb := hL.ro K.S.b3 (by simp [winRo])
  simp only [winOther, rcbW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at ha hb ⊢
  grind

/-- The additions of the loop: into `D`, from `R` and `R` or `E`. -/
theorem WinLay.rcbApart_D {K : WinCfg} {size : Nat} (hL : WinLay K size) {q : Pt}
    (hq : q = K.R ∨ q = K.E) : RcbApart K.S K.R q K.D := by
  obtain ⟨-, -, -, hR, -, -, -, hE, -, hD⟩ := hL.other_ne
  have ha := hL.ro K.S.a (by simp [winRo])
  have hb := hL.ro K.S.b3 (by simp [winRo])
  refine ⟨hD, fun x hx => ?_⟩
  simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
  have hRx : ∀ y ∈ [K.R.x, K.R.y, K.R.z], y ∉ rcbW K.S K.D := fun y hy h =>
    hR y hy (List.mem_append_right _ h)
  have hEx : ∀ y ∈ [K.E.x, K.E.y, K.E.z], y ∉ rcbW K.S K.D := fun y hy h =>
    hE y hy (List.mem_cons_of_mem _ h)
  have hab : ∀ y ∈ [K.S.a, K.S.b3], y ∉ rcbW K.S K.D := by
    intro y hy h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact ha (List.mem_append_right _ h)
    · exact hb (List.mem_append_right _ h)
  rcases hx with rfl | rfl | rfl | rfl | rfl | h
  · exact hab _ (by simp)
  · exact hab _ (by simp)
  · exact hRx _ (by simp)
  · exact hRx _ (by simp)
  · exact hRx _ (by simp)
  · rcases hq with rfl | rfl
    · exact hRx x (by simpa using h)
    · exact hEx x (by simpa using h)

/-- The additions of the table: `[m + 1]P = [m]P + P`. -/
theorem WinLay.rcbApart_tbl {K : WinCfg} {size : Nat} (hL : WinLay K size) {m : Nat}
    (h1 : 1 ≤ m) (h7 : m ≤ 7) : RcbApart K.S (K.tblPt m) (K.tblPt 1) (K.tblPt (m + 1)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hD⟩ := hL.other_ne
  have ets : ∀ o : Pt, rcbW K.S o = [K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5] ++
      [o.x, o.y, o.z] := fun _ => rfl
  rw [ets, List.nodup_append] at hD
  have ho := tblPt_mem K (m := m + 1) (by omega) (by omega)
  have hp := tblPt_mem K (m := m) h1 (by omega)
  have hq := tblPt_mem K (m := 1) (by omega) (by omega)
  have hab : ∀ x ∈ [K.S.a, K.S.b3], x ∈ winRo K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp [winRo]
  refine ⟨?_, fun x hx hw => ?_⟩
  · rw [ets, List.nodup_append]
    refine ⟨hD.1, ?_, fun x hx y hy => ?_⟩
    · obtain ⟨i, hi, ex, -, -⟩ := ho _ (List.mem_cons_self ..)
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, tblPt_x, tblPt_y, tblPt_z, Nat.add_sub_cancel, not_false_eq_true]
      and_intros <;> exact hL.tbl_ne₂ (by omega)
    · obtain ⟨i, hi, rfl, -, -⟩ := ho y hy
      exact hL.tbl_ne (rcbW_mem_other x hx) hi
  · simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [ets, List.mem_append] at hw
    have hxs : x ∈ [K.S.a, K.S.b3] ∨ ∃ i < 24, x = K.tbl + 8 * K.M.n * i ∧ i < 3 * m := by
      rcases hx with rfl | rfl | h
      · exact Or.inl (by simp)
      · exact Or.inl (by simp)
      · refine Or.inr ?_
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨i, hi, e, -, h⟩ := hp (K.tblPt m).x (by simp); exact ⟨i, hi, e, h⟩
        · obtain ⟨i, hi, e, -, h⟩ := hp (K.tblPt m).y (by simp); exact ⟨i, hi, e, h⟩
        · obtain ⟨i, hi, e, -, h⟩ := hp (K.tblPt m).z (by simp); exact ⟨i, hi, e, h⟩
        · obtain ⟨i, hi, e, -, h⟩ := hq (K.tblPt 1).x (by simp); exact ⟨i, hi, e, by omega⟩
        · obtain ⟨i, hi, e, -, h⟩ := hq (K.tblPt 1).y (by simp); exact ⟨i, hi, e, by omega⟩
        · obtain ⟨i, hi, e, -, h⟩ := hq (K.tblPt 1).z (by simp); exact ⟨i, hi, e, by omega⟩
    rcases hw with hw | hw
    · rcases hxs with hxs | ⟨i, hi, rfl, -⟩
      · exact hL.ro x (hab x hxs) (by
          simp only [winOther, List.mem_append]; exact Or.inr (List.mem_append_left _ hw))
      · exact hL.tbl_ne (rcbW_mem_other _ hw) hi rfl
    · obtain ⟨j, hj, rfl, hj₁, -⟩ := ho _ hw
      rcases hxs with hxs | ⟨i, hi, e, hi'⟩
      · exact hL.tbl_ne (List.mem_append_left _ (hab _ hxs)) hj rfl
      · exact hL.tbl_ne₂ (i := i) (j := j) (by omega) e.symm

end VG.Proof.Weierstrass
