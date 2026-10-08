import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays

/-!
# ECDSA on AArch64: what every phase keeps

After `setup`, the slots below `12` but the temporary area's hold constants
the code only reads, and `[0, 64)` the saved registers (`Fixed`); every
later phase writes only slots from `12` on, the temporary area, the flag
and the tables (`FixedOk`), so it keeps them (`Fixed.unch`). A slot or a
table byte apart from what a phase writes keeps its value too (`sv_unch`,
`tbl_unch`).
-/

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- The constants and the saved registers `g`. -/
structure Fixed (c : Cfg) (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop where
  mp : wordsVal m base (c.sl MP) c.n = c.C.p
  mn : wordsVal m base (c.sl MN) c.n = c.C.n
  zero : wordsVal m base (c.sl ZERO) c.n = 0
  one : wordsVal m base (c.sl ONE) c.n = 1
  onep : wordsVal m base (c.sl ONEP) c.n = 2 ^ (64 * c.n) % c.C.p
  ap : wordsVal m base (c.sl AP) c.n = c.mont c.C.a
  bm : wordsVal m base (c.sl BM) c.n = c.mont c.C.b
  gx : wordsVal m base (c.sl GX) c.n = c.mont c.C.gx
  gy : wordsVal m base (c.sl GY) c.n = c.mont c.C.gy
  r2n : wordsVal m base (c.sl R2N) c.n = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n
  onen : wordsVal m base (c.sl ONEN) c.n = 2 ^ (64 * c.n) % c.C.n
  saved : Spill.Saved base g Cfg.saved m

/-- What a phase writes misses the constants and the saved registers. -/
def FixedOk (c : Cfg) (W : List (Nat × Nat)) : Prop :=
  ∀ w ∈ W, (w.1 = c.sl TMP ∧ w.2 = 8 * c.n) ∨ c.sl 12 ≤ w.1

/-- The ranges of numbered slots. -/
abbrev slW (c : Cfg) (l : List Nat) : List (Nat × Nat) := l.map fun i => (c.sl i, 8 * c.n)

theorem FixedOk.append {W W' : List (Nat × Nat)} (h : FixedOk c W) (h' : FixedOk c W') :
    FixedOk c (W ++ W') := fun w hw => (List.mem_append.mp hw).elim (h w) (h' w)

theorem fixedOk_slW {l : List Nat} (hl : ∀ i ∈ l, i = TMP ∨ 12 ≤ i) : FixedOk c (slW c l) := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  rcases hl i hi with h | h
  · exact Or.inl ⟨by rw [h], rfl⟩
  · refine Or.inr ?_
    rcases Nat.eq_or_lt_of_le h with h | h
    · rw [h]
    · exact Nat.le_trans (Nat.le_add_right _ _) (sl_lt c h)

theorem fixedOk_tbl (j : Nat) : FixedOk c [(bitsAt c.n j, 64 * c.n)] := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_bits c (by decide) j 0))

theorem fixedOk_flag : FixedOk c [(c.sl FLAG, 8)] := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (show 12 < FLAG by decide)))

theorem fixedOk_whole (h7 : c.n < 10) : FixedOk c [(size, 2 ^ 64)] := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  refine Or.inr ?_
  have := sl_le c (i := 12) h7 (by decide)
  show c.sl 12 ≤ size
  omega

/-- A constant's slot is apart from what a phase writes. -/
theorem fixed_apart {W : List (Nat × Nat)} (hW : FixedOk c W) {i : Nat} (hi : i < 12) (hit : i ≠ TMP) :
    ∀ w ∈ W, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rcases hW w hw with ⟨h1, h2⟩ | h
  · rw [h1, h2]; exact sl_apart c hit
  · exact Or.inl (Nat.le_trans (sl_lt c hi) h)

theorem Fixed.unch {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Fixed c base g m)
    (h7 : c.n < 10) (hn : base.toNat + size ≤ 2 ^ 64) {W : List (Nat × Nat)} (hW : FixedOk c W)
    (hu : Unch base W m m') : Fixed c base g m' := by
  have e : ∀ i, i < 12 → i ≠ TMP → wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n :=
    fun i hi hit => hu.wordsVal (fixed_apart hW hi hit) (by have := sl_le c h7 (i := i) (by omega); omega)
  refine ⟨(e MP (by decide) (by decide)).trans h.mp, (e MN (by decide) (by decide)).trans h.mn,
    (e ZERO (by decide) (by decide)).trans h.zero, (e ONE (by decide) (by decide)).trans h.one,
    (e ONEP (by decide) (by decide)).trans h.onep, (e AP (by decide) (by decide)).trans h.ap,
    (e BM (by decide) (by decide)).trans h.bm, (e GX (by decide) (by decide)).trans h.gx,
    (e GY (by decide) (by decide)).trans h.gy, (e R2N (by decide) (by decide)).trans h.r2n,
    (e ONEN (by decide) (by decide)).trans h.onen, fun p hp => ?_⟩
  have := setupSaved_lt p hp
  refine (hu.word (d := p.2) (fun w hw => Or.inl ?_) (by omega)).trans (h.saved p hp)
  rcases hW w hw with ⟨h1, -⟩ | h
  · rw [h1]; have := sl_ge64 c TMP; omega
  · simp (disch := decide) only [sl_eq] at h; omega

/-- A slot apart from the ranges of other numbered slots. -/
theorem apart_slW {l : List Nat} {i : Nat} (hi : i ∉ l)
    (hiA : i ≠ 54 ∧ i ≠ 82 := by first | decide | exact ⟨by omega, by omega⟩)
    (hl : ∀ j ∈ l, j ≠ 54 ∧ j ≠ 82 := by decide) :
    ∀ w ∈ slW c l, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
  exact sl_apart c (fun h => hi (h ▸ hj)) (.inr (hl j hj)) (.inr hiA)

theorem apart_tbl {i : Nat} (hi : i < 45) (j : Nat) (h7 : c.n < 10)
    (hj0 : j = 0 ∨ i ≠ TMP := by first | exact .inl rfl | exact .inr (by sl_ne)) :
    ∀ w ∈ [(bitsAt c.n j, 64 * c.n)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  by_cases hT : i = TMP
  · subst hT
    obtain rfl := hj0.resolve_right (fun h => h rfl)
    exact tmp_bits0 c h7
  · exact Or.inl (by have := sl_below_bits c hi j 0 hT; omega)

theorem apart_flag (h0 : 0 < c.n) {i : Nat} (hi : i ≠ FLAG) :
    ∀ w ∈ [(c.sl FLAG, 8)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  have := sl_apart c hi
  dsimp only
  omega

theorem apart_append {W W' : List (Nat × Nat)} {x k : Nat}
    (h : ∀ w ∈ W, x + k ≤ w.1 ∨ w.1 + w.2 ≤ x) (h' : ∀ w ∈ W', x + k ≤ w.1 ∨ w.1 + w.2 ≤ x) :
    ∀ w ∈ W ++ W', x + k ≤ w.1 ∨ w.1 + w.2 ≤ x :=
  fun w hw => (List.mem_append.mp hw).elim (h w) (h' w)

/-- A number in a slot apart from what changed. -/
theorem sv_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (hu : Unch base W m m')
    (h7 : c.n < 10) (hn : base.toNat + size ≤ 2 ^ 64) {i : Nat} (hi : i < 45)
    (hW : ∀ w ∈ W, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i) :
    wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n :=
  hu.wordsVal hW (by have := sl_le c h7 hi; omega)

/-- A byte of table `j` apart from what changed. -/
theorem tbl_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (hu : Unch base W m m')
    (h7 : c.n < 10) {j t : Nat} (hj : j < 3) (ht : t < 64 * c.n)
    (hW : ∀ w ∈ W, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t) :
    m' (off base (bitsAt c.n j + t)) = m (off base (bitsAt c.n j + t)) :=
  hu.byte hW (by have := bitsAt_le c h7 hj; have : size = 8192 := rfl; omega)

theorem tbl_apart_slW {l : List Nat} (hl : ∀ i ∈ l, i < 45 ∧ i ≠ TMP) (j t : Nat) :
    ∀ w ∈ slW c l, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  exact Or.inr (sl_below_bits c (hl i hi).1 j t (hl i hi).2)

theorem tbl_apart_flag (h0 : 0 < c.n) (j t : Nat) :
    ∀ w ∈ [(c.sl FLAG, 8)], bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  have := sl_below_bits c (i := FLAG) (by decide) j t
  exact Or.inr (by dsimp only; omega)

/-- Tables `j ≠ j'` are apart. -/
theorem tbl_apart_tbl {j j' t : Nat} (hjj : j ≠ j') (ht : t < 64 * c.n) :
    ∀ w ∈ [(bitsAt c.n j', 64 * c.n)], bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  simp only [bitsAt_eq]
  rcases Nat.lt_or_gt_of_ne hjj with h | h
  · have := Nat.mul_le_mul_left (64 * c.n) h
    rw [Nat.mul_succ] at this
    omega
  · have := Nat.mul_le_mul_left (64 * c.n) h
    rw [Nat.mul_succ] at this
    omega

/-- What a power writes: `ACC`, its table and the temporary area. -/
abbrev chainWc (c : Cfg) : List (Nat × Nat) :=
  [(c.sl ACC, 8 * c.n), (c.sl CT, 9 * (8 * c.n)), (c.sl TMP, 8 * c.n)]

theorem invWP_eq (c : Cfg) : invW c.invP = chainWc c := rfl
theorem invWN_eq (c : Cfg) : invW c.invN = chainWc c := rfl
theorem chainWN_eq (c : Cfg) : chainW c.powN = chainWc c := rfl

theorem fixedOk_chainWc : FixedOk c (chainWc c) := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (show 12 < ACC by decide)))
  · exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (show 12 < CT by decide)))
  · exact Or.inl ⟨rfl, rfl⟩

/-- A slot but `ACC` and `TMP` is apart from what a power writes. -/
theorem apart_chainWc {i : Nat} (hi : i < 45) (hl : i ∉ [ACC, TMP]) :
    ∀ w ∈ chainWc c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw hl
  rcases hw with rfl | rfl | rfl
  · exact sl_apart c hl.1
  · exact Or.inl (sl_lt c (show i < CT by unfold CT; omega))
  · exact sl_apart c hl.2

/-- The flag survives a power and changes of other slots. -/
theorem flag_unch_cw {base : Addr} {l : List Nat} {m m' : Mem} (hu : Unch base (chainWc c ++ slW c l) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 64) (hl : FLAG ∉ l)
    (hlA : ∀ j ∈ l, j ≠ 54 ∧ j ≠ 82 := by decide) :
    word m' base (c.sl FLAG) = word m base (c.sl FLAG) := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine hu.word (fun w hw => ?_) (by omega)
  rcases apart_append (apart_chainWc (c := c) (i := FLAG) (by decide) (by decide)) (apart_slW hl (hl := hlA)) w hw
    with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

/-- The flag survives a power. -/
theorem flag_unch_chain {base : Addr} {m m' : Mem} (hu : Unch base (chainWc c) m m') (h7 : c.n < 10)
    (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 64) :
    word m' base (c.sl FLAG) = word m base (c.sl FLAG) := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine hu.word (fun w hw => ?_) (by omega)
  rcases apart_chainWc (c := c) (i := FLAG) (by decide) (by decide) w hw with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

/-- The moduli, from their slots. -/
theorem modP_of (hc : BaseCfgOk c) {base : Addr} {m : Mem} (h : wordsVal m base (c.sl MP) c.n = c.C.p) :
    ModOkA c.MP' size c.C.p m base :=
  ⟨hc.n0, hc.n10, sl_le c hc.n10 (i := MP) (by decide), sl_le c hc.n10 (i := TMP) (by decide),
    sl_apart c (show MP ≠ TMP by decide), h,
    hc.minv_p, hc.red_p, fun f m' h' => (hc.call_p f m' h').1⟩

theorem modN_of (hc : BaseCfgOk c) {base : Addr} {m : Mem} (h : wordsVal m base (c.sl MN) c.n = c.C.n) :
    ModOkA c.MN' size c.C.n m base :=
  ⟨hc.n0, hc.n10, sl_le c hc.n10 (i := MN) (by decide), sl_le c hc.n10 (i := TMP) (by decide),
    sl_apart c (show MN ≠ TMP by decide), h,
    hc.minv_n, hc.red_n, fun _ _ h' => nomatch hc.call_n.symm.trans h'⟩

/-- `ACC = RZ^(p - 2)` (in Montgomery form), by divsteps. -/
theorem pPow_ok (hc : BaseCfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    (hM : ModOkA c.MP' size c.C.p s.mem base) (hB : wordsVal s.mem base (c.sl RZ) c.n < c.C.p) :
    WP isa c.pPow s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (chainWc c) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl ACC) c.n < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
        toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl RZ) c.n) ^ (c.C.p - 2) := by
  have := hc.p_ge
  exact hc.sound_p (invLayP hc) (by omega) (unitMod_pow_two hc.p_odd _) hs hM hB hc.inv_p

/-- `ACC = KM^(n - 2)` (in Montgomery form), by divsteps or a chain. -/
theorem nPow_ok (hc : BaseCfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    (hM : ModOkA c.MN' size c.C.n s.mem base) (hB : wordsVal s.mem base (c.sl KM) c.n < c.C.n) :
    WP isa c.nPow s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (chainWc c) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl ACC) c.n < c.C.n ∧
      toM c.C.n (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
        toM c.C.n (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl KM) c.n) ^ (c.C.n - 2) := by
  have := hc.n_ge
  rw [Cfg.nPow]
  split
  · rename_i h
    exact (hc.inv_n h).1 (invLayN hc) (by omega) (unitMod_pow_two hc.n_odd _) hs hM hB (hc.inv_n h).2
  · rename_i h
    exact WP.mono (chainPow_ok (chainLayN hc) (unitMod_pow_two hc.n_odd _) hs hM hB
      (chainOkN hc (by simpa using h))) fun s' ⟨K, U, lt, v⟩ => ⟨K, by rw [chainWN_eq] at U; exact U, lt, v⟩

theorem x20_not_clob {n : Nat} (h : n < 10) : Reg.x20 ∉ clob n := by
  have : ∀ n < 10, Reg.x20 ∉ clob n := by decide
  exact this n h

theorem x20_not_powClob {n : Nat} (h : n < 10) : Reg.x20 ∉ powClob n := by
  intro h'
  rcases List.mem_cons.mp h' with h' | h'
  · exact absurd h' (by decide)
  · exact x20_not_clob h h'

end VG.Proof.Ecdsa.AArch64
