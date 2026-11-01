module
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout

import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract

/-!
# ECDSA on AArch64: what every phase keeps

After `setup`, the slots below `12` but the temporary area's hold constants
the code only reads, and `[0, 64)` the saved registers (`Fixed`); every
later phase writes only slots from `12` on, the temporary area, the flag
and the tables (`FixedOk`), so it keeps them (`Fixed.unch`). A slot or a
table byte apart from what a phase writes keeps its value too (`sv_unch`,
`tbl_unch`).
-/

@[expose] public section

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
  ∀ w ∈ W, (w.1 = slot c.n TMP ∧ w.2 = 8 * c.n) ∨ c.sl 12 ≤ w.1

/-- The ranges of numbered slots. -/
abbrev slW (c : Cfg) (l : List Nat) : List (Nat × Nat) := l.map fun i => (c.sl i, 8 * c.n)

theorem FixedOk.append {W W' : List (Nat × Nat)} (h : FixedOk c W) (h' : FixedOk c W') :
    FixedOk c (W ++ W') := fun w hw => (List.mem_append.mp hw).elim (h w) (h' w)

theorem fixedOk_slW {l : List Nat} (hl : ∀ i ∈ l, i = TMP ∨ 12 ≤ i) : FixedOk c (slW c l) := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  rcases hl i hi with h | h
  · subst i
    by_cases ht : c.n = 6 ∨ c.n = 8 ∨ c.n = 9
    · apply Or.inr
      rw [sl_eq c 12, sl_tmp c ht]
      rcases ht with h | h | h <;> rw [h] <;> decide
    · exact Or.inl ⟨by rw [sl_aff c ht]; rfl, rfl⟩
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
  omega_arith

/-- A constant's slot is apart from what a phase writes. -/
theorem fixed_apart {W : List (Nat × Nat)} (hW : FixedOk c W) {i : Nat} (hi : i < 12) (hit : i ≠ TMP) :
    ∀ w ∈ W, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rcases hW w hw with ⟨h1, h2⟩ | h
  · rw [h1, h2]; exact sl_apart_raw_tmp c hit
  · exact Or.inl (Nat.le_trans (sl_lt c hi) h)

theorem Fixed.unch {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Fixed c base g m)
    (h7 : c.n < 10) (hn : base.toNat + size ≤ 2 ^ 64) {W : List (Nat × Nat)} (hW : FixedOk c W)
    (hu : Unch base W m m') : Fixed c base g m' := by
  have e : ∀ i, i < 12 → i ≠ TMP → wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n :=
    fun i hi hit => hu.wordsVal (fixed_apart hW hi hit) (by have := sl_le c h7 (i := i) (by omega_arith); omega_arith)
  refine ⟨(e MP (by decide) (by decide)).trans h.mp, (e MN (by decide) (by decide)).trans h.mn,
    (e ZERO (by decide) (by decide)).trans h.zero, (e ONE (by decide) (by decide)).trans h.one,
    (e ONEP (by decide) (by decide)).trans h.onep, (e AP (by decide) (by decide)).trans h.ap,
    (e BM (by decide) (by decide)).trans h.bm, (e GX (by decide) (by decide)).trans h.gx,
    (e GY (by decide) (by decide)).trans h.gy, (e R2N (by decide) (by decide)).trans h.r2n,
    (e ONEN (by decide) (by decide)).trans h.onen, fun p hp => ?_⟩
  have := setupSaved_lt p hp
  refine (hu.word (d := p.2) (fun w hw => Or.inl ?_) (by omega_arith)).trans (h.saved p hp)
  rcases hW w hw with ⟨h1, -⟩ | h
  · rw [h1]; simp only [slot]; omega_arith
  · simp (disch := decide) only [sl_eq] at h; omega_arith

/-- A slot apart from the ranges of other numbered slots. -/
theorem apart_slW {l : List Nat} {i : Nat} (hi : i ∉ l)
    (hiA : i ≠ 54 ∧ i ≠ 61 ∧ i ≠ 82 := by first | decide | exact ⟨by omega_arith, by omega_arith⟩)
    (hl : ∀ j ∈ l, j ≠ 54 ∧ j ≠ 61 ∧ j ≠ 82 := by decide) :
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
  · exact Or.inl (by have := sl_below_bits c hi j 0 hT; omega_arith)

theorem apart_flag (h0 : 0 < c.n) {i : Nat} (hi : i ≠ FLAG) :
    ∀ w ∈ [(c.sl FLAG, 8)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  have := sl_apart c hi
  dsimp only
  omega_arith

theorem apart_append {W W' : List (Nat × Nat)} {x k : Nat}
    (h : ∀ w ∈ W, x + k ≤ w.1 ∨ w.1 + w.2 ≤ x) (h' : ∀ w ∈ W', x + k ≤ w.1 ∨ w.1 + w.2 ≤ x) :
    ∀ w ∈ W ++ W', x + k ≤ w.1 ∨ w.1 + w.2 ≤ x :=
  fun w hw => (List.mem_append.mp hw).elim (h w) (h' w)

/-- A number in a slot apart from what changed. -/
theorem sv_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (hu : Unch base W m m')
    (h7 : c.n < 10) (hn : base.toNat + size ≤ 2 ^ 64) {i : Nat} (hi : i < 45)
    (hW : ∀ w ∈ W, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i) :
    wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n :=
  hu.wordsVal hW (by have := sl_le c h7 hi; omega_arith)

/-- A byte of table `j` apart from what changed. -/
theorem tbl_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (hu : Unch base W m m')
    (h7 : c.n < 10) {j t : Nat} (hj : j < 3) (ht : t < 64 * c.n)
    (hW : ∀ w ∈ W, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t) :
    m' (off base (bitsAt c.n j + t)) = m (off base (bitsAt c.n j + t)) :=
  hu.byte hW (by have := bitsAt_le c h7 hj; have : size = 8192 := rfl; omega_arith)

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
  exact Or.inr (by dsimp only; omega_arith)

/-- Tables `j ≠ j'` are apart. -/
theorem tbl_apart_tbl {j j' t : Nat} (hjj : j ≠ j') (ht : t < 64 * c.n) :
    ∀ w ∈ [(bitsAt c.n j', 64 * c.n)], bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  simp only [bitsAt_eq]
  rcases Nat.lt_or_gt_of_ne hjj with h | h
  · have := Nat.mul_le_mul_left (64 * c.n) h
    rw [Nat.mul_succ] at this
    omega_arith
  · have := Nat.mul_le_mul_left (64 * c.n) h
    rw [Nat.mul_succ] at this
    omega_arith

/-- What a power writes: `ACC`, its table (and, for a function, where it
keeps registers) and the temporary area. -/
abbrev chainWc (c : Cfg) : List (Nat × Nat) :=
  [(c.sl ACC, 8 * c.n), (c.invTbl, 9 * (8 * c.n) + c.invSaveLen), (c.invTmp, 8 * c.n)]

theorem invW_cover {P : InvCfg} (ha : P.acc = c.sl ACC) (ht : P.tbl = c.invTbl) (hn : P.M.n = c.n)
    (hm : P.M.tmp = c.invTmp) : ∀ w ∈ invW P, ∃ w' ∈ chainWc c, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  intro w hw
  simp only [invW, ha, ht, hn, hm, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Nat.le_refl _, by dsimp only; omega_arith⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Nat.le_refl _,
      Nat.le_refl _⟩

theorem chainWN_cover (c : Cfg) :
    ∀ w ∈ chainW c.powN, ∃ w' ∈ chainWc c, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  intro w hw
  simp only [chainW, Cfg.powN, ChainCfg.ofExp, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Nat.le_refl _, by
      have : c.MN'.n = c.n := rfl
      dsimp only; omega_arith⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Nat.le_refl _,
      Nat.le_refl _⟩

theorem fixedOk_chainWc (hc : BaseCfgOk c) : FixedOk c (chainWc c) := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (show 12 < ACC by decide)))
  · exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_invTbl hc (show 12 < 45 by decide) (by decide)))
  · rcases hc.inv_at with h | h
    · have H : FixedOk c (slW c [TMP]) := fixedOk_slW (by simp)
      simpa only [slW, List.map_cons, List.map_nil, invTmp_none h] using H _ (List.mem_cons_self ..)
    · rcases h.2.2.2 with h' | h'
      · exact Or.inl ⟨h'.1, rfl⟩
      · have := sl_invTbl hc (show 12 < 45 by decide) (by decide)
        have := sl_lt c (i := 12) (j := nslots) (by decide) (by decide) (by decide)
        exact Or.inr (by rcases h'.1 with h'' | h'' <;> (dsimp only; omega_arith))

/-- A slot but `ACC` and `TMP` is apart from what a power writes. -/
theorem apart_chainWc (hc : BaseCfgOk c) {i : Nat} (hi : i < 45) (hl : i ∉ [ACC, TMP]) :
    ∀ w ∈ chainWc c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw hl
  rcases hw with rfl | rfl | rfl
  · exact sl_apart c hl.1
  · exact Or.inl (sl_invTbl hc hi hl.2)
  · exact sl_invTmp hc hi hl.2

/-- The flag survives a power and changes of other slots. -/
theorem flag_unch_cw (hc : BaseCfgOk c) {base : Addr} {l : List Nat} {m m' : Mem} (hu : Unch base (chainWc c ++ slW c l) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 64) (hl : FLAG ∉ l)
    (hlA : ∀ j ∈ l, j ≠ 54 ∧ j ≠ 61 ∧ j ≠ 82 := by decide) :
    word m' base (c.sl FLAG) = word m base (c.sl FLAG) := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine hu.word (fun w hw => ?_) (by omega_arith)
  rcases apart_append (apart_chainWc hc (i := FLAG) (by decide) (by decide)) (apart_slW hl (hl := hlA)) w hw
    with h | h
  · exact Or.inl (by omega_arith)
  · exact Or.inr h

/-- The flag survives a power. -/
theorem flag_unch_chain (hc : BaseCfgOk c) {base : Addr} {m m' : Mem} (hu : Unch base (chainWc c) m m') (h7 : c.n < 10)
    (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 64) :
    word m' base (c.sl FLAG) = word m base (c.sl FLAG) := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine hu.word (fun w hw => ?_) (by omega_arith)
  rcases apart_chainWc hc (i := FLAG) (by decide) (by decide) w hw with h | h
  · exact Or.inl (by omega_arith)
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
    hc.minv_n, hc.red_n, fun f m' h' => (hc.call_n f m' h').1⟩

/-- The powers' modulus, with their temporary area. -/
theorem modOkA_inv {M : Mod} (hc : BaseCfgOk c) {m : Nat} {base : Addr} {mem : Mem}
    (hM : ModOkA M size m mem base) (hmo : M.mo = c.sl MP ∨ M.mo = c.sl MN) (hn : M.n = c.n)
    (htmp : M.tmp = c.sl TMP) : ModOkA { M with tmp := c.invTmp } size m mem base := by
  refine ⟨hM.n0, hM.n10, hM.mo, by dsimp only; rw [hn]; exact invTmp_le hc, ?_, hM.val, hM.inv,
    hM.red, fun f m' e => ?_⟩
  · dsimp only; rw [hn]
    rcases hmo with e | e <;> rw [e]
    · exact sl_invTmp hc (by decide) (by decide)
    · exact sl_invTmp hc (by decide) (by decide)
  · have hT : c.invTmp = c.sl TMP → Mont.callOf M = some (f, m') := fun ht => by
      simp only [Mont.callOf, ht] at e ⊢
      rw [htmp]; exact e
    rcases hc.inv_at with h | h
    · exact hM.call f m' (hT (invTmp_none h))
    · rcases h.2.2.2 with h' | h'
      · have hn10 := hc.n10
        have ht : slot c.n TMP ≠ Mont.moAt c.n := by simp only [slot, TMP, Mont.moAt]; omega_arith
        simp only [Mont.callOf, hn, h'.1, ht, ite_false, reduceCtorEq] at e
      · simp only [Mont.callOf, hn, h'.2.2.2, ite_false, reduceCtorEq] at e

/-- `ACC = RZ^(p - 2)` (in Montgomery form), by divsteps, inline. -/
theorem pPowI_ok (hc : BaseCfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    (hM : ModOkA c.MP' size c.C.p s.mem base) (hB : wordsVal s.mem base (c.sl RZ) c.n < c.C.p) :
    WP isa c.pPowI s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (chainWc c) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl ACC) c.n < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
        toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl RZ) c.n) ^ (c.C.p - 2) := by
  have := hc.p_ge
  exact WP.mono (hc.sound_p (invLayP hc) (by omega_arith) (unitMod_pow_two hc.p_odd _) hs
      (modOkA_inv hc hM (.inl rfl) rfl rfl) hB hc.inv_p)
    fun s' ⟨K, U, lt, v⟩ => ⟨K, U.cover (invW_cover rfl rfl rfl rfl), lt, v⟩

/-- `ACC = KM^(n - 2)` (in Montgomery form), by divsteps or a chain, inline. -/
theorem nPowI_ok (hc : BaseCfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    (hM : ModOkA c.MN' size c.C.n s.mem base) (hB : wordsVal s.mem base (c.sl KM) c.n < c.C.n) :
    WP isa c.nPowI s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (chainWc c) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl ACC) c.n < c.C.n ∧
      toM c.C.n (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
        toM c.C.n (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl KM) c.n) ^ (c.C.n - 2) := by
  have := hc.n_ge
  have hM' := modOkA_inv hc hM (.inr rfl) rfl rfl
  rw [Cfg.nPowI]
  split
  · rename_i h
    exact WP.mono ((hc.inv_n h).1 (invLayN hc) (by omega_arith) (unitMod_pow_two hc.n_odd _) hs hM' hB
      (hc.inv_n h).2) fun s' ⟨K, U, lt, v⟩ => ⟨K, U.cover (invW_cover rfl rfl rfl rfl), lt, v⟩
  · rename_i h
    exact WP.mono (chainPow_ok (chainLayN hc) (unitMod_pow_two hc.n_odd _) hs hM' hB
      (chainOkN hc (by simpa using h))) fun s' ⟨K, U, lt, v⟩ => ⟨K, U.cover (chainWN_cover c), lt, v⟩

/-! ## The functions `vg_<curve>_inv_mod_p` and `_n` -/

theorem invSave_facts (hc : BaseCfgOk c) (hI : c.inverse ≠ none) :
    (c.invSave + c.invSaveLen ≤ c.invTmp ∨ c.invTmp + 8 * c.n ≤ c.invSave) ∧ c.invSave % 8 = 0 ∧
      c.invSave = c.invTbl + 9 * (8 * c.n) ∧ c.invSave + c.invSaveLen ≤ size := by
  rcases hc.inv_at with h | h
  · exact absurd h hI
  · have := h.2.1
    have := h.1
    have := h.2.2.1
    refine ⟨?_, by unfold Cfg.invSave; omega_arith, rfl, by unfold Cfg.invSave; omega_arith⟩
    rcases h.2.2.2 with h' | h'
    · exact Or.inr (by unfold Cfg.invSave; omega_arith)
    · rcases h'.1 with h'' | h''
      · exact Or.inl (by unfold Cfg.invSave; omega_arith)
      · exact Or.inr (by unfold Cfg.invSave; omega_arith)

/-- The words from `d` hold `g` of the registers `rs`, in order. -/
def SavedAt (m : Mem) (base : Addr) (g : Reg → BitVec 64) : Nat → List Reg → Prop
  | _, [] => True
  | d, r :: rs => word m base d = g r ∧ SavedAt m base g (d + 8) rs

theorem SavedAt.congr {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} :
    ∀ {d : Nat} {rs : List Reg}, SavedAt m base g d rs →
    (∀ e, d ≤ e → e + 8 ≤ d + 8 * rs.length → word m' base e = word m base e) → SavedAt m' base g d rs
  | _, [], _, _ => trivial
  | d, r :: rs, ⟨h₁, h₂⟩, hw => by
    refine ⟨(hw d (Nat.le_refl _) (by simp only [List.length_cons]; omega_arith)).trans h₁,
      SavedAt.congr h₂ fun e h₁ h₂ => hw e (by omega_arith) ?_⟩
    simp only [List.length_cons]; omega_arith

/-- Storing registers in consecutive words. -/
theorem stAll_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) :
    ∀ (rs : List Reg) {d : Nat}, d + 8 * rs.length ≤ size → d % 8 = 0 →
    WP isa (.block (stAll rs d)) s fun s' => KeepRegs [] s s' ∧ s'.gpr = s.gpr ∧
      Outside base d (8 * rs.length) s.mem s'.mem ∧ SavedAt s'.mem base s.gpr d rs
  | [], _, _, _ => WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl, Outside.refl _ _ _ _, trivial⟩
  | r :: rs, d, hd, h8 => by
    have hn := hs.nowrap
    simp only [List.length_cons] at hd
    rw [stAll, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (st_out hs (o := d) (by omega_arith) h8 r) fun s₁ ⟨m₁, k₁, g₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have O₁ : Outside base d 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega_arith)
    refine WP.mono (stAll_ok hs₁ rs (d := d + 8) (by omega_arith) (by omega_arith)) fun s₂ ⟨k₂, g₂, O₂, S₂⟩ => ?_
    refine ⟨k₁.trans k₂, g₂.trans g₁, fun x hx => ?_, ?_, ?_⟩
    · simp only [List.length_cons] at hx
      rw [O₂ x (by omega_arith), O₁ x (by omega_arith)]
    · rw [O₂.word (by omega_arith) (by omega_arith), m₁, word_writeW_self]
    · rw [← g₁]; exact S₂

/-- Loading registers from consecutive words. -/
theorem ldAll_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) :
    ∀ (rs : List Reg) {d : Nat}, d + 8 * rs.length ≤ size → d % 8 = 0 → (∀ r ∈ rs, r ≠ .x0) →
    WP isa (.block (ldAll rs d)) s fun s' => KeepRegs rs s s' ∧ s'.mem = s.mem ∧
      ∀ g, SavedAt s.mem base g d rs → ∀ r ∈ rs, s'.gpr r = g r
  | [], _, _, _, _ => WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl, fun _ _ _ h => nomatch h⟩
  | r :: rs, d, hd, h8, h0 => by
    simp only [List.length_cons] at hd
    rw [ldAll, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ld_ok hs (d := d) (by omega_arith) h8 r) fun s₁ ⟨l₁, k₁, _⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by simpa using (h0 r List.mem_cons_self).symm)
    refine WP.mono (ldAll_ok hs₁ rs (d := d + 8) (by omega_arith) (by omega_arith)
      fun r' hr' => h0 r' (List.mem_cons_of_mem _ hr')) fun s₂ ⟨K₂, m₂, V₂⟩ => ?_
    refine ⟨((Keeps.regs k₁).mono (by simp)).trans (K₂.mono (by simp_all)), m₂.trans k₁.mem,
      fun g ⟨w, S⟩ r' hr' => ?_⟩
    by_cases hm : r' ∈ rs
    · exact V₂ g (by rw [k₁.mem]; exact S) r' hm
    · obtain rfl : r' = r := by simpa [hm] using hr'
      rw [K₂.gpr _ hm, l₁, w]

theorem invKept_ne_x0 (c : Cfg) : ∀ r ∈ c.invKept, r ≠ .x0 := by
  unfold Cfg.invKept Cfg.invRegs
  split <;> decide

/-- The registers a function changes: `clob`'s, but those it keeps. -/
def invClob (c : Cfg) : List Reg := (clob c.n).filter fun r => r ∉ c.invKept

/-- A power `body` between saving `invKept` past its working slots and
restoring them: the function keeps them, and writes no more than `chainWc`. -/
theorem invFn_ok (hc : BaseCfgOk c) (hI : c.inverse ≠ none) {body : Prog isa} {s : State}
    {base : Addr} (hs : Scr s base size) {R : Mem → Mem → Prop}
    (hb : ∀ t, Scr t base size → Unch base [(c.invSave, c.invSaveLen)] s.mem t.mem →
      WP isa body t fun t' =>
      KeepRegs (powClob c.n) t t' ∧ Unch base (chainWc c) t.mem t'.mem ∧
      (∀ e, c.invSave ≤ e → e + 8 ≤ c.invSave + c.invSaveLen → word t'.mem base e = word t.mem base e) ∧
      R s.mem t'.mem) :
    WP isa (c.invFn body) s fun s' => KeepRegs (invClob c) s s' ∧
      Unch base (chainWc c) s.mem s'.mem ∧ R s.mem s'.mem := by
  obtain ⟨-, hsv8, hsv3, hsv⟩ := invSave_facts hc hI
  have hl : c.invSaveLen = 8 * c.invKept.length := rfl
  rw [Cfg.invFn]
  refine WP.seq (WP.mono (stAll_ok hs c.invKept (d := c.invSave) (by omega_arith) hsv8)
    fun s₁ ⟨k₁, g₁, O₁, S₁⟩ => ?_)
  have hs₁ : Scr s₁ base size := hs.of_keepRegs k₁ (by decide)
  have U₁ : Unch base [(c.invSave, c.invSaveLen)] s.mem s₁.mem := by rw [hl]; exact O₁.unch
  refine WP.seq (WP.mono (hb s₁ hs₁ U₁) fun s₂ ⟨K₂, U₂, w₂, R₂⟩ => ?_)
  have hs₂ := hs₁.of_keepRegs K₂ (by simp [powClob, x0_not_clob])
  have S₂ : SavedAt s₂.mem base s.gpr c.invSave c.invKept :=
    SavedAt.congr S₁ fun e h₁ h₂ => w₂ e h₁ (by omega_arith)
  refine WP.mono (ldAll_ok hs₂ c.invKept (d := c.invSave) (by omega_arith) hsv8 (invKept_ne_x0 c))
    fun s₃ ⟨K₃, m₃, V₃⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [K₃.rd, K₂.rd, k₁.rd], by rw [K₃.wr, K₂.wr, k₁.wr],
    by rw [K₃.sp, K₂.sp, k₁.sp]⟩, ?_, by rw [m₃]; exact R₂⟩
  · by_cases hk : r ∈ c.invKept
    · exact V₃ s.gpr S₂ r hk
    · have h19 : r ≠ .x19 := fun e => hk (e ▸ List.mem_cons_self)
      have hcl : r ∉ clob c.n := fun h => hr (List.mem_filter.mpr ⟨h, by simpa using hk⟩)
      rw [K₃.gpr _ hk, K₂.gpr _ (by simp [powClob, h19, hcl]), k₁.gpr _ (by simp)]
  · rw [m₃]
    refine (U₁.trans U₂).cover fun w hw => ?_
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with rfl | hw
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by omega_arith, by dsimp only; omega_arith⟩
    · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩

/-- `x30` into lane 0 of `v29`. -/
theorem keepLr_ok (s : State) :
    WP isa (.block [.vop (.ins .d2 .v29 0 .x30)]) s fun s₁ =>
      KeepRegs [] s s₁ ∧ s₁.mem = s.mem ∧ (s₁.v .v29).extractLsb' 0 64 = s.gpr .x30 := by
  apply WP.of_runBlock
  simp only [runBlock_cons, Mont.exec_ins (show 0 < 2 by decide), runStep_some, runBlock_nil,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r _ => by simp [RegUpd.gpr_setV], rfl, rfl, rfl⟩, rfl, ?_⟩
  simp only [RegUpd.v_setV_self]
  have := Mont.extract_setLane (s.v .v29) (s.gpr .x30) (i := 0) (j := 0) (by decide) (by decide)
  simpa using this

/-- What the call of an inversion's function needs and gives, from its
caller's state `s₀`: the working space, and the memory unchanged. -/
def invK (c : Cfg) (base : Addr) (mem : Mem) (R : Mem → Mem → Prop) : Contract isa where
  pre t := Scr t base size ∧ t.mem = mem
  post t t' := KeepRegs (invClob c) t t' ∧ Unch base (chainWc c) t.mem t'.mem ∧ t'.v = t.v ∧
    R t.mem t'.mem
  pub _ _ := True

/-- A call of the function `name`, whose code `c.invFn body` gives `R` and
keeps `invKept`: as `body` inline, keeping `x30` and `x19`. -/
theorem invCall_ok {name : String} {body : Prog isa} {s : State} {base : Addr}
    (hs : Scr s base size) {R : Mem → Mem → Prop}
    (hfn : ∀ t, Scr t base size → t.mem = s.mem → WP isa (c.invFn body) t fun t' =>
      KeepRegs (invClob c) t t' ∧ Unch base (chainWc c) t.mem t'.mem ∧ R t.mem t'.mem)
    (hpres : ∀ r ∈ preserved, r ∉ clob c.n ∨ r ∈ c.invKept)
    (hv : (c.invFn body).allInstrs (fun i => (vdstOf i).isNone) = true)
    (hnf : (c.invFn body).noFrames = true) :
    WP isa (Cfg.invCall name (c.invFn body)) s fun s' => KeepRegs (powClob c.n) s s' ∧
      Unch base (chainWc c) s.mem s'.mem ∧ R s.mem s'.mem := by
  have hnv : ∀ (r : VReg), ∀ i ∈ instrs (c.invFn body), vdstOf i ≠ some r := by
    intro r i hi e
    have := List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ hv) i hi
    rw [e] at this; cases this
  rw [Cfg.invCall]
  refine WP.seq (WP.mono (keepLr_ok s) fun s₁ ⟨k₁, m₁, l₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have hcov : Covers [⟨base, size⟩] s₁.wr := Covers.one ⟨_, hs₁.wr, by
    have := hs.contains (d := 0) (n := size) (by omega_arith) (by decide)
    simpa [off] using this⟩
  refine WP.seq (WP.callV (k := invK c base s.mem R)
    (fun t ⟨ht, hm⟩ => by
      obtain ⟨tr, t', he, K, U, Rr⟩ := hfn t ht hm
      exact ⟨tr, t', he, ⟨fun r hr => K.gpr r fun h => (List.mem_filter.mp h).elim fun h₁ h₂ =>
          (hpres r hr).elim (· h₁) (by simpa using h₂), K.sp, Exec.preservedV he (by
        rw [Code.allInstrs_eq]; exact List.all_eq_true.mpr fun i hi => by
          unfold keepsV
          cases h : vdstOf i with
          | none => rfl
          | some r => exact absurd h (hnv r i hi))⟩, K, U, funext fun r => Exec.vec (hnv r) he, Rr⟩)
    (rd := []) (wr := [⟨base, size⟩]) ⟨⟨by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), hs₁.x0], by simp,
        hs.nowrap, hs.enc⟩, by rw [State.withRegions_mem, State.callEntry_mem, m₁]⟩
      (Covers.right hcov) hcov ?_ hnf)
  intro s₂ r₂ w₂ p₂ _ _ _ _ ⟨K, U, V, Rr⟩
  simp only [State.withRegions_mem, State.callEntry_mem] at U Rr
  rw [m₁] at U Rr
  have V' : s₂.v = s₁.v := V
  refine WP.mono (Mont.lr_ok s₂) fun s₃ ⟨l₃, k₃⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [k₃.rd, r₂, k₁.rd], by rw [k₃.wr, w₂, k₁.wr], by rw [k₃.sp, p₂, k₁.sp]⟩,
    by rw [k₃.mem]; exact U, by rw [k₃.mem]; exact Rr⟩
  by_cases h30 : r = .x30
  · subst h30; rw [l₃, V', l₁]
  · simp only [powClob, List.mem_cons, not_or] at hr
    have h16 : Reg.x16 ∈ clob c.n := by simp [clob]
    have h17 : Reg.x17 ∈ clob c.n := by simp [clob]
    refine (k₃.gpr _ (by simpa using h30)).trans ((K.gpr r fun h => hr.2 (List.mem_filter.mp h).1).trans ?_)
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by
      simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun e => hr.2 (e ▸ h16), fun e => hr.2 (e ▸ h17), h30⟩), k₁.gpr _ (by simp)]

/-- Where a function keeps `x19` is apart from what its power writes. -/
theorem invSave_apart (hc : BaseCfgOk c) (hI : c.inverse ≠ none) {P : InvCfg} (ha : P.acc = c.sl ACC)
    (ht : P.tbl = c.invTbl) (hn : P.M.n = c.n) (hm : P.M.tmp = c.invTmp) :
    ∀ w ∈ invW P, c.invSave + c.invSaveLen ≤ w.1 ∨ w.1 + w.2 ≤ c.invSave := by
  obtain ⟨h1, -, h3, -⟩ := invSave_facts hc hI
  have := sl_invTbl hc (i := ACC) (by decide) (by decide)
  intro w hw
  simp only [invW, ha, ht, hn, hm, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact Or.inr (by dsimp only; omega_arith)
  · exact Or.inr (by dsimp only; omega_arith)
  · dsimp only; omega_arith

/-- A slot below the tables, but `TMP`, is apart from where a function keeps registers. -/
theorem sl_invSave (hc : BaseCfgOk c) (hI : c.inverse ≠ none) {i : Nat} (hi : i < 45) (hT : i ≠ TMP) :
    ∀ w ∈ [(c.invSave, c.invSaveLen)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  obtain ⟨-, -, h3, -⟩ := invSave_facts hc hI
  have := sl_invTbl hc hi hT
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inl (by dsimp only; omega_arith)

/-- What an inversion's function needs of its body: run from a state whose
memory differs from `s`'s only where the function keeps registers. -/
theorem invBody_ok (hc : BaseCfgOk c) (hI : c.inverse ≠ none) {P : InvCfg} {m b jm : Nat} [NeZero m]
    (hS : InvSound m) (hL : InvLay P size) (hOk : InvOk P m) (hm2 : 2 < m)
    (hR : UnitMod m (2 ^ (64 * c.n))) (ha : P.acc = c.sl ACC) (ht : P.tbl = c.invTbl) (hn : P.M.n = c.n)
    (htmp : P.M.tmp = c.invTmp) (hb : P.base = c.sl b) (hb45 : b < 45) (hbT : b ≠ TMP)
    (hmo : P.M.mo = c.sl jm) (hjm : jm < 45) (hjT : jm ≠ TMP) {s : State} {base : Addr}
    (hs : Scr s base size) (hM : ModOkA P.M size m s.mem base) (hB : wordsVal s.mem base P.base c.n < m)
    {t : State} (ht' : Scr t base size) (hU : Unch base [(c.invSave, c.invSaveLen)] s.mem t.mem) :
    WP isa (InvCfg.inv P) t fun t' =>
      KeepRegs (powClob c.n) t t' ∧ Unch base (chainWc c) t.mem t'.mem ∧
      (∀ e, c.invSave ≤ e → e + 8 ≤ c.invSave + c.invSaveLen →
        word t'.mem base e = word t.mem base e) ∧
      (wordsVal t'.mem base (c.sl ACC) c.n < m ∧
        toM m (2 ^ (64 * c.n)) (wordsVal t'.mem base (c.sl ACC) c.n) =
          toM m (2 ^ (64 * c.n)) (wordsVal s.mem base P.base c.n) ^ (m - 2)) := by
  have hnw := hs.nowrap
  have hle := sl_le c hc.n10 hb45
  have hMt : ModOkA P.M size m t.mem base := hM.unch hU (by
    rw [hmo, hn]; exact sl_invSave hc hI hjm hjT) hnw
  have eB : wordsVal t.mem base P.base c.n = wordsVal s.mem base P.base c.n := by
    rw [hb]; exact hU.wordsVal (sl_invSave hc hI hb45 hbT) (by omega_arith)
  have hn' := hn
  refine WP.mono (hS hL hm2 (by rw [hn]; exact hR) ht' hMt (by rw [hn, eB]; exact hB) hOk)
    fun t' ⟨K, U, lt, v⟩ => ?_
  rw [hn] at K
  rw [hn, ha] at lt
  rw [hn, ha, eB] at v
  obtain ⟨-, -, -, h4⟩ := invSave_facts hc hI
  refine ⟨K, U.cover (invW_cover ha ht hn htmp), fun e h₁ h₂ => U.word (fun w hw => by
    rcases invSave_apart hc hI ha ht hn htmp w hw with h | h
    · exact Or.inl (by omega_arith)
    · exact Or.inr (by omega_arith)) (by omega_arith), lt, v⟩

/-- `ACC = RZ^(p - 2)` (in Montgomery form), by divsteps: inline, or a call
of `vg_<curve>_inv_mod_p`. -/
theorem pPow_ok (hc : BaseCfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    (hM : ModOkA c.MP' size c.C.p s.mem base) (hB : wordsVal s.mem base (c.sl RZ) c.n < c.C.p) :
    WP isa c.pPow s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (chainWc c) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl ACC) c.n < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
        toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl RZ) c.n) ^ (c.C.p - 2) := by
  have := hc.p_ge
  unfold Cfg.pPow
  split
  · rename_i C hC
    have hI : c.inverse ≠ none := by rw [hC]; exact Option.some_ne_none _
    obtain ⟨hpres, hvp, -, hfp, -⟩ := hc.inv_fn hI
    have hM' := modOkA_inv hc hM (.inl rfl) rfl rfl
    exact invCall_ok hs (R := fun m m' => wordsVal m' base (c.sl ACC) c.n < c.C.p ∧
        toM c.C.p (2 ^ (64 * c.n)) (wordsVal m' base (c.sl ACC) c.n) =
          toM c.C.p (2 ^ (64 * c.n)) (wordsVal m base (c.sl RZ) c.n) ^ (c.C.p - 2))
      (fun t ht hm => WP.mono (invFn_ok hc hI ht (R := fun _ m' => wordsVal m' base (c.sl ACC) c.n < c.C.p ∧
          toM c.C.p (2 ^ (64 * c.n)) (wordsVal m' base (c.sl ACC) c.n) =
            toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl RZ) c.n) ^ (c.C.p - 2)) (fun u hu hU =>
        invBody_ok hc hI hc.sound_p (invLayP hc) hc.inv_p (by omega_arith) (unitMod_pow_two hc.p_odd _)
          rfl rfl rfl rfl (b := RZ) rfl (by decide) (by decide) (jm := MP) rfl (by decide) (by decide) hs hM' hB hu
          (by rw [hm] at hU; exact hU)))
      fun t' ⟨K, U, R⟩ => ⟨K, U, by rw [hm]; exact R⟩) hpres hvp hfp
  · exact pPowI_ok hc hs hM hB

/-- `ACC = KM^(n - 2)` (in Montgomery form), by divsteps or a chain: inline,
or a call of `vg_<curve>_inv_mod_n`. -/
theorem nPow_ok (hc : BaseCfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    (hM : ModOkA c.MN' size c.C.n s.mem base) (hB : wordsVal s.mem base (c.sl KM) c.n < c.C.n) :
    WP isa c.nPow s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (chainWc c) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl ACC) c.n < c.C.n ∧
      toM c.C.n (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
        toM c.C.n (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl KM) c.n) ^ (c.C.n - 2) := by
  have := hc.n_ge
  unfold Cfg.nPow
  split
  · rename_i C hC
    have hI : c.inverse ≠ none := by rw [hC]; exact Option.some_ne_none _
    obtain ⟨hpres, -, hvn, -, hfn⟩ := hc.inv_fn hI
    have hM' := modOkA_inv hc hM (.inr rfl) rfl rfl
    refine invCall_ok hs (R := fun m m' => wordsVal m' base (c.sl ACC) c.n < c.C.n ∧
        toM c.C.n (2 ^ (64 * c.n)) (wordsVal m' base (c.sl ACC) c.n) =
          toM c.C.n (2 ^ (64 * c.n)) (wordsVal m base (c.sl KM) c.n) ^ (c.C.n - 2))
      (fun t ht hm => WP.mono (invFn_ok hc hI ht (R := fun _ m' => wordsVal m' base (c.sl ACC) c.n < c.C.n ∧
          toM c.C.n (2 ^ (64 * c.n)) (wordsVal m' base (c.sl ACC) c.n) =
            toM c.C.n (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl KM) c.n) ^ (c.C.n - 2)) (fun u hu hU => ?_))
      fun t' ⟨K, U, R⟩ => ⟨K, U, by rw [hm]; exact R⟩) hpres hvn hfn
    rw [hm] at hU
    rw [Cfg.nPowI]
    split
    · rename_i h
      exact invBody_ok hc hI (hc.inv_n h).1 (invLayN hc) (hc.inv_n h).2 (by omega_arith)
        (unitMod_pow_two hc.n_odd _) rfl rfl rfl rfl (b := KM) rfl (by decide) (by decide) (jm := MN) rfl
        (by decide) (by decide) hs hM' hB hu hU
    · rename_i h
      have hnw := hs.nowrap
      have hMt := hM'.unch hU (sl_invSave hc hI (i := MN) (by decide) (by decide)) hnw
      have eB : wordsVal u.mem base (c.sl KM) c.n = wordsVal s.mem base (c.sl KM) c.n :=
        hU.wordsVal (sl_invSave hc hI (i := KM) (by decide) (by decide))
          (by have := sl_le c hc.n10 (i := KM) (by decide); omega_arith)
      refine WP.mono (chainPow_ok (chainLayN hc) (unitMod_pow_two hc.n_odd _) hu hMt
        (show wordsVal u.mem base (c.sl KM) c.n < c.C.n by rw [eB]; exact hB)
        (chainOkN hc (by simpa using h))) fun t' ⟨K, U, lt, v⟩ => ⟨K, U.cover (chainWN_cover c),
          fun e he₁ he₂ => U.word (by
            obtain ⟨h1, -, h3, -⟩ := invSave_facts hc hI
            have := sl_invTbl hc (i := ACC) (by decide) (by decide)
            intro w hw
            simp only [chainW, Cfg.powN, ChainCfg.ofExp, List.mem_cons, List.not_mem_nil, or_false] at hw
            have : c.MN'.n = c.n := rfl
            rcases hw with rfl | rfl | rfl
            · exact Or.inr (by dsimp only; omega_arith)
            · exact Or.inr (by dsimp only; omega_arith)
            · dsimp only; omega_arith)
            (by obtain ⟨-, -, -, h4⟩ := invSave_facts hc hI; omega_arith),
          lt, by
            have v' : toM c.C.n (2 ^ (64 * c.n)) (wordsVal t'.mem base (c.sl ACC) c.n) =
                toM c.C.n (2 ^ (64 * c.n)) (wordsVal u.mem base (c.sl KM) c.n) ^ (c.C.n - 2) := v
            rw [v', eB]⟩
  · exact nPowI_ok hc hs hM hB

theorem x20_not_clob {n : Nat} (h : n < 10) : Reg.x20 ∉ clob n := by
  have : ∀ n < 10, Reg.x20 ∉ clob n := by decide
  exact this n h

theorem x20_not_powClob {n : Nat} (h : n < 10) : Reg.x20 ∉ powClob n := by
  intro h'
  rcases List.mem_cons.mp h' with h' | h'
  · exact absurd h' (by decide)
  · exact x20_not_clob h h'

end VG.Proof.Ecdsa.AArch64
