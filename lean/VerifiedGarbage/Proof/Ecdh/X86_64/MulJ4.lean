module

public import VerifiedGarbage.Proof.Ecdh.X86_64.MulOk
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJNorm
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJLoop
import VerifiedGarbage.Proof.Ecdsa.X86_64.Fixed
import VerifiedGarbage.Proof.Ecdh.X86_64.Window
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Weierstrass.WindowJ

/-!
# ECDH on x86-64: `[d]P` by 4-bit windows with a Jacobian accumulator

`Cfg.mulQJ4`, for a curve of prime order whose order `n` is above the
multiples of every iteration but the last (`winE_two_bound`): `winMulJ_ok`
recodes `d` and runs `WinCfg.windowJ` (`windowJ_ok`), as `winMul_ok` runs
the window method, and `mulQJ4_ok` is it with `d` reduced first and the
power after it, as `mulPow_ok`'s windows. Its table's inversion
(`Cfg.invWin`, `invSpecQ`) writes `E.x`, the temporary area and a
working area over the table of the bits of `n - 2`, so it writes what `mulQ`
writes and that area (`mulQJ4W`, `winXJ`).
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open VG.Impl.Ecdh.X86_64 (PX PY BP)

variable {c : Cfg}

/-! ## The table's inversion -/

/-- `winX`, and the working area of the inversion of the window method in
Jacobian coordinates (`invWin`, over the table of the bits of `n - 2`). -/
def winXJ (c : Cfg) : List (Nat × Nat) := winX c ++ [(bitsAt c.n 2, invTbl c.n)]

theorem fixedOk_winXJ : FixedOk c (winXJ c) :=
  fixedOk_winX.append fun w hw => by
    rw [List.mem_singleton.mp hw]
    exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_bits c (show 12 < 45 by decide) 2 0))

/-- For six words, the inversion's working area ends below the temporary area. -/
theorem invW_below_tmp (h6 : c.n = 6) : bitsAt c.n 2 + invTbl c.n ≤ c.sl TMP := by
  rw [sl_tmp6 c h6, bitsAt_eq, h6]; decide

theorem apart_winXJ {i : Nat} (hi : i < 45) :
    ∀ w ∈ winXJ c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_winX hi) fun w hw => by
    rw [List.mem_singleton.mp hw]
    exact sl_apart_hi c hi (Nat.le_refl _) invW_below_tmp

theorem tbl_apart_winXJ {j t : Nat} (hj : j < 2) (ht : t < 64 * c.n) :
    ∀ w ∈ winXJ c, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t :=
  apart_append (tbl_apart_winX (by omega_arith) ht) fun w hw => by
    rw [List.mem_singleton.mp hw]
    refine Or.inl ?_
    dsimp only
    rw [bitsAt_eq, bitsAt_eq]
    have := Nat.mul_le_mul_left (64 * c.n + 8) (show j + 1 ≤ 2 by omega_arith)
    rw [Nat.mul_succ] at this
    omega_arith


/-- What `mulQJ4` and the power may write: what `mulQ` and the power may,
and the inversion's working area (`winXJ`). -/
abbrev mulQJ4W (c : Cfg) : List (Nat × Nat) := winXJ c ++ slW c mulI ++ pwW c

/-- `WinMulPost` for the window method in Jacobian coordinates, which also
runs an inversion (`invClob`, `winXJ`). -/
structure WinMulPostJ (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (invClob c.n) s s'
  unch : Unch base (winXJ c ++ slW c (otherI ++ tblI ++ [TMP]) ++ pwW c) s.mem s'.mem
  mod : ModOkW c.MP' size c.C.p s'.mem base
  lt : ∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p
  q : Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
    (tmv c.C c.n base s' (c.sl RZ)) (mul k P)

/-- The inversion of the window method in Jacobian coordinates: its slots
and working area (over the table of the bits of `n - 2`). -/
theorem invLayW (hc : CfgOk c) (h9 : c.n ≤ 9) (h4 : 4 ≤ c.n) :
    InvLay (Impl.Ecdh.X86_64.Cfg.invWin c) size := by
  have h7 := hc.n10
  have hT : bitsAt c.n 2 + invTbl c.n ≤ size := by
    simp only [bitsAt_eq, invTbl]; show _ ≤ 8192
    have : 8 * c.n * 45 ≤ 8 * 9 * 45 := Nat.mul_le_mul_right _ (by omega_arith)
    omega_arith
  have below : ∀ {i}, i < 45 → i ≠ TMP → c.sl i + 8 * c.n ≤ bitsAt c.n 2 := fun hi hT => by
    have := sl_below_bits c hi 2 0 (.inl hT); omega_arith
  exact ⟨h4, show c.n < 10 by omega_arith, sl_le c h7 (i := TX) (by decide), sl_le c h7 (i := RZ) (by decide), hT,
    sl_le c h7 (i := MP) (by decide), sl_le c h7 (i := TMP) (by decide), sl_apart c (by decide),
    Or.inl (below (by decide) (by decide)), Or.inl (below (by decide) (by decide)), sl_apart c (by decide),
    (sl_apart_hi c (i := TMP) (by decide) (Nat.le_refl _) invW_below_tmp).symm, sl_apart c (by decide),
    Or.inl (below (by decide) (by decide)),
    sl_apart c (by decide)⟩

/-- The inversion of the window method in Jacobian coordinates, as the
window method takes it: `E.x = R.z^(p-2)`, writing `E.x`, the temporary area
and a working area apart from the window's slots and table of bits. -/
theorem invSpecQ (hc : CfgOk c) (h9 : c.n ≤ 9) {base : Addr} :
    InvSpecW (winQ c) c.C base size (InvCfg.inv (Impl.Ecdh.X86_64.Cfg.invWin c))
      (invW (Impl.Ecdh.X86_64.Cfg.invWin c)) := by
  obtain ⟨h4, sp, ip⟩ := hc.inv h9
  have h7 := hc.n10
  refine ⟨fun t ht hM hz => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · exact WP.mono (sp (invLayW hc h9 h4) (by have := hc.p_ge; omega_arith) (unitMod_pow_two hc.p_odd (64 * c.n))
      ht hM.of_inl hz ⟨ip.B1, ip.B16, ip.C, ip.Cpos, ip.Cn, ip.bound⟩ trivial) fun t' ⟨a, b, d, e⟩ => ⟨a, b, d, e⟩
  · simp only [invW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact Or.inl rfl
    · refine Or.inr (Or.inr ⟨Or.inl (show c.sl MP + 8 * c.n ≤ bitsAt c.n 2 by
        have := sl_below_bits c (i := MP) (by decide) 2 0; omega_arith), fun x hx => ?_⟩)
      rw [winSlots_eq] at hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have key : ∀ i ∈ roI ++ otherI ++ tblI, i < 45 ∨ 84 ≤ i := by decide
      rcases key i hi with h | h
      · exact sl_apart_hi c h (Nat.le_refl _) invW_below_tmp
      · refine Or.inr ?_
        show bitsAt c.n 2 + invTbl c.n ≤ c.sl i
        rw [bitsAt_eq]; simp (disch := sl_ne) only [sl_eq]; simp only [invTbl]
        have := Nat.mul_le_mul_left (8 * c.n) h
        omega_arith
    · exact Or.inr (Or.inl rfl)
  · simp only [invW, List.mem_cons, List.not_mem_nil, or_false] at hw
    have hb : (winQ c).bits = c.sl WB := rfl
    rw [hb]
    rcases hw with rfl | rfl | rfl
    · exact Or.inr (sl_lt c (show TX < WB by decide))
    · refine Or.inr ?_
      show bitsAt c.n 2 + invTbl c.n ≤ c.sl WB
      rw [bitsAt_eq]; simp (disch := sl_ne) only [sl_eq]; simp only [invTbl]; unfold WB
      omega_arith
    · by_cases h6 : c.n = 6
      · refine Or.inl ?_
        show c.sl WB + 4 * c.winJ ≤ c.sl TMP
        have hJle : c.winJ ≤ 16 * c.n + 1 := by
          unfold Cfg.winJ; have := hc.len_hi; have := hc.nbits_le; omega_arith
        rw [sl_tmp6 c h6]; simp (disch := sl_ne) only [sl_eq]; unfold WB
        omega_arith
      · exact Or.inr (sl_lt c (show TMP < WB by decide) (.inr (.inr ⟨h6, by decide⟩)))

/-! ## The table's inversion by a call -/

/-- Words that read the same, as numbers, are the same. -/
theorem word_eq_of_wordsVal {m m' : Mem} {base : Addr} : ∀ {d k : Nat},
    wordsVal m base d k = wordsVal m' base d k → ∀ j < k, word m base (d + 8 * j) = word m' base (d + 8 * j)
  | _, 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | d, k + 1, h, j, hj => by
    simp only [wordsVal] at h
    obtain ha := (word m base d).isLt
    obtain hb := (word m' base d).isLt
    obtain e1 : (word m base d).toNat = (word m' base d).toNat := by omega_arith
    obtain e2 : wordsVal m base (d + 8) k = wordsVal m' base (d + 8) k := by omega_arith
    rcases j with _ | j
    · exact BitVec.eq_of_toNat_eq e1
    · have := word_eq_of_wordsVal e2 j (by omega_arith)
      rwa [show d + 8 + 8 * j = d + 8 * (j + 1) by omega_arith] at this

/-- Bytes whose word reads the same are the same. -/
theorem byte_of_word {m m' : Mem} {base : Addr} {d : Nat} (h : word m base d = word m' base d)
    {j : Nat} (hj : j < 8) : m (off base d + BitVec.ofNat 64 j) = m' (off base d + BitVec.ofNat 64 j) := by
  obtain e := congrArg (fun v : BitVec 64 => v.extractLsb' (8 * j) 8) h
  change ((m.read (off base d) 8).setWidth 64).extractLsb' (8 * j) 8 =
    ((m'.read (off base d) 8).setWidth 64).extractLsb' (8 * j) 8 at e
  rw [BitVec.setWidth_eq, BitVec.setWidth_eq, Mem.extractLsb'_read _ _ hj, Mem.extractLsb'_read _ _ hj] at e
  exact e

/-- The bytes of words that read the same, as a number, are the same. -/
theorem byte_of_wordsVal {m m' : Mem} {base : Addr} {d k : Nat}
    (h : wordsVal m base d k = wordsVal m' base d k) {x : Addr} (hx : d ≤ ofs base x)
    (hx' : ofs base x < d + 8 * k) : m x = m' x := by
  obtain ⟨j, hj, i, hi, rfl⟩ : ∃ j < k, ∃ i < 8, x = off base (d + 8 * j) + BitVec.ofNat 64 i := by
    refine ⟨(ofs base x - d) / 8, by omega_arith, (ofs base x - d) % 8, Nat.mod_lt _ (by decide), ?_⟩
    rw [off, Offset.add_add, show d + 8 * ((ofs base x - d) / 8) + (ofs base x - d) % 8 = ofs base x by omega_arith,
      BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  exact byte_of_word (word_eq_of_wordsVal h j hj) hi

/-- What the call writes, but for the bytes it keeps: `TX`, the table of the
bits of `n - 2`, the temporary area, `ACC`, and the function's working area
below the window's table of bits. -/
def invWinCallW (c : Cfg) : List (Nat × Nat) :=
  [(c.sl TX, 8 * c.n), (bitsAt c.n 2, invTbl c.n), (c.sl TMP, 8 * c.n), (c.sl ACC, 8 * c.n),
    (bitsAt c.n 3, c.sl WB - bitsAt c.n 3)]

/-- The places, for nine words. -/
theorem callLay9 (h9 : c.n = 9) :
    c.sl WB = 5320 ∧ bitsAt c.n 2 = 4472 ∧ bitsAt c.n 3 = 5056 ∧
    Impl.Ecdh.X86_64.Cfg.invJAWords c = 47 ∧ Impl.Ecdh.X86_64.Cfg.invJAPt c = 4848 ∧
    c.sl PT = 2224 ∧ c.sl ACC = 2152 ∧ c.sl RZ = 1216 ∧ c.sl TX = 1504 ∧ c.sl TMP = 4024 ∧
    c.sl MP = 64 ∧ invTbl c.n = 640 ∧ (∀ i, i ≠ TMP → i ≠ 55 → i ≠ 83 → c.sl i = 64 + 72 * i) := by
  obtain hs : ∀ i, i ≠ TMP → i ≠ 55 → i ≠ 83 → c.sl i = 64 + 72 * i := fun i h1 h2 h3 => by
    rw [sl_eq c i ⟨h1, h2, h3⟩, h9]
  refine ⟨hs _ (by decide) (by decide) (by decide), by rw [bitsAt_eq, h9], by rw [bitsAt_eq, h9], ?_, ?_,
    hs _ (by decide) (by decide) (by decide), hs _ (by decide) (by decide) (by decide),
    hs _ (by decide) (by decide) (by decide), hs _ (by decide) (by decide) (by decide),
    by rw [sl_eq', ix, ite_eq_left_of_eq_true _ _ (eq_true h9), h9]; rfl, hs _ (by decide) (by decide) (by decide),
    by simp only [invTbl, h9], hs⟩
  · unfold Impl.Ecdh.X86_64.Cfg.invJAWords
    rw [hs _ (by decide) (by decide) (by decide), bitsAt_eq, h9]; rfl
  · unfold Impl.Ecdh.X86_64.Cfg.invJAPt Impl.Ecdh.X86_64.Cfg.invJAWords
    rw [hs _ (by decide) (by decide) (by decide), bitsAt_eq, bitsAt_eq, h9]; rfl

/-- The inversion by a call, for nine words: `TX = R.z^(p-2)`, writing
`invWinCallW`. -/
theorem invSpecQCall (hc : CfgOk c) (h9 : c.n = 9) (hi : c.inverse ≠ none) {base : Addr} :
    InvSpecW (winQ c) c.C base size (Impl.Ecdh.X86_64.Cfg.invCallTo c (c.sl TX)) (invWinCallW c) := by
  obtain ⟨eWB, eB2, eB3, eW, ePt, ePT, eACC, eRZ, eTX, eTMP, eMP, eT, hs⟩ := callLay9 h9
  have hb : (winQ c).bits = c.sl WB := rfl
  have hJ : (winQ c).J = c.winJ := rfl
  obtain hJle : c.winJ ≤ 16 * c.n + 1 := by
    unfold Cfg.winJ; have := hc.len_hi; have := hc.nbits_le; omega_arith
  have hsz : size = 8192 := rfl
  obtain hn9 : 8 * c.n = 72 := by rw [h9]
  have hMn : (winQ c).M.n = c.n := rfl
  have hMmo : (winQ c).M.mo = c.sl MP := rfl
  have hMtmp : (winQ c).M.tmp = c.sl TMP := rfl
  have hEx : (winQ c).E.x = c.sl TX := rfl
  have hRz : (winQ c).R.z = c.sl RZ := rfl
  -- The window's slots, numbered.
  obtain key : ∀ x ∈ winSlots (winQ c), ∃ i, x = 64 + 72 * i ∧ ((i < 45 ∧ i ≠ ACC) ∨ WT ≤ i) := by
    intro x hx
    rw [winSlots_eq] at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain k : ∀ i ∈ roI ++ otherI ++ tblI, i ≠ TMP ∧ i ≠ 55 ∧ i ≠ 83 ∧ ((i < 45 ∧ i ≠ ACC) ∨ WT ≤ i) := by
      decide
    obtain ⟨k1, k2, k3, k4⟩ := k i hi
    exact ⟨i, hs i k1 k2 k3, k4⟩
  refine ⟨fun t ht hM hz => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · have hn := ht.nowrap
    rw [hMn, hRz] at hz
    rw [hEx, hRz, hMn]
    unfold Impl.Ecdh.X86_64.Cfg.invCallTo
    simp only [Code.inline]
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (copy_ok (Impl.Ecdh.X86_64.Cfg.invJAWords c) ht (o := bitsAt c.n 2) (a := c.sl WB)
      (by omega_arith) (by omega_arith) (by omega_arith)) fun t₁ ⟨e₁, k₁, O₁⟩ => ?_
    obtain ht₁ := ht.of_keepRegs k₁ (by decide)
    refine WP.mono (copy_ok c.n ht₁ (o := Impl.Ecdh.X86_64.Cfg.invJAPt c) (a := c.sl PT)
      (by omega_arith) (by omega_arith) (by omega_arith)) fun t₂ ⟨e₂, k₂, O₂⟩ => ?_
    obtain ht₂ := ht₁.of_keepRegs k₂ (by decide)
    obtain U₂ : Unch base [(bitsAt c.n 2, 8 * Impl.Ecdh.X86_64.Cfg.invJAWords c),
        (Impl.Ecdh.X86_64.Cfg.invJAPt c, 8 * c.n)] t.mem t₂.mem := O₁.unch.trans O₂.unch
    obtain hM₂ : ModOkW c.MP' size c.C.p t₂.mem base := (hM.of_inl).unch U₂ (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      show c.sl MP + 8 * c.n ≤ w.1 ∨ _
      rcases hw with rfl | rfl <;> dsimp only <;> omega_arith) hn
    obtain z₂ : wordsVal t₂.mem base (c.sl RZ) c.n = wordsVal t.mem base (c.sl RZ) c.n :=
      U₂.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
    refine WP.seq (WP.mono (show WP isa c.pPow.inline t₂ fun s' => KeepRegs (invClob c.n) t₂ s' ∧
        Unch base (pwW c) t₂.mem s'.mem ∧ wordsVal s'.mem base (c.sl ACC) c.n < c.C.p ∧
        toM c.C.p (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
          toM c.C.p (2 ^ (64 * c.n)) (wordsVal t₂.mem base (c.sl RZ) c.n) ^ (c.C.p - 2) by
      unfold Cfg.pPow
      cases hi' : c.inverse with
      | none => exact absurd hi' hi
      | some C =>
        obtain ⟨h9', -⟩ := hc.inverse (by rw [hi']; rfl)
        dsimp only
        rw [ite_eq_right_of_eq_false _ _ (eq_false fun hv => by have := hc.inv4_n hv; omega_arith)]
        exact WP.mono (invPFn_ok hc (by omega_arith) h9' ht₂ hM₂ (by rw [z₂]; exact hz)) fun _ h => h.2)
      fun t₃ ⟨K₃, U₃, lt₃, v₃⟩ => ?_)
    obtain ht₃ := ht₂.of_keepRegs K₃ (rdi_not_invClob _)
    obtain p₃ : ∀ x, (ofs base x < 2152 ∨ 2296 ≤ ofs base x) → (ofs base x < 5056 ∨ 5696 ≤ ofs base x) →
        (ofs base x < 4024 ∨ 4096 ≤ ofs base x) → t₃.mem x = t₂.mem x := fun x h1 h2 h3 =>
      U₃ x fun w hw => by
        simp only [pwW, slW, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
          List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (copy_ok c.n ht₃ (o := c.sl TX) (a := c.sl ACC) (by omega_arith) (by omega_arith) (by omega_arith))
      fun t₄ ⟨e₄, k₄, O₄⟩ => ?_
    obtain ht₄ := ht₃.of_keepRegs k₄ (by decide)
    refine WP.mono (copy_ok c.n ht₄ (o := c.sl PT) (a := Impl.Ecdh.X86_64.Cfg.invJAPt c) (by omega_arith)
      (by omega_arith) (by omega_arith)) fun t₅ ⟨e₅, k₅, O₅⟩ => ?_
    obtain ht₅ := ht₄.of_keepRegs k₅ (by decide)
    refine WP.mono (copy_ok (Impl.Ecdh.X86_64.Cfg.invJAWords c) ht₅ (o := c.sl WB) (a := bitsAt c.n 2)
      (by omega_arith) (by omega_arith) (by omega_arith)) fun t₆ ⟨e₆, k₆, O₆⟩ => ?_
    obtain hrax : ∀ r ∈ [Reg.rax], r ∈ invClob c.n := fun r hr => by
      rw [List.mem_singleton.mp hr]; simp [invClob, powClob, clob]
    -- What the call and the copies after it keep.
    obtain far : ∀ x, (ofs base x < 2152 ∨ 2296 ≤ ofs base x) → (ofs base x < 5056 ∨ 5696 ≤ ofs base x) →
        (ofs base x < 4024 ∨ 4096 ≤ ofs base x) → (ofs base x < 1504 ∨ 1576 ≤ ofs base x) →
        t₄.mem x = t₂.mem x := fun x h1 h2 h3 h4 => by
      rw [O₄ x (by omega_arith), p₃ x h1 h2 h3]
    obtain U₄ : Unch base [(2152, 144), (5056, 640), (4024, 72), (1504, 72)] t₂.mem t₄.mem := fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
      exact far x (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    obtain W4 : ∀ {d k : Nat}, 4472 ≤ d → d + 8 * k ≤ 5056 →
        wordsVal t₄.mem base d k = wordsVal t₂.mem base d k := fun h1 h2 =>
      U₄.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
    obtain B : wordsVal t₅.mem base (bitsAt c.n 2) 47 = wordsVal t.mem base (c.sl WB) 47 := by
      rw [O₅.wordsVal (by omega_arith) (by omega_arith), W4 (by omega_arith) (by omega_arith),
        O₂.wordsVal (by omega_arith) (by omega_arith), ← eW, e₁]
    obtain P : wordsVal t₄.mem base (Impl.Ecdh.X86_64.Cfg.invJAPt c) c.n = wordsVal t.mem base (c.sl PT) c.n := by
      rw [W4 (by omega_arith) (by omega_arith), e₂, O₁.wordsVal (by omega_arith) (by omega_arith)]
    obtain X : wordsVal t₆.mem base (c.sl TX) c.n = wordsVal t₃.mem base (c.sl ACC) c.n := by
      rw [O₆.wordsVal (by omega_arith) (by omega_arith), O₅.wordsVal (by omega_arith) (by omega_arith), e₄]
    refine ⟨((((k₁.mono hrax).trans (k₂.mono hrax)).trans K₃).trans ((k₄.mono hrax).trans
      ((k₅.mono hrax).trans (k₆.mono hrax)))), fun x hx => ?_, by rw [X]; exact lt₃, ?_⟩
    · simp only [invWinCallW, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
      rw [eTX, eB2, eT, eTMP, eACC, eB3, eWB, hn9] at hx
      by_cases hb' : 5320 ≤ ofs base x ∧ ofs base x < 5696
      · -- The window's bits, put back.
        refine byte_of_wordsVal (base := base) (d := c.sl WB) (k := 47) (x := x) ?_ (by omega_arith) (by omega_arith)
        rw [← B, ← eW, e₆]
      · by_cases hp : 2224 ≤ ofs base x ∧ ofs base x < 2296
        · -- `PT`, put back.
          rw [O₆ x (by omega_arith)]
          refine byte_of_wordsVal (base := base) (d := c.sl PT) (k := c.n) (x := x) ?_ (by omega_arith) (by omega_arith)
          rw [e₅, P]
        · rw [O₆ x (by omega_arith), O₅ x (by omega_arith), far x (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
            O₂ x (by omega_arith), O₁ x (by omega_arith)]
    · show toM _ _ _ = toM _ _ _ ^ _
      rw [X, v₃, z₂]
  · simp only [invWinCallW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rw [hMn, hMmo, hMtmp, hEx]
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · refine Or.inr (Or.inr ⟨Or.inl (by dsimp only; omega_arith), fun x hx => ?_⟩)
      obtain ⟨i, rfl, hi⟩ := key x hx
      dsimp only; unfold WT ACC at hi; omega_arith
    · exact Or.inr (Or.inl rfl)
    · refine Or.inr (Or.inr ⟨Or.inl (by dsimp only; omega_arith), fun x hx => ?_⟩)
      obtain ⟨i, rfl, hi⟩ := key x hx
      dsimp only; unfold WT ACC at hi; omega_arith
    · refine Or.inr (Or.inr ⟨Or.inl (by dsimp only; omega_arith), fun x hx => ?_⟩)
      obtain ⟨i, rfl, hi⟩ := key x hx
      dsimp only; unfold WT ACC at hi; omega_arith
  · simp only [invWinCallW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rw [hb, hJ]
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith

/-- What the inversion of `mulQJ4`'s table writes, a call or written out. -/
def invWinW (c : Cfg) : List (Nat × Nat) :=
  if c.n = 9 ∧ c.inverse.isSome then invWinCallW c else invW (Impl.Ecdh.X86_64.Cfg.invWin c)

/-- The inversion of `mulQJ4`'s table, a call or written out (`invWinProg`). -/
theorem invSpecQP (hc : CfgOk c) (h9 : c.n ≤ 9) {base : Addr} :
    InvSpecW (winQ c) c.C base size (Impl.Ecdh.X86_64.Cfg.invWinProg c) (invWinW c) := by
  unfold Impl.Ecdh.X86_64.Cfg.invWinProg invWinW
  by_cases h : c.n = 9 ∧ c.inverse.isSome
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h)]
    exact invSpecQCall hc h.1 fun e => by have := h.2; rw [e] at this; exact absurd this (by decide)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h)]
    exact invSpecQ hc h9

/-- What the inversion writes is within what the window method in Jacobian
coordinates, and the power after it, may write: `winXJ`, slots and `pwW`. -/
theorem invWinW_cover :
    ∀ w ∈ invWinW c, ∃ w' ∈ winXJ c ++ slW c (otherI ++ tblI ++ [TMP]) ++ pwW c,
      w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  intro w hw
  obtain self : ∀ {w : Nat × Nat} {l : List (Nat × Nat)}, w ∈ l → ∃ w' ∈ l, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 :=
    fun h => ⟨_, h, Nat.le_refl _, Nat.le_refl _⟩
  obtain hX : (c.sl TX, 8 * c.n) ∈ winXJ c ++ slW c (otherI ++ tblI ++ [TMP]) ++ pwW c :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨TX, by decide, rfl⟩))
  obtain hB : (bitsAt c.n 2, invTbl c.n) ∈ winXJ c ++ slW c (otherI ++ tblI ++ [TMP]) ++ pwW c :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)))
  obtain hT : (c.sl TMP, 8 * c.n) ∈ winXJ c ++ slW c (otherI ++ tblI ++ [TMP]) ++ pwW c :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨TMP, by decide, rfl⟩))
  unfold invWinW at hw
  split at hw
  · simp only [invWinCallW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact self hX
    · exact self hB
    · exact self hT
    · exact self (List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨ACC, by decide, rfl⟩)))
    · refine ⟨(bitsAt c.n 3, 64 * c.n + 64), List.mem_append_right _ (List.mem_append_right _
        (List.mem_singleton_self _)), Nat.le_refl _, ?_⟩
      dsimp only
      rw [bitsAt_eq]; simp (disch := sl_ne) only [sl_eq]; unfold WB; omega_arith
  · simp only [invW, Impl.Ecdh.X86_64.Cfg.invWin, InvCfg.ofMod, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact self hX
    · exact self hB
    · exact self hT

/-! ## The window method -/

/-- `winMul_ok` by windows in Jacobian coordinates (`windowJ_ok`), for a curve
of prime order (`PrimeOrder`), with the bound it needs for scalars
of `nbits` bits. -/
theorem winMulJ_ok (hc : CfgOk c) (h9 : c.n ≤ 9) (hC : Law c.C) (hO : PrimeOrder c.C)
    (hbd : 16 * ((2 ^ c.nbits + 135) / 256) + 8 < c.C.n) {base : Addr} {s : State}
    (hs : Scr s base size) {g : Reg → BitVec 64} (F : Fixed c base g s.mem) (hbp : sv c base s BP = c.mont c.C.b)
    {P : Point c.C} (hP : onCurve c.C P = true) (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P) {ks : Nat} (hks : ks < 45)
    (hk8 : sv c base s ks < 2 ^ c.nbits) {rest : Prog isa} {R : State → Prop}
    (h : ∀ s', WinMulPostJ c base P (sv c base s ks) s s' → WP isa rest s' R) (hkT : ks ≠ TMP := by decide) :
    WP isa (.seq (.seq (c.winPrep (c.sl ks))
      (WinCfg.windowJ (winQ c) (Impl.Ecdh.X86_64.Cfg.invWinProg c)).inline) rest) s R := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have hrec : wordsVal s.mem base (c.sl ks) c.n + 8 * geom c.winJ < 16 ^ c.winJ := recode_lt_bits hk8
  have hJle : c.winJ ≤ 16 * c.n + 1 := by
    unfold Cfg.winJ; have := hc.len_hi; have := hc.nbits_le; omega_arith
  have hWK : c.sl WK + 16 * c.n ≤ size := by
    have := sl_le_win c h9 (i := WK + 1) (by decide)
    simp (disch := sl_ne) only [sl_eq] at this ⊢; rw [Nat.mul_add] at this; omega_arith
  have hKW := sl_lt c (show ks < WK by unfold WK; omega_arith) (.inl hkT)
  have h16 : (16 : Nat) ^ c.winJ ≤ 2 ^ (64 * (c.n + 1)) := by
    rw [show (16 : Nat) = 2 ^ 4 by rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega_arith)
  have hJ : (winQ c).J = c.winJ := rfl
  have hK : c.winK = c.sl WK := rfl
  have hB : c.winBits = c.sl WB := rfl
  have e82 : c.sl WK + 16 * c.n = c.sl WB := by simp (disch := sl_ne) only [sl_eq]; unfold WK WB; omega_arith
  have h4 := (hc.inv (by omega_arith)).1
  have hB8 : c.sl WB + 64 * (c.n + 1) ≤ c.sl WB + 80 * c.n := by omega_arith
  have hBs : c.sl WB + 80 * c.n ≤ size := by
    have := sl_le_win c h9 (i := WB + 9) (by decide)
    simp (disch := sl_ne) only [sl_eq] at this ⊢; rw [Nat.mul_add] at this; omega_arith
  rw [Cfg.winPrep]
  refine WP.seq (WP.seq (WP.seq ?_))
  rw [hK, offset_eq]
  refine WP.mono (addConst_ok hs (n := c.n) (src := c.sl ks) (dst := c.sl WK)
    (c := 8 * geom c.winJ) h0 (sl_le c h7 hks) (by omega_arith)
    (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [hB]
  refine WP.mono (bits_ok hs₁ (n := c.n + 1) (src := c.sl WK) (dst := c.sl WB) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (Or.inl (by omega_arith))) fun s₂ ⟨b₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [e₁] at b₂
  have U₂ : Unch base (winX c) s.mem s₂.mem :=
    ((O₁.mono (o' := c.sl WK) (n' := 16 * c.n) (Nat.le_refl _) (by omega_arith)).unch.trans
      ((O₂.mono (o' := c.sl WB) (n' := 80 * c.n) (Nat.le_refl _) (by omega_arith)).unch)).mono
      (fun w hw => by rcases List.mem_append.mp hw with h | h <;> (rw [List.mem_singleton.mp h]; simp [winX, hK, hB]))
  have F₂ := F.unch h7 hn fixedOk_winX U₂
  have e₂ : ∀ {i}, i < 45 → sv c base s₂ i = sv c base s i := fun hi =>
    sv_unch U₂ h7 hn hi (apart_winX hi)
  have hM₂ := modP_of hc F₂.mp
  have tv : ∀ {i}, i < 45 → tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := fun hi => by
    show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _); rw [e₂ hi]
  have hF : WinFixed (winQ c) c.C base s₂ P (wordsVal s.mem base (c.sl ks) c.n + 8 * geom c.winJ) := by
    refine ⟨?_, ?_, fun x hx => ?_, F₂.zero, ?_, fun t ht => ?_⟩
    · show toM _ _ (wordsVal s₂.mem _ (c.sl AP) c.n) = _; rw [F₂.ap]; exact toM_cmont hc _
    · show toM _ _ (sv c base s₂ BP) = _; rw [e₂ (by decide), hbp]; exact toM_cmont hc _
    · simp only [winRo, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact lt_of_eq_of_lt F₂.ap (hmont _)
      · exact lt_of_eq_of_lt ((e₂ (i := BP) (by decide)).trans hbp) (hmont _)
      · exact lt_of_eq_of_lt F₂.zero (by omega_arith)
      · exact lt_of_eq_of_lt (e₂ (i := PX) (by decide)) hpx
      · exact lt_of_eq_of_lt (e₂ (i := PY) (by decide)) hpy
      · exact lt_of_eq_of_lt F₂.onep (Nat.mod_lt _ (by omega_arith))
    · show Rep _ (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY))
        (tmv c.C c.n base s₂ (c.sl ONEP)) P
      rw [tv (by decide), tv (by decide), tv (by decide)]; exact hrep
    · rw [hJ] at ht
      exact b₂ t (by omega_arith)
  have hJ2 : 2 ≤ c.winJ := by
    unfold Cfg.winJ
    have hnb := hc.n_bits
    by_contra hlt
    have : 2 ^ c.nbits ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) (by omega)
    omega_arith
  have hP0 : P ≠ .infinity := by
    intro e
    have hz := (hrep.z_eq_zero_iff).mpr e
    have h1 : tmv c.C c.n base s (c.sl ONEP) = 1 := by
      show toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n) = 1
      rw [F.onep]; exact toM_one hpR
    exact hC.one_ne_zero (h1 ▸ hz)
  refine WP.mono (windowJ_ok (winLayQ hc h9) (winXQ hc h9) hpR hC hc.am3 hO hP hP0 hc.p_lt (hmont 1)
    (show toM c.C.p (2 ^ (64 * c.n)) (c.mont 1) = 1 by rw [toM_cmont hc]; rfl) (invSpecQP hc h9) hs₂ (hM₂.inl c.hot) hF
    (by rw [hJ]; exact hrec) (Nat.le_add_left _ _) (by rw [hJ]; exact hJ2)
    (by rw [hJ]; exact winE_two_bound hJ2 hk8 hbd)) fun s₃ ⟨K₃, U₃, M₃, L₃, R₃⟩ => h s₃ ?_
  rw [winW_eq] at U₃
  rw [hJ, Nat.add_sub_cancel] at R₃
  have c₁ : ∀ r ∈ [Reg.rax, .r8], r ∈ powClob c.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [powClob, clob]
    · exact mem_powClob_of_clob (r8_mem_clob _)
  have c₂ : ∀ r ∈ [Reg.rax, .rdx, .rbx], r ∈ powClob c.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [powClob, clob]
  have pc : ∀ r ∈ powClob c.n, r ∈ invClob c.n := fun r h => List.mem_cons_of_mem _ h
  exact ⟨hs₂.of_keepRegs K₃ (rdi_not_invClob _),
    (((k₁.mono c₁).trans (k₂.mono c₂)).mono pc).trans K₃,
    (U₂.trans U₃).cover fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact ⟨w, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hw)),
          Nat.le_refl _, Nat.le_refl _⟩
      · rcases List.mem_append.mp hw with hw | hw
        · exact ⟨w, List.mem_append_left _ (List.mem_append_right _ hw), Nat.le_refl _, Nat.le_refl _⟩
        · exact invWinW_cover w hw, M₃.of_inl, L₃, R₃⟩


/-- `mulPow_ok` for `mulQJ4`. -/
theorem mulPowJ4_ok (hc : CfgOk c) (h9 : c.n ≤ 9) (hC : Law c.C) (hO : PrimeOrder c.C)
    (hbd : 16 * ((2 ^ c.nbits + 135) / 256) + 8 < c.C.n) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) (hbp : sv c base s BP = c.mont c.C.b)
    {P : Point c.C} (hP : onCurve c.C P = true) (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P)
    {k : Nat} (hk : sv c base s K = k) (hk8 : k < 2 ^ (8 * c.C.len))
    (ht₁ : ¬ c.n ≤ 9 → ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0)
    {rest : Prog isa} {R : State → Prop} (h : ∀ s', MulPostW c (mulQJ4W c) base P k s s' → WP isa rest s' R) :
    WP isa (.seq (Impl.Ecdh.X86_64.Cfg.mulQJ4 c).inline (.seq c.pPow.inline rest)) s R := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  unfold Impl.Ecdh.X86_64.Cfg.mulQJ4
  · refine WP.seq (WP.seq (WP.mono (maskK_ok hc hs (hk ▸ hk8)) fun s₁ ⟨hs₁, k₁, e₁, U₁⟩ => ?_))
    have F₁ := F.unch h7 hn (fixedOk_slW (l := [K]) (by decide)) U₁
    have v₁ : ∀ {i}, i < 45 → i ≠ K → sv c base s₁ i = sv c base s i := fun hi hne =>
      sv_unch U₁ h7 hn hi (apart_slW (by simpa using hne))
    have tv₁ : ∀ {i}, i < 45 → i ≠ K → tmv c.C c.n base s₁ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
      fun hi hne => by show toM _ _ (sv c base s₁ _) = toM _ _ (sv c base s _); rw [v₁ hi hne]
    refine WP.seq_iff.mp (winMulJ_ok hc h9 hC hO hbd hs₁ F₁ (by rw [v₁ (by decide) (by decide)]; exact hbp) hP
      (by rw [v₁ (by decide) (by decide)]; exact hpx) (by rw [v₁ (by decide) (by decide)]; exact hpy)
      (by rw [tv₁ (by decide) (by decide), tv₁ (by decide) (by decide), tv₁ (by decide) (by decide)]; exact hrep)
      (ks := K) (by decide) (by rw [e₁]; exact Nat.mod_lt _ (Nat.pow_pos (by decide))) fun s₃ W => ?_)
    have F₃ := F₁.unch h7 hn ((fixedOk_winXJ.append (fixedOk_slW (by decide))).append fixedOk_pwW) W.unch
    have rz₃ : wordsVal s₃.mem base (c.sl RZ) c.n < c.C.p := W.lt _ (by simp)
    refine WP.seq (WP.mono (pPow_ok hc W.scr W.mod rz₃ F₃.onep (fun h9 t ht => by
        rw [tbl_unch W.unch h7 hn (j := 1) (by decide) ht (apart_append (apart_append (tbl_apart_winXJ (by decide) ht)
          (tbl_apart_slW' (by decide) (by decide) ht)) (tbl_apart_pwW (by decide) ht (.inr (by omega_arith)))),
          tbl_unch U₁ h7 hn (j := 1) (by decide) ht (tbl_apart_slW' (by decide) (by decide) ht)]
        exact ht₁ h9 t ht)) fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => h s₄ ?_)
    have r₄ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₄ i = sv c base s₃ i := fun hi h₁ =>
      sv_unch U₄ h7 hn hi (apart_pwW hi h₁)
    refine ⟨W.scr.of_keepRegs K₄ (rdi_not_invClob _), ?_, by rw [K₄.rd, W.keep.rd, k₁.rd],
      by rw [K₄.wr, W.keep.wr, k₁.wr], ((U₁.trans W.unch).trans U₄).mono ?_,
      fun _ hn' => ?_, lt₄, ?_, ?_⟩
    · rw [K₄.gpr _ (rsi_not_invClob _), W.keep.gpr _ (rsi_not_invClob _), k₁.gpr _ (by decide)]
    · intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · exact List.mem_append_left _ (List.mem_append_right _ (slW_mono (by decide) hw))
        · rcases List.mem_append.mp hw with hw | hw
          · rcases List.mem_append.mp hw with hw | hw
            · exact List.mem_append_left _ (List.mem_append_left _ hw)
            · exact List.mem_append_left _ (List.mem_append_right _ (slW_mono (by decide) hw))
          · exact List.mem_append_right _ hw
      · exact List.mem_append_right _ hw
    · show Rep _ (toM _ _ (sv c base s₄ RX)) (toM _ _ (sv c base s₄ RY)) (toM _ _ (sv c base s₄ RZ)) _
      rw [r₄ (i := RX) (by decide) (by decide), r₄ (i := RY) (by decide) (by decide),
        r₄ (i := RZ) (by decide) (by decide)]
      have hq := W.q
      rw [e₁, hk, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hn' hc.n_bits)] at hq
      exact hq
    · show _ = toM _ _ (sv c base s₄ RZ) ^ _
      rw [r₄ (i := RZ) (by decide) (by decide)]
      exact v₄
    · rw [r₄ (i := RZ) (by decide) (by decide)]; exact rz₃

theorem mulQJ4_ok (hc : CfgOk c) (h9 : c.n ≤ 9) (hC : Law c.C) (hO : PrimeOrder c.C)
    (hbd : 16 * ((2 ^ c.nbits + 135) / 256) + 8 < c.C.n) :
    MulOk c (Impl.Ecdh.X86_64.Cfg.mulQJ4 c) (mulQJ4W c) :=
  fun hs _ F hbp _ hP hpx hpy hrep _ _ _ _ hk hk8 _ ht₁ _ _ h =>
    mulPowJ4_ok hc h9 hC hO hbd hs F hbp hP hpx hpy hrep hk hk8 ht₁ h

theorem mulQJ4_w (hc : CfgOk c) : MulW c (mulQJ4W c) where
  fixed := (fixedOk_winXJ.append (fixedOk_slW mulI_idx)).append fixedOk_pwW
  d := apart_append (apart_append (apart_winXJ (by decide)) (apart_slW (by decide))) (apart_pwW (by decide) (by decide))
  flag := fun w hw => by
    have := hc.n0
    rcases apart_append (apart_append (apart_winXJ (c := c) (i := FLAG) (by decide)) (apart_slW (by decide)))
      (apart_pwW (by decide) (by decide)) w hw with h | h
    · exact Or.inl (by omega_arith)
    · exact Or.inr h

end VG.Proof.Ecdh.X86_64
