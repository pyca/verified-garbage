import VerifiedGarbage.Proof.Ecdsa.X86.CombLays
import VerifiedGarbage.Proof.Weierstrass.X86.Rep

/-!
# ECDSA on x86 (32-bit): `[k]G`

`Cfg.gMul` is the comb for a curve with one, else the ladder; either leaves
`R = [k]G`, from the table of `k`'s bits, changing only the slots and word of
`gW` (`gMul_ok`).
-/

namespace VG.Proof.Ecdsa.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- What `[k]G` may write, by the comb (with `b R mod p` in `EM`) or the
ladder: their slots and the word past the table of `k`'s bits. -/
abbrev gW (c : Cfg) : List (Nat × Nat) :=
  slW c [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] ++
    [(c.wk, 16 * c.n + 4), (bitsAt c.n 0 + 64 * c.n, 4)]

/-- A slot is apart from the word past the table of `k`'s bits. -/
theorem apart_pad {i : Nat} (hi : i < 45) :
    ∀ w ∈ [(bitsAt c.n 0 + 64 * c.n, 4)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inl (sl_below_bits c hi 0 _)

/-- A slot apart from what `[k]G` writes. -/
theorem apart_gW {i : Nat} (hi : i < 45)
    (hl : i ∉ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM]) :
    ∀ w ∈ gW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_slW hl) (apart_append (apart_wk hi) (apart_pad hi))

theorem fixedOk_gW : FixedOk c (gW c) := by
  refine (fixedOk_slW (by decide)).append (fixedOk_wk.append ?_)
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_bits c (by decide) 0 _))

/-- Tables `1` and `2` are apart from what `[k]G` writes. -/
theorem tbl_apart_gW {j t : Nat} (hj : j = 1 ∨ j = 2) (ht : t < 64 * c.n) :
    ∀ w ∈ gW c, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  refine apart_append (tbl_apart_slW (by decide) j t)
    (apart_append (tbl_apart_wk (by omega) ht) ?_)
  intro w hw
  rw [List.mem_singleton.mp hw]
  simp only [bitsAt_eq]
  rcases hj with rfl | rfl <;> exact Or.inr (by omega)

/-- The flag word apart from what `[k]G` writes. -/
theorem flag_unch_gW {base : Addr} {m m' : Mem} (hu : Unch base (gW c) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 32) :
    m'.readW (off base (c.sl FLAG)) 32 = m.readW (off base (c.sl FLAG)) 32 := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine Unch.readW32 hu (fun w hw => ?_) (by omega)
  rcases apart_gW (c := c) (i := FLAG) (by decide) (by decide) w hw with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

/-- Every fixed-base write fits in the existing scratch buffer. -/
theorem gW_le (h7 : c.n < 10) : ∀ w ∈ gW c, w.1 + w.2 ≤ size := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have hl : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM], i < 45 := by decide
    exact sl_le c h7 (hl i hi)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · simpa only [accLen_MP'] using wk_le c h7 (M := c.MP') rfl
    · rw [bitsAt_eq]; change _ ≤ 8192; omega

/-- Prepare the comb's Montgomery constant and retain its public table pointer. -/
theorem combPrepare_ok (hc : CfgOk c) {d : CombData} (hcd : c.comb = some d)
    {base : Addr} {g : Reg → BitVec 32} {s : State} {k : Nat}
    (hs : Scr s base size) (F : Fixed c base g s.mem) (hkl : k < 2 ^ (64 * c.n))
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (hTM : TblMem s ((g .eax).setWidth 64) (c.combWords d))
    (hout : ∀ i < (c.combWords d).length, ∀ b < 8,
      size ≤ ofs base ((g .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) :
    WP isa (.block (setConst c.n (c.sl EM) (c.mont c.C.b))) s fun s₁ =>
      Keeps [.eax] s s₁ ∧ Scr s₁ base size ∧ ModOkW c.MP' size c.C.p s₁.mem base ∧
      TCombFixed (c.combCfg d) c.C base size s₁ k ((g .eax).setWidth 64) (c.combWords d) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by have := hc.p_ge; omega)
  have hp3 := hc.p_ge
  refine WP.mono (setConst_ok hs (n := c.n) (o := c.sl EM) (x := c.mont c.C.b)
    (sl_le c h7 (by decide)) (by have := hc.p_lt; have := hmont c.C.b; omega))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have F₁ := F.unch h7 hn (fixedOk_slW (l := [EM]) (by decide)) O₁.unch
  have ht₁ : ∀ t < 64 * c.n, s₁.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      rw [tbl_unch (W := slW c [EM]) O₁.unch h7 (j := 0) (by decide) ht (tbl_apart_slW (by decide) 0 t)]
      exact ht₀ t ht
  have hTM₁ : TblMem s₁ ((g .eax).setWidth 64) (c.combWords d) :=
    hTM.of_unch (by rw [k₁.2.1, k₁.2.2]) O₁.unch (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact sl_le c h7 (by decide)) hout
  have hF : TCombFixed (c.combCfg d) c.C base size s₁ k ((g .eax).setWidth 64)
      (tcombWords (c.combCfg d).M.n (2 ^ (64 * (c.combCfg d).M.n)) c.C.p d.tbl) := by
    refine ⟨?_, ?_, fun x hx => ?_, F₁.zero, ht₁, hkl, ?_, hTM₁, hout⟩
    · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem _ (c.sl AP) c.n) = _
      rw [F₁.ap]; exact toM_cmont hc _
    · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem _ (c.sl EM) c.n) = _
      rw [e₁]; exact toM_cmont hc _
    · simp only [combRo, TCombCfg.toComb, Cfg.combCfg, Cfg.rcbSlots, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact lt_of_eq_of_lt F₁.ap (hmont _)
      · exact lt_of_eq_of_lt e₁ (hmont _)
      · exact lt_of_eq_of_lt F₁.zero (by omega)
    · change (s₁.mem.readW (off base Cfg.combPtr) 32).setWidth 64 = _
      rw [F₁.table (by simp [hcd])]
  exact ⟨k₁, hs₁, modP_of hc F₁.mp, hF⟩

/-- `R = [k]G`, by the comb or the ladder, from the table of `k`'s bits, with
`R = O` (for the ladder) and the comb's tables (`hTb`) where the comb reads
them. -/
theorem gMul_ok' (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c)
    (hCo : ∀ d, c.comb = some d → CombOk c d) (ham3 : AM3 c.C) {base : Addr} {g : Reg → BitVec 32}
    {s : State} (hs : Scr s base size) (F : Fixed c base g s.mem) {k : Nat} (hkl : k < 2 ^ (64 * c.n))
    (hrx : sv c base s RX = 0) (hry : sv c base s RY = c.mont 1) (hrz : sv c base s RZ = 0)
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (hTb : ∀ d, c.comb = some d → TblMem s ((g .eax).setWidth 64) (c.combWords d) ∧
      ∀ i < (c.combWords d).length, ∀ b < 8,
        size ≤ ofs base ((g .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) :
    WP isa c.gMul s fun s' => Keeps (powClob) s s' ∧ Unch base (gW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul k (G c.C)) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  unfold Cfg.gMul
  cases hcd : c.comb with
  | none =>
    have hlt : ∀ x ∈ ladR c.ladderCfg, wordsVal s.mem base x c.MP'.n < c.C.p := by
      intro x hx
      have hx' : x ∈ [AP, B3P, GX, GY, ONEP, RX, RY, RZ].map c.sl := hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      show sv c _ s i < c.C.p
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact lt_of_eq_of_lt F.ap (hmont _)
      · exact lt_of_eq_of_lt F.b3p (hmont _)
      · exact lt_of_eq_of_lt F.gx (hmont _)
      · exact lt_of_eq_of_lt F.gy (hmont _)
      · exact lt_of_eq_of_lt F.onep (Nat.mod_lt _ (by omega))
      · exact lt_of_eq_of_lt hrx (by omega)
      · exact lt_of_eq_of_lt hry (hmont _)
      · exact lt_of_eq_of_lt hrz (by omega)
    have hG : Rep c.C (tmv c.C c.n base s (c.sl GX)) (tmv c.C c.n base s (c.sl GY))
        (tmv c.C c.n base s (c.sl ONEP)) (G c.C) := by
      show Rep c.C (toM _ _ (wordsVal s.mem _ (c.sl GX) c.n)) (toM _ _ (wordsVal s.mem _ (c.sl GY) c.n))
        (toM _ _ (wordsVal s.mem _ (c.sl ONEP) c.n)) (G c.C)
      rw [F.gx, F.gy, F.onep, toM_cmont hc, toM_cmont hc, toM_one hpR]
      exact rep_affine' hC _ _
    have hR : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
        (tmv c.C c.n base s (c.sl RZ)) (mul (k >>> (64 * c.n)) (G c.C)) := by
      show Rep c.C (toM _ _ (sv c _ s RX)) (toM _ _ (sv c _ s RY)) (toM _ _ (sv c _ s RZ)) _
      rw [hrx, hry, hrz, toM_cmont hc, toM_zero, shiftRight_eq_zero hkl, mul_zero_pt]
      exact rep_infinity' hC
    have hstep := step_rep (L := c.ladderCfg) (k := k) hC hc.onG (by
        show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem _ (c.sl AP) c.n) = _
        rw [F.ap]; exact toM_cmont hc _)
      (by
        show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem _ (c.sl B3P) c.n) = _
        rw [F.b3p]; exact toM_cmont hc _) hG
    refine WP.mono (ladder_ok (ladLay hc) (ladWk hc) hpR hs (modP_of hc F.mp) hlt hstep hR ht₀)
      fun s' ⟨K', U', M', L', R'⟩ => ⟨K', ?_, M', L', by rw [Nat.shiftRight_zero] at R'; exact R'⟩
    rw [ladWx_eq, accLen_MP'] at U'
    have hsub : slW c [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ,
        TMP] ⊆ slW c [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] :=
      List.map_subset _ (by decide)
    exact Unch.cover U' fun w hw => ⟨w, by
      rcases List.mem_append.mp hw with hw | hw
      · exact List.mem_append_left _ (hsub hw)
      · exact List.mem_append_right _ (by rw [List.mem_singleton.mp hw]; exact List.mem_cons_self ..), Nat.le_refl _, Nat.le_refl _⟩
  | some d =>
    have hd := hCo d hcd
    obtain ⟨hTM, hout⟩ := hTb d hcd
    have hn := hs.nowrap
    -- `b R mod p` in `EM`.
    refine WP.seq (WP.mono (setConst_ok hs (n := c.n) (o := c.sl EM) (x := c.mont c.C.b)
      (sl_le c h7 (by decide)) (by have := hc.p_lt; have := hmont c.C.b; omega))
      fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
    have hs₁ := hs.of_keeps k₁ (by decide)
    have F₁ := F.unch h7 hn (fixedOk_slW (l := [EM]) (by decide)) O₁.unch
    have ht₁ : ∀ t < 64 * c.n, s₁.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0 :=
      fun t ht => by
        rw [tbl_unch (W := slW c [EM]) O₁.unch h7 (j := 0) (by decide) ht (tbl_apart_slW (by decide) 0 t)]
        exact ht₀ t ht
    have hTM₁ : TblMem s₁ ((g .eax).setWidth 64) (c.combWords d) :=
      hTM.of_unch (by rw [k₁.2.1, k₁.2.2]) O₁.unch (fun w hw => by
        rw [List.mem_singleton.mp hw]; exact sl_le c h7 (by decide)) hout
    have hF : TCombFixed (c.combCfg d) c.C base size s₁ k ((g .eax).setWidth 64)
        (tcombWords (c.combCfg d).M.n (2 ^ (64 * (c.combCfg d).M.n)) c.C.p d.tbl) := by
      refine ⟨?_, ?_, fun x hx => ?_, F₁.zero, ht₁, hkl, ?_, hTM₁, hout⟩
      · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem _ (c.sl AP) c.n) = _
        rw [F₁.ap]; exact toM_cmont hc _
      · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem _ (c.sl EM) c.n) = _
        rw [e₁]; exact toM_cmont hc _
      · simp only [combRo, TCombCfg.toComb, Cfg.combCfg, Cfg.rcbSlots, List.mem_cons, List.not_mem_nil,
          or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact lt_of_eq_of_lt F₁.ap (hmont _)
        · exact lt_of_eq_of_lt e₁ (hmont _)
        · exact lt_of_eq_of_lt F₁.zero (by omega)
      · change (s₁.mem.readW (off base Cfg.combPtr) 32).setWidth 64 = _
        rw [F₁.table (by simp [hcd])]
    refine WP.mono (tcombCore_ok (tcombLay hc hd) hC ham3 hc.onG (tcombVals hc hC (hT d hcd)) hc.p_lt hs₁
      (modP_of hc F₁.mp) hF) fun s' ⟨K', U', M', L', R'⟩ =>
        ⟨(k₁.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp [powClob, clob]).trans K', ?_, M', L', R'⟩
    change Unch base ((slW c [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP] ++
      [(c.wk, accLen c.MP')]) ++ [(bitsAt c.n 0 + 64 * c.n, 4 * (c.combCfg d).zw)]) s₁.mem s'.mem at U'
    rw [accLen_MP'] at U'
    have hz := zw_le hd
    refine Unch.cover (O₁.unch.trans U') fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · rw [List.mem_singleton.mp hw]
      exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem (f := fun i => (c.sl i, 8 * c.n))
        (show EM ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] by decide)),
        Nat.le_refl _, Nat.le_refl _⟩
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · have sub : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP],
            i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] := by decide
        exact ⟨w, List.mem_append_left _ (List.map_subset _ sub hw), Nat.le_refl _, Nat.le_refl _⟩
      · rw [List.mem_singleton.mp hw]
        exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), Nat.le_refl _, Nat.le_refl _⟩
    · rw [List.mem_singleton.mp hw]
      exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), Nat.le_refl _, by dsimp only; omega⟩

end VG.Proof.Ecdsa.X86
