import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Weierstrass.X86_64.Rep

/-!
# ECDSA on x86-64: `[k]G`

`Cfg.gMul` is the comb for a curve with one, else the ladder; either leaves
`R = [k]G`, from the table of `k`'s bits, changing only the slots and word of
`gW` (`gMul_ok`).
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- What `[k]G` may write, by the comb or the ladder: their slots and the
word past the table of `k`'s bits. -/
abbrev gW (c : Cfg) : List (Nat × Nat) :=
  slW c [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP] ++
    [(bitsAt c.n 0 + 64 * c.n, 8)]

/-- Memory unchanged but in ranges each within one of `W'`. -/
theorem _root_.VG.Proof.Weierstrass.Unch.cover {base : Addr} {W W' : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    (hW : ∀ w ∈ W, ∃ w' ∈ W', w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2) : Unch base W' m m' :=
  fun x hx => h x fun w hw => by
    obtain ⟨w', hw', h1, h2⟩ := hW w hw
    have := hx w' hw'; omega

/-- A slot is apart from the word past the table of `k`'s bits. -/
theorem apart_pad {i : Nat} (hi : i < 45) :
    ∀ w ∈ [(bitsAt c.n 0 + 64 * c.n, 8)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inl (sl_below_bits c hi 0 _)

/-- A slot apart from what `[k]G` writes. -/
theorem apart_gW {i : Nat} (hi : i < 45)
    (hl : i ∉ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP]) :
    ∀ w ∈ gW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_slW hl) (apart_pad hi)

theorem fixedOk_gW : FixedOk c (gW c) := by
  refine FixedOk.append (fixedOk_slW (by decide)) fun w hw => ?_
  rw [List.mem_singleton.mp hw]
  exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_bits c (by decide) 0 _))

/-- Tables `1` and `2` are apart from what `[k]G` writes. -/
theorem tbl_apart_gW {j t : Nat} (hj : j = 1 ∨ j = 2) :
    ∀ w ∈ gW c, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  refine apart_append (tbl_apart_slW (by decide) j t) fun w hw => ?_
  rw [List.mem_singleton.mp hw]
  simp only [bitsAt_eq]
  rcases hj with rfl | rfl <;> exact Or.inr (by omega)

/-- The flag word apart from what `[k]G` writes. -/
theorem flag_unch_gW {base : Addr} {m m' : Mem} (hu : Unch base (gW c) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 64) :
    word m' base (c.sl FLAG) = word m base (c.sl FLAG) := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine hu.word (fun w hw => ?_) (by omega)
  rcases apart_gW (c := c) (i := FLAG) (by decide) (by decide) w hw with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

/-- `R = [k]G`, by the comb or the ladder, from the table of `k`'s bits, with
`R = O` (for the ladder) and the comb's tables (`hTb`) where the comb reads
them. -/
theorem gMul_ok' (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c) {base : Addr} {g : Reg → BitVec 64}
    {s : State} (hs : Scr s base size) (F : Fixed c base g s.mem) {k : Nat} (hkl : k < 2 ^ (64 * c.n))
    (hrx : sv c base s RX = 0) (hry : sv c base s RY = c.mont 1) (hrz : sv c base s RZ = 0)
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (hTb : ∀ d, c.comb = some d → TblMem s (s.syms d.tsym) (c.combWords d) ∧
      ∀ i < (c.combWords d).length, ∀ b < 8,
        size ≤ ofs base (s.syms d.tsym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) :
    WP isa c.gMul s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (gW c) s.mem s'.mem ∧
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
    refine WP.mono (ladder_ok (ladLay hc) hpR hs (modP_of hc F.mp) hlt hstep hR ht₀)
      fun s' ⟨K', U', M', L', R'⟩ => ⟨K', ?_, M', L', by rw [Nat.shiftRight_zero] at R'; exact R'⟩
    rw [ladW_eq] at U'
    have hsub : slW c [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ,
        TMP] ⊆ slW c [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP] :=
      List.map_subset _ (by decide)
    exact Unch.cover U' fun w hw => ⟨w, List.mem_append_left _ (hsub hw), Nat.le_refl _, Nat.le_refl _⟩
  | some d =>
    have hd := hc.comb d hcd
    obtain ⟨hTM, hout⟩ := hTb d hcd
    have hF : TCombFixed (c.combCfg d) c.C base size s k (s.syms d.tsym)
        (tcombWords (c.combCfg d).M.n (2 ^ (64 * (c.combCfg d).M.n)) c.C.p d.tbl) := by
      refine ⟨?_, ?_, fun x hx => ?_, F.zero, ht₀, hkl, rfl, hTM, hout⟩
      · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem _ (c.sl AP) c.n) = _
        rw [F.ap]; exact toM_cmont hc _
      · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem _ (c.sl B3P) c.n) = _
        rw [F.b3p]; exact toM_cmont hc _
      · simp only [combRo, TCombCfg.toComb, Cfg.combCfg, Cfg.rcbSlots, List.mem_cons, List.not_mem_nil,
          or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact lt_of_eq_of_lt F.ap (hmont _)
        · exact lt_of_eq_of_lt F.b3p (hmont _)
        · exact lt_of_eq_of_lt F.zero (by omega)
    refine WP.mono (tcomb_ok (tcombLay hc hd) hC hc.onG (tcombVals hc hC (hT d hcd)) hc.p_lt hs
      (modP_of hc F.mp) hF) fun s' ⟨K', U', M', L', R'⟩ => ⟨K', ?_, M', L', R'⟩
    rw [tcombW_eq] at U'
    have hz := zw_le hd
    exact Unch.cover U' fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact ⟨w, List.mem_append_left _ hw, Nat.le_refl _, Nat.le_refl _⟩
      · rw [List.mem_singleton.mp hw]
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _, by dsimp only; omega⟩


/-- `R = [k]G`, by the comb or the ladder, after the setup and the tables. -/
theorem gMul_ok (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c) {hs : Option Nat} {s₀ : State} (hp : Pre c s₀)
    {s : State} (hS : St₁ c hs s₀ (s₀.gpr .r8) s) :
    WP isa c.gMul s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch (s₀.gpr .r8) (gW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem (s₀.gpr .r8) ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem (s₀.gpr .r8) x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RX)) (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RY))
        (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RZ)) (mul (kv c s₀) (G c.C)) :=
  gMul_ok' hc hC hT hS.scr hS.fixed (hS.k ▸ wordsVal_lt _ _ _ _) hS.rx hS.ry hS.rz hS.t₀ fun d hcd => by
    rw [hS.syms]; exact tbl_of hcd hp hS.rd hS.unch

end VG.Proof.Ecdsa.X86_64
