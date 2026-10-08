import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Weierstrass.X86_64.Rep
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ

/-!
# ECDSA on x86-64: `[k]G`

`Cfg.gMul` is the comb for a curve with one, else the ladder (`Cfg.gMulK`, for a
secret scalar, the comb with Booth's digits where the curve's has them); each leaves
`R = [k]G`, from the table of `k`'s bits, changing only the slots and word of
`gW` (`gMul_ok`).
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- What `[k]G` may write, by the comb (with `b R mod p` in `EM`) or the
ladder: their slots and the word past the table of `k`'s bits. -/
abbrev gW (c : Cfg) : List (Nat × Nat) :=
  slW c [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] ++
    [(bitsAt c.n 0 + 64 * c.n, 8)]

/-- A slot is apart from the word past the table of `k`'s bits. -/
theorem apart_pad {i : Nat} (hi : i < 45) :
    ∀ w ∈ [(bitsAt c.n 0 + 64 * c.n, 8)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inl (sl_below_bits c hi 0 _)

/-- A slot apart from what `[k]G` writes. -/
theorem apart_gW {i : Nat} (hi : i < 45)
    (hl : i ∉ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM]) :
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

/-- `R = [k]G` by a comb `P` (`d`'s, with its tables where it reads them),
after `b R mod p` is put in `EM`: what `P` gives from `TCombFixed`, `gMul`'s
postcondition. -/
theorem gMulComb_ok' (hc : BaseCfgOk c) {d : CombData} (hcd : c.comb = some d) {base : Addr}
    {g : Reg → BitVec 64} {s : State} (hs : Scr s base size) (F : Fixed c base g s.mem) {k : Nat}
    (hkl : k < 2 ^ (64 * c.n))
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (hTM : TblMem s (s.syms d.tsym) (c.combWords d))
    (hout : ∀ i < (c.combWords d).length, ∀ b < 8,
      size ≤ ofs base (s.syms d.tsym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) {P : Prog isa}
    (hP : ∀ s₁, Scr s₁ base size → ModOkW (c.combCfg d).M size c.C.p s₁.mem base →
      TCombFixed (c.combCfg d) c.C base size s₁ k (s₁.syms d.tsym)
        (tcombWords (c.combCfg d).M.n (2 ^ (64 * (c.combCfg d).M.n)) c.C.p d.tbl) →
      WP isa P s₁ fun s' => KeepRegs (powClob (c.combCfg d).M.n) s₁ s' ∧
        Unch base (tcombW (c.combCfg d)) s₁.mem s'.mem ∧ ModOkW (c.combCfg d).M size c.C.p s'.mem base ∧
        (∀ x ∈ [(c.combCfg d).A.x, (c.combCfg d).A.y, (c.combCfg d).A.z],
          wordsVal s'.mem base x (c.combCfg d).M.n < c.C.p) ∧
        Rep c.C (tmv c.C (c.combCfg d).M.n base s' (c.combCfg d).A.x)
          (tmv c.C (c.combCfg d).M.n base s' (c.combCfg d).A.y)
          (tmv c.C (c.combCfg d).M.n base s' (c.combCfg d).A.z) (mul k (G c.C))) :
    WP isa (.seq (.block (setConst c.n (c.sl EM) (c.mont c.C.b))) P) s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (gW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul k (G c.C)) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have hd := hc.comb d hcd
  have hn := hs.nowrap
  -- `b R mod p` in `EM`.
  refine WP.seq (WP.mono_syms (setConst_ok hs (n := c.n) (o := c.sl EM) (x := c.mont c.C.b)
    (sl_le c h7 (by decide)) (by have := hc.p_lt; have := hmont c.C.b; omega))
    fun s₁ ⟨e₁, k₁, O₁⟩ sy₁ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have F₁ := F.unch h7 hn (fixedOk_slW (l := [EM]) (by decide)) O₁.unch
  have ht₁ : ∀ t < 64 * c.n, s₁.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      rw [tbl_unch (W := slW c [EM]) O₁.unch h7 hn (j := 0) (by decide) ht (tbl_apart_slW (by decide) 0 t)]
      exact ht₀ t ht
  have hTM₁ : TblMem s₁ (s.syms d.tsym) (c.combWords d) :=
    hTM.of_unch (by rw [k₁.rd, k₁.wr]) O₁.unch (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact sl_le c h7 (by decide)) hout
  have hF : TCombFixed (c.combCfg d) c.C base size s₁ k (s₁.syms d.tsym)
      (tcombWords (c.combCfg d).M.n (2 ^ (64 * (c.combCfg d).M.n)) c.C.p d.tbl) := by
    refine ⟨?_, ?_, fun x hx => ?_, F₁.zero, ht₁, hkl, rfl, by rw [sy₁]; exact hTM₁,
      by rw [sy₁]; exact hout⟩
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
  refine WP.mono (hP s₁ hs₁ (modP_of hc F₁.mp) hF) fun s' ⟨K', U', M', L', R'⟩ =>
      ⟨(k₁.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp [powClob, clob]).trans K', ?_, M', L', R'⟩
  rw [tcombW_eq] at U'
  have hz := zw_le hd
  refine Unch.cover (O₁.unch.trans U') fun w hw => ?_
  rcases List.mem_append.mp hw with hw | hw
  · rw [List.mem_singleton.mp hw]
    exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem (f := fun i => (c.sl i, 8 * c.n))
      (show EM ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] by decide)),
      Nat.le_refl _, Nat.le_refl _⟩
  rcases List.mem_append.mp hw with hw | hw
  · have sub : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP],
        i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] := by decide
    exact ⟨w, List.mem_append_left _ (List.map_subset _ sub hw), Nat.le_refl _, Nat.le_refl _⟩
  · rw [List.mem_singleton.mp hw]
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _, by dsimp only; omega⟩


/-- `R = [k]G`, by the comb or the ladder, from the table of `k`'s bits, with
`R = O` (for the ladder) and the comb's tables (`hTb`) where the comb reads
them. -/
theorem gMul_ok' (hc : BaseCfgOk c) (hC : Law c.C) (hT : CombTbls c) {base : Addr} {g : Reg → BitVec 64}
    {s : State} (hs : Scr s base size) (F : Fixed c base g s.mem) {k : Nat} (hkl : k < 2 ^ (64 * c.n))
    (hrx : sv c base s RX = 0) (hry : sv c base s RY = c.mont 1) (hrz : sv c base s RZ = 0)
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (hTb : ∀ d, c.comb = some d → TblMem s (s.syms d.tsym) (c.combWords d) ∧
      ∀ i < (c.combWords d).length, ∀ b < 8,
        size ≤ ofs base (s.syms d.tsym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) (publicLookup : Bool := false) :
    WP isa (c.gMul publicLookup) s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (gW c) s.mem s'.mem ∧
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
        TMP] ⊆ slW c [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] :=
      List.map_subset _ (by decide)
    exact Unch.cover U' fun w hw => ⟨w, List.mem_append_left _ (hsub hw), Nat.le_refl _, Nat.le_refl _⟩
  | some d =>
    obtain ⟨hTM, hout⟩ := hTb d hcd
    exact gMulComb_ok' hc hcd hs F hkl ht₀ hTM hout fun s₁ hs₁ hM₁ hF =>
      tcomb_ok (tcombLay hc (hc.comb d hcd)) hC (hc.comb_am3 d hcd) hc.onG (tcombVals hc hC (hT d hcd).1) hc.p_lt hs₁
        hM₁ hF publicLookup

/-- `R = [k]G`, by the comb or the ladder, after the setup and the tables. -/
theorem gMul_ok (hc : BaseCfgOk c) (hC : Law c.C) (hT : CombTbls c) {hs : Option Nat} {s₀ : State} (hp : Pre c s₀)
    {s : State} (hS : St₁ c hs s₀ (s₀.gpr .r8) s) :
    WP isa c.gMul s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch (s₀.gpr .r8) (gW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem (s₀.gpr .r8) ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem (s₀.gpr .r8) x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RX)) (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RY))
        (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RZ)) (mul (kv c s₀) (G c.C)) :=
  gMul_ok' hc hC hT hS.scr hS.fixed (hS.k ▸ wordsVal_lt _ _ _ _) hS.rx hS.ry hS.rz hS.t₀ fun d hcd => by
    rw [hS.syms]; exact tbl_of hcd hp hS.rd hS.unch

/-- `R = [k]G` for a secret `k` (`gMulK`): by the comb with Booth's digits for
a curve whose comb has them, else as `gMul`. -/
theorem gMulK_ok' (hc : BaseCfgOk c) (hC : Law c.C) (hT : CombTbls c) {base : Addr} {g : Reg → BitVec 64}
    {s : State} (hs : Scr s base size) (F : Fixed c base g s.mem) {k : Nat} (hkl : k < 2 ^ (64 * c.n))
    (hrx : sv c base s RX = 0) (hry : sv c base s RY = c.mont 1) (hrz : sv c base s RZ = 0)
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (hTb : ∀ d, c.comb = some d → TblMem s (s.syms d.tsym) (c.combWords d) ∧
      ∀ i < (c.combWords d).length, ∀ b < 8,
        size ≤ ofs base (s.syms d.tsym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) :
    WP isa c.gMulK s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (gW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul k (G c.C)) := by
  unfold Cfg.gMulK
  cases hcd : c.comb with
  | none => exact gMul_ok' hc hC hT hs F hkl hrx hry hrz ht₀ hTb
  | some d =>
    cases hj : d.jac
    · simp only [hj, Bool.false_eq_true, ↓reduceIte]
      exact gMul_ok' hc hC hT hs F hkl hrx hry hrz ht₀ hTb
    · simp only [hj, ↓reduceIte]
      obtain ⟨hTM, hout⟩ := hTb d hcd
      exact gMulComb_ok' hc hcd hs F hkl ht₀ hTM hout fun s₁ hs₁ hM₁ hF =>
        tcombJ_ok (tcombLay hc (hc.comb d hcd)) hC (hc.comb_am3 d hcd) hc.onG (tcombVals hc hC (hT d hcd).1) hc.p_lt
          (by show 1 ≤ bitsAt c.n 0; rw [bitsAt_eq]; omega) ((hT d hcd).2 hj) hkl hs₁ hM₁ hF

/-- `R = [k]G` for a secret `k`, after the setup and the tables. -/
theorem gMulK_ok (hc : BaseCfgOk c) (hC : Law c.C) (hT : CombTbls c) {hs : Option Nat} {s₀ : State} (hp : Pre c s₀)
    {s : State} (hS : St₁ c hs s₀ (s₀.gpr .r8) s) :
    WP isa c.gMulK s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch (s₀.gpr .r8) (gW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem (s₀.gpr .r8) ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem (s₀.gpr .r8) x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RX)) (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RY))
        (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RZ)) (mul (kv c s₀) (G c.C)) :=
  gMulK_ok' hc hC hT hS.scr hS.fixed (hS.k ▸ wordsVal_lt _ _ _ _) hS.rx hS.ry hS.rz hS.t₀ fun d hcd => by
    rw [hS.syms]; exact tbl_of hcd hp hS.rd hS.unch

end VG.Proof.Ecdsa.X86_64
