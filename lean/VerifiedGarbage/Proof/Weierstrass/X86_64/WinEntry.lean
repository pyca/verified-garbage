import VerifiedGarbage.Proof.Weierstrass.X86_64.Window

/-!
# The window method on x86-64: the entry of a digit

Iteration `j` reads digit `j` as the comb reads its digits (`digit_ok` for
windows of 4 bits: `combWin 4 k j` is `nib k j`), selects the entry of its
magnitude `a` from the table at `rdx = rdi + tbl` (`winSelSetup_ok`) as the
comb selects one (`selLoad_ok`), its `⌈3 n / 2⌉` 16-byte pieces stored to `E`
(the last over the entry's last 16 bytes), so that `E` holds the point `[a]P`'s three coordinates, sets `y = R` for `a = 0`
(`ySel0_ok`, so that `E` is `(0 : 1 : 0)`), and negates `y` for a negative
digit as the comb does (`winEntry_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

theorem combWin_four (k i : Nat) : combWin 4 k i = nib k i := by
  unfold combWin nib; rw [Nat.pow_mul]

/-- `rdx = rdi + tbl`. -/
theorem winSelSetup_ok (K : WinCfg) (s : State) {base : Addr} (hd : s.gpr .rdi = base)
    (ht : K.tbl < 2 ^ 31) :
    WP isa (.block (WinCfg.selSetup K)) s fun t => t.gpr .rdx = base + BitVec.ofNat 64 K.tbl ∧
      Keeps [.rdx] s t ∧ t.xmm = s.xmm := by
  crun [WinCfg.selSetup, imm32_sext ht, hd, RegUpd.xmm_setReg, RegUpd.xmm_arithFlags]
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `y |= R` if the magnitude `r8 = a` is zero, word by word. -/
theorem ySel0_ok (K : WinCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (ha : a < 2 ^ 64) (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (hy : K.E.y + 8 * K.M.n ≤ size) :
    WP isa (.block (WinCfg.ySel0 K)) s fun t =>
      (∀ i < K.M.n, word t.mem base (K.E.y + 8 * i) =
        (wordOf K.one i &&& bmask (decide (a = 0))) ||| word s.mem base (K.E.y + 8 * i)) ∧
      KeepRegs [.rax, .rcx] s t ∧ Outside base K.E.y (8 * K.M.n) s.mem t.mem := by
  unfold WinCfg.ySel0
  rw [WP.block_append_iff]
  refine WP.mono (isZero_ok s ha h8) fun s₁ ⟨c₁, k₁, _⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (orSteps_ok K.M.n s₁ hs₁ c₁ hy) fun t ⟨e₂, k₂, O₂, _⟩ =>
    ⟨fun i hi => by rw [e₂ i hi, k₁.2.1], ((Keeps.regs k₁).mono (by decide)).trans (k₂.mono (by decide)),
      by rw [← k₁.2.1]; exact O₂⟩

/-- A change within `[o, o + 3 k)`, as within its three thirds. -/
theorem Unch.split3 {base : Addr} {o k : Nat} {m m' : Mem} (h : Unch base [(o, 3 * k)] m m') :
    Unch base [(o, k), (o + k, k), (o + 2 * k, k)] m m' := fun x hx => h x fun w hw => by
  simp only [List.mem_singleton] at hw; subst hw
  have h1 := hx _ (List.mem_cons_self ..)
  have h2 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have h3 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  dsimp only at h1 h2 h3 ⊢; omega

/-- What the selection leaves: in `E`, entry `a`'s coordinates if `a ≥ 1`,
else `(0, R, 0)`. -/
structure WinSelPost (K : WinCfg) (base : Addr) (s : State) (a : Nat) (t : State) : Prop where
  x : wordsVal t.mem base K.E.x K.M.n = if 1 ≤ a then wordsVal s.mem base (K.tblPt a).x K.M.n else 0
  y : wordsVal t.mem base K.E.y K.M.n = if 1 ≤ a then wordsVal s.mem base (K.tblPt a).y K.M.n else K.one
  z : wordsVal t.mem base K.E.z K.M.n = if 1 ≤ a then wordsVal s.mem base (K.tblPt a).z K.M.n else 0
  keep : KeepRegs [.rax, .rcx, .rdx] s t
  unch : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s.mem t.mem

/-- The entry of the magnitude `r8 = a ≤ 8` into `E`. -/
theorem winSelect_ok (K : WinCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hn : 1 ≤ K.M.n ∧ K.M.n ≤ 9) (ht : K.tbl < 2 ^ 31)
    (htb : K.tbl + 192 * K.M.n ≤ size) (hexy : K.E.y = K.E.x + 8 * K.M.n)
    (hexz : K.E.z = K.E.x + 16 * K.M.n) (hz : K.E.z + 8 * K.M.n ≤ size) (hone : K.one < 2 ^ (64 * K.M.n))
    {a : Nat} (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (ha : a ≤ 8) :
    WP isa (.block (WinCfg.select K)) s (WinSelPost K base s a) := by
  have hnw := hs.nowrap
  have hnp : WinCfg.np K = (3 * K.M.n + 1) / 2 := rfl
  have hpo : ∀ c, WinCfg.po K c = if c + 1 < WinCfg.np K then 16 * c else 24 * K.M.n - 16 := fun _ => rfl
  have hpo16 : ∀ c < WinCfg.np K, WinCfg.po K c + 16 ≤ 24 * K.M.n := fun c hc => by
    rw [hpo]; rw [hnp] at hc ⊢; split <;> omega
  have hlast : WinCfg.po K (WinCfg.np K - 1) = 24 * K.M.n - 16 := by
    rw [hpo, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  rw [WinCfg.select, List.append_assoc, WP.block_append_iff]
  refine WP.mono (winSelSetup_ok K s hs.rdi ht) fun s₁ ⟨x₁, k₁, _⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have h8₁ : s₁.gpr .r8 = BitVec.ofNat 64 a := by rw [k₁.1 _ (by decide), h8]
  rw [WP.block_append_iff, selPassAt, WP.block_append_iff]
  -- Every piece is within its entry, and the entries within the table.
  have hr : ∀ e < 8, ∀ c < WinCfg.np K, InRegions (s₁.rd ++ s₁.wr)
      (base + BitVec.ofNat 64 K.tbl + BitVec.ofNat 64 (24 * K.M.n * e + WinCfg.po K c)) 16 := by
    intro e he c hc
    rw [Offset.add_add]
    have := hpo16 c hc
    have := Nat.mul_le_mul_left (24 * K.M.n) (show e + 1 ≤ 8 by omega)
    rw [Nat.mul_succ] at this
    exact ⟨_, List.mem_append_right _ (k₁.2.2.2 ▸ hs.wr), hs.contains (by omega) (by decide)⟩
  refine WP.mono (selLoad_ok (st := 24 * K.M.n) (H := 8) (by rw [hnp]; omega) (by decide) (by omega)
    h8₁ x₁ hr) fun s₂l ⟨a₂, k₂l, m₂l⟩ => ?_
  have hs₂l : Scr s₂l base size := hs₁.of_keepRegs k₂l (by decide)
  -- The pieces but the last are `16` bytes apart; the last ends the entry.
  rw [show WinCfg.np K = (WinCfg.np K - 1) + 1 by rw [hnp]; omega, List.range_succ, List.map_append,
    List.map_singleton, WP.block_append_iff,
    List.map_congr_left (l := List.range (WinCfg.np K - 1))
      (g := fun c => Instr.movdquStore (sc (K.E.x + 16 * c)) (selAcc c)) fun c hc => by
        rw [List.mem_range] at hc; rw [hpo, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]]
  refine WP.mono (storeAcc_ok (o := K.E.x) (WinCfg.np K - 1) s₂l hs₂l (by rw [hnp]; omega))
    fun s₂f ⟨a₃, O₃f, g₃, r₃, w₃, x₃⟩ => ?_
  have hs₂f : Scr s₂f base size := ⟨by rw [g₃]; exact hs₂l.rdi, by rw [w₃]; exact hs₂l.wr, hnw⟩
  refine WP.mono (store128_ok (d := K.E.x + WinCfg.po K (WinCfg.np K - 1)) s₂f hs₂f
    (by rw [hlast]; omega) _) fun s₂ ⟨a₄, O₄, g₄, r₄, w₄, x₄⟩ => ?_
  have k₂ : KeepRegs [.rcx] s₁ s₂ :=
    ⟨fun r hr => by rw [g₄, g₃, k₂l.gpr r hr], by rw [r₄, r₃, k₂l.rd], by rw [w₄, w₃, k₂l.wr]⟩
  have O₂ : Outside base K.E.x (24 * K.M.n) s₁.mem s₂.mem := by
    rw [← m₂l]
    exact (O₃f.mono (Nat.le_refl _) (by rw [hnp]; omega)).trans (O₄.mono (by omega) (by rw [hlast]; omega))
  have hs₂ : Scr s₂ base size := hs₁.of_keepRegs k₂ (by decide)
  have h8₂ : s₂.gpr .r8 = BitVec.ofNat 64 a := by rw [k₂.gpr _ (by decide), h8₁]
  refine WP.mono (ySel0_ok K hs₂ (by omega) h8₂ (by omega)) fun t ⟨ey, k₃, O₃⟩ => ?_
  have hX : ∀ d, word s.mem (base + BitVec.ofNat 64 K.tbl) d = word s.mem base (K.tbl + d) := fun d => by
    rw [Mont.word, Mont.word, off, off, Offset.add_add]
  -- The words of `E`, from the table at `s`.
  have hW : ∀ i < 3 * K.M.n, word s₂.mem base (K.E.x + 8 * i) =
      if 1 ≤ a ∧ a ≤ 8 then word s.mem base (K.tbl + 24 * K.M.n * (a - 1) + 8 * i) else 0 := by
    intro i hi
    have e₂ : ∀ c < WinCfg.np K, s₂l.xmm (selAcc c) =
        accVal s.mem (base + BitVec.ofNat 64 K.tbl) (24 * K.M.n) (WinCfg.po K) a 8 c := fun c hc => by
      rw [a₂ c hc, k₁.2.1]
    by_cases hi2 : 3 * K.M.n - 2 ≤ i
    · have h := a₄
      rw [x₃, e₂ _ (by rw [hnp]; omega)] at h
      have w := accVal_word1 (q := i - (3 * K.M.n - 2)) h (by omega)
      rw [hlast, show K.E.x + (24 * K.M.n - 16) + 8 * (i - (3 * K.M.n - 2)) = K.E.x + 8 * i by omega,
        hX] at w
      rw [w, show K.tbl + (24 * K.M.n * (a - 1) + (24 * K.M.n - 16) + 8 * (i - (3 * K.M.n - 2))) =
        K.tbl + 24 * K.M.n * (a - 1) + 8 * i by omega]
    · have hc : i / 2 + 1 < WinCfg.np K := by rw [hnp]; omega
      have h := a₃ (i / 2) (by omega)
      rw [e₂ _ (by omega)] at h
      have w := accVal_word1 (q := i % 2) h (Nat.mod_lt _ (by decide))
      rw [hpo, ite_eq_left_of_eq_true _ _ (eq_true hc), show K.E.x + 16 * (i / 2) + 8 * (i % 2) = K.E.x + 8 * i by omega, hX] at w
      rw [O₄.word (by rw [hlast]; omega) (by omega), w,
        show K.tbl + (24 * K.M.n * (a - 1) + 16 * (i / 2) + 8 * (i % 2)) =
          K.tbl + 24 * K.M.n * (a - 1) + 8 * i by omega]
  have hxw : ∀ i < K.M.n, word t.mem base (K.E.x + 8 * i) = word s₂.mem base (K.E.x + 8 * i) := fun i hi =>
    O₃.word (by omega) (by omega)
  have hzw : ∀ i < K.M.n, word t.mem base (K.E.z + 8 * i) = word s₂.mem base (K.E.z + 8 * i) := fun i hi =>
    O₃.word (by omega) (by omega)
  have tx : (K.tblPt a).x = K.tbl + 24 * K.M.n * (a - 1) := rfl
  have ty : (K.tblPt a).y = K.tbl + 24 * K.M.n * (a - 1) + 8 * K.M.n := rfl
  have tz : (K.tblPt a).z = K.tbl + 24 * K.M.n * (a - 1) + 16 * K.M.n := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), tx]
      exact wordsVal_congr₂ _ _ _ fun i hi => by
        rw [hxw i hi, hW i (by omega), ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact wordsVal_zeros fun i hi => by
        rw [hxw i hi, hW i (by omega), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · have hyw : ∀ i < K.M.n, word s₂.mem base (K.E.y + 8 * i) =
        if 1 ≤ a ∧ a ≤ 8 then word s.mem base (K.tbl + 24 * K.M.n * (a - 1) + 8 * K.M.n + 8 * i) else 0 :=
      fun i hi => by
        rw [hexy, show K.E.x + 8 * K.M.n + 8 * i = K.E.x + 8 * (K.M.n + i) by omega, hW _ (by omega),
          show K.tbl + 24 * K.M.n * (a - 1) + 8 * (K.M.n + i) =
            K.tbl + 24 * K.M.n * (a - 1) + 8 * K.M.n + 8 * i by omega]
    by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ty]
      exact wordsVal_congr₂ _ _ _ fun i hi => by
        rw [ey i hi, hyw i hi, ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩),
          decide_eq_false (show ¬ a = 0 by omega), bv_and_or_false]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact wordsVal_wordOf hone fun i hi => by
        rw [ey i hi, hyw i hi, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
          decide_eq_true (show a = 0 by omega), bv_and_or_true, bv_or_zero]
  · have hzw' : ∀ i < K.M.n, word s₂.mem base (K.E.z + 8 * i) =
        if 1 ≤ a ∧ a ≤ 8 then word s.mem base (K.tbl + 24 * K.M.n * (a - 1) + 16 * K.M.n + 8 * i) else 0 :=
      fun i hi => by
        rw [hexz, show K.E.x + 16 * K.M.n + 8 * i = K.E.x + 8 * (2 * K.M.n + i) by omega, hW _ (by omega),
          show K.tbl + 24 * K.M.n * (a - 1) + 8 * (2 * K.M.n + i) =
            K.tbl + 24 * K.M.n * (a - 1) + 16 * K.M.n + 8 * i by omega]
    by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), tz]
      exact wordsVal_congr₂ _ _ _ fun i hi => by
        rw [hzw i hi, hzw' i hi, ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact wordsVal_zeros fun i hi => by
        rw [hzw i hi, hzw' i hi, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · exact ((Keeps.regs k₁).mono (by decide)).trans ((k₂.mono (by decide)).trans (k₃.mono (by decide)))
  · rw [← k₁.2.1]
    have U₂ : Unch base [(K.E.x, 3 * (8 * K.M.n))] s₁.mem s₂.mem := by
      have := O₂.unch
      rwa [show 24 * K.M.n = 3 * (8 * K.M.n) by omega] at this
    refine ((Unch.split3 U₂).trans O₃.unch).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with (rfl | rfl | rfl) | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (Prod.ext (by dsimp only; omega) rfl))
    · exact Or.inr (Or.inr (Prod.ext (by dsimp only; omega) rfl))
    · exact Or.inr (Or.inl rfl)

/-- After the selection and the negation: `E` represents the point of digit
`i` (by `Rp`), and only `E`, `-y` and the temporary area changed. -/
structure EntryPostR (K : WinCfg) (C : Curve) (base : Addr) (size : Nat)
    (Rp : Fe C → Fe C → Fe C → Point C → Prop) (P : Point C) (k i : Nat)
    (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob K.M.n) s s'
  unch : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n),
    (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)] s.mem s'.mem
  lt : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s'.mem base x K.M.n < C.p
  rep : Rp (tmv C K.M.n base s' K.E.x) (tmv C K.M.n base s' K.E.y) (tmv C K.M.n base s' K.E.z)
    (winPt C P k i)

/-- `EntryPostR` in projective coordinates. -/
abbrev EntryPostW (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (k i : Nat)
    (s s' : State) : Prop := EntryPostR K C base size (Rep C) P k i s s'

theorem winE_mem {K : WinCfg} : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x ∈ winOther K := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> win_mem

theorem mul_zero_pt' {C : Curve} (P : Point C) : mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; simp

/-- The layout facts the entry needs: `E`'s three slots adjacent, the table's
address an immediate, and at most nine words (the selection keeps an entry's
16-byte pieces in fourteen registers). -/
structure WinX (K : WinCfg) (size : Nat) : Prop where
  n : 1 ≤ K.M.n ∧ K.M.n ≤ 9
  tbl : K.tbl < 2 ^ 31
  exy : K.E.y = K.E.x + 8 * K.M.n
  exz : K.E.z = K.E.x + 16 * K.M.n

/-- The digit's magnitude, its entry from the table, and its `y` negated for a
negative digit. -/
theorem winEntryR_ok {K : WinCfg} {C : Curve} {base : Addr} {size k i : Nat} (hL : WinLay K size)
    (hX : WinX K size) {Rp : Fe C → Fe C → Fe C → Point C → Prop} (hRp0 : Rp 0 1 0 .infinity)
    (hRpNeg : ∀ {X Y Z : Fe C} {Q : Point C}, Rp X Y Z Q → Rp X (-Y) Z (negPt Q))
    {P : Point C} (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base) (hi : i < K.J) (hx : s.gpr .rbx = BitVec.ofNat 64 i)
    (hbits : ∀ t < 4 * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hz : wordsVal s.mem base K.zero K.M.n = 0) (hT : TblOkR K C base Rp P 8 s) :
    WP isa (.block ((WinCfg.tc K).digit ++ WinCfg.select K)) s fun s₂ =>
      WP isa (.block (WinCfg.tc K).negY) s₂ (EntryPostR K C base size Rp P k i s) := by
  have hn := hs.nowrap
  have hJ := hL.J
  have h0 := hL.n0
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hone_lt
  obtain ⟨-, -, -, -, exy, exz, eyz, hEo, -, -⟩ := hL.other_ne
  have wE : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x ∈ winWs K := fun x hx => winOther_ws K x (winE_mem x hx)
  have le : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x + 8 * K.M.n ≤ size := fun x hx =>
    hL.lay.le x (winOther_mem (winE_mem x hx))
  have tmp : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x + 8 * K.M.n ≤ K.M.tmp ∨ K.M.tmp + 8 * K.M.n ≤ x :=
    fun x hx => hL.lay.tmp x (winOther_mem (winE_mem x hx))
  have mo : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x + 8 * K.M.n ≤ K.M.mo ∨ K.M.mo + 8 * K.M.n ≤ x :=
    fun x hx => hL.lay.mo x (winOther_mem (winE_mem x hx))
  have neN : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ≠ K.neg := fun x hx e => hEo x hx (by rw [e]; simp)
  have yneg := hL.apart₂ (wE K.E.y (by simp)) (wE K.neg (by simp)) (neN _ (by simp))
  have xneg := hL.apart₂ (wE K.E.x (by simp)) (wE K.neg (by simp)) (neN _ (by simp))
  have zneg := hL.apart₂ (wE K.E.z (by simp)) (wE K.neg (by simp)) (neN _ (by simp))
  have xy := hL.apart₂ (wE K.E.x (by simp)) (wE K.E.y (by simp)) exy
  have xz := hL.apart₂ (wE K.E.x (by simp)) (wE K.E.z (by simp)) exz
  have yz := hL.apart₂ (wE K.E.y (by simp)) (wE K.E.z (by simp)) eyz
  have hbs := hL.bits
  have hEx := le K.E.x (by simp)
  have hEy := le K.E.y (by simp)
  have hEz := le K.E.z (by simp)
  have hneg := le K.neg (by simp)
  have hzs : K.zero ∈ winSlots K := winRo_slots K _ (by simp [winRo])
  have hzl := hL.lay.le K.zero hzs
  -- The table's last slot bounds it.
  have htb : K.tbl + 192 * K.M.n ≤ size := by
    have := hL.lay.le _ (show K.tbl + 8 * K.M.n * 23 ∈ winSlots K by
      simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K (by decide)))
    omega
  have hwi : 4 * i + 4 ≤ 4 * K.J := by omega
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok (WinCfg.tc K) hs (k := k) (j := i) (N := 4 * K.J) (by show 1 ≤ 4; decide)
    (by show 4 < 9; decide) hwi
    hL.bits hx hbits) fun s₁ ⟨_, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hx₁ : s₁.gpr .rbx = BitVec.ofNat 64 i := by rw [k₁.1 _ (by decide), hx]
  have hw4 : combWin 4 k i = nib k i := combWin_four k i
  have hmag : magH 8 (nib k i) ≤ 8 := magH_le (by have := nib_lt k i; omega)
  have m₁' : s₁.gpr .r8 = BitVec.ofNat 64 (magH 8 (nib k i)) := by
    rw [m₁, show (WinCfg.tc K).H = 8 from rfl, show (WinCfg.tc K).w = 4 from rfl, hw4]
  refine WP.mono (winSelect_ok K hs₁ hX.n hX.tbl htb hX.exy hX.exz hEz (Nat.lt_trans hone_lt hpn) m₁' hmag)
    fun s₂ S₂ => ?_
  obtain ⟨ex₂, ey₂, ez₂, k₂, U₂⟩ := S₂
  rw [k₁.2.1] at ex₂ ey₂ ez₂ U₂
  generalize ha : magH 8 (nib k i) = a at ex₂ ey₂ ez₂ hmag
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have hmoE : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)],
      K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · have := mo K.E.x (by simp); dsimp only; omega
    · have := mo K.E.y (by simp); dsimp only; omega
    · have := mo K.E.z (by simp); dsimp only; omega
  have hM₂ : ModOkW K.M size C.p s₂.mem base := hM.unch U₂ hmoE hn
  have hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by
    have hzW := hL.ro_w (x := K.zero) (by simp [winRo])
    rw [U₂.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;>
        exact hzW _ (List.mem_append_left _ (List.mem_map_of_mem (wE _ (by simp))))) (by omega), hz]
  -- The entry's numbers, below `p`.
  have Ta := fun (h : 1 ≤ a) => hT a h hmag
  have hEy₂ : wordsVal s₂.mem base K.E.y K.M.n < C.p := by
    rw [ey₂]; split
    · exact (Ta ‹_›).1 _ (by simp)
    · exact hone_lt
  -- The negation.
  rw [TCombCfg.negY, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sub_ok hs₂ hM₂ (o := K.neg) (a := K.zero) (b := K.E.y) hneg hzl hEy
    (tmp _ (by simp)) (hL.lay.tmp _ hzs) (tmp _ (by simp)) (mo _ (by simp))
    (by rw [hz₂]; exact hp0) hEy₂) fun s₃ ⟨k₃, e₃⟩ => ?_
  have hs₃ : Scr s₃ base size := k₃.scr hs₂
  have U₃ := k₃.unch
  have hx₃ : s₃.gpr .rbx = BitVec.ofNat 64 i := by
    rw [k₃.gpr _ (rbx_not_clob _), k₂.gpr _ (by decide), hx₁]
  have hbW : ∀ w ∈ winW K, K.bits + 4 * K.J ≤ w.1 ∨ w.1 + w.2 ≤ K.bits := hL.bits_w
  have hbits₃ : ∀ t < 4 * K.J, s₃.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 := by
    intro t ht
    have hW : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], K.bits + 4 * K.J ≤ x ∨ x + 8 * K.M.n ≤ K.bits := fun x hx =>
      hbW _ (List.mem_append_left _ (List.mem_map_of_mem (wE x hx)))
    have hT' := hbW _ (List.mem_append_right _ (List.mem_singleton_self (K.M.tmp, 8 * K.M.n)))
    rw [U₃.byte (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · have := hW K.neg (by simp); dsimp only; omega
        · dsimp only at hT' ⊢; omega) (by omega),
      U₂.byte (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · have := hW K.E.x (by simp); dsimp only; omega
        · have := hW K.E.y (by simp); dsimp only; omega
        · have := hW K.E.z (by simp); dsimp only; omega) (by omega)]
    exact hbits t ht
  rw [WP.block_append_iff]
  refine WP.mono (signMask_ok (WinCfg.tc K) hs₃ (k := k) (j := i) (N := 4 * K.J) (by show 1 ≤ 4; decide)
    (by show 4 < 2 ^ 31; decide) hwi
    hL.bits hx₃ hbits₃) fun s₄ ⟨x₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (sel_ok (decide (combWin (WinCfg.tc K).w k i < 2 ^ ((WinCfg.tc K).w - 1))) K.M.n hs₄ x₄
    (o := K.E.y) (a := K.E.y) (b := K.neg) hEy hEy hneg (Or.inl (Nat.le_refl _)) (by omega))
    fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  rw [show (WinCfg.tc K).w = 4 from rfl, hw4] at e₅
  -- The values.
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  have vx : wordsVal s₅.mem base K.E.x K.M.n = wordsVal s₂.mem base K.E.x K.M.n := by
    rw [O₅.wordsVal (by omega) (by omega), m₄, U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · dsimp only; omega
      · have := tmp K.E.x (by simp); dsimp only; omega) (by omega)]
  have vz : wordsVal s₅.mem base K.E.z K.M.n = wordsVal s₂.mem base K.E.z K.M.n := by
    rw [O₅.wordsVal (by omega) (by omega), m₄, U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · dsimp only; omega
      · have := tmp K.E.z (by simp); dsimp only; omega) (by omega)]
  have vy₃ : wordsVal s₃.mem base K.E.y K.M.n = wordsVal s₂.mem base K.E.y K.M.n :=
    U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · dsimp only; omega
      · have := tmp K.E.y (by simp); dsimp only; omega) (by omega)
  have vy : wordsVal s₅.mem base K.E.y K.M.n = if decide (nib k i < 2 ^ (4 - 1)) then
      (0 + C.p - wordsVal s₂.mem base K.E.y K.M.n) % C.p else wordsVal s₂.mem base K.E.y K.M.n := by
    rw [e₅, m₄, e₃, hz₂, vy₃]
  -- The point the selected entry represents: `[a]P` (`O` for `0`).
  have hR : Rp (tmv C K.M.n base s₂ K.E.x) (tmv C K.M.n base s₂ K.E.y) (tmv C K.M.n base s₂ K.E.z)
      (mul a P) := by
    show Rp (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [ex₂, ey₂, ez₂]
    by_cases h1 : 1 ≤ a
    · simp only [h1, ↓reduceIte]
      exact (Ta h1).2
    · have h0 : a = 0 := by omega
      subst h0
      simp only [show ¬ 1 ≤ 0 by omega, ↓reduceIte, toM_zero, hone, mul_zero_pt']
      exact hRp0
  have hcl : ∀ r ∈ [Reg.rax, .rcx, .rdx, .r8], r ∈ clob K.M.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp [clob]
    · simp [clob]
    · simp [clob]
    · exact r8_mem_clob _
  refine ⟨hs₄.of_keepRegs k₅ (by decide), ?_, ?_, ?_, ?_⟩
  · exact (((((Keeps.regs k₁).mono hcl).trans (k₂.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))).trans
      ⟨k₃.gpr, k₃.rd, k₃.wr⟩).trans ((Keeps.regs k₄).mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))).trans
      (k₅.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]))
  · refine ((U₂.trans (U₃.trans (m₄ ▸ O₅.unch))).mono ?_)
    intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    grind
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vx, ex₂]; split
      · exact (Ta ‹_›).1 _ (by simp)
      · exact hp0
    · rw [vy]; split
      · exact Nat.mod_lt _ hp0
      · exact hEy₂
    · rw [vz, ez₂]; split
      · exact (Ta ‹_›).1 _ (by simp)
      · exact hp0
  · have ex : tmv C K.M.n base s₅ K.E.x = tmv C K.M.n base s₂ K.E.x := by
      show toM _ _ _ = toM _ _ _; rw [vx]
    have ez : tmv C K.M.n base s₅ K.E.z = tmv C K.M.n base s₂ K.E.z := by
      show toM _ _ _ = toM _ _ _; rw [vz]
    rw [ex, ez]
    unfold winPt
    by_cases h8 : 8 ≤ nib k i
    · have hy : tmv C K.M.n base s₅ K.E.y = tmv C K.M.n base s₂ K.E.y := by
        show toM _ _ _ = toM _ _ _
        rw [vy, decide_eq_false (show ¬ nib k i < 2 ^ (4 - 1) by omega)]; rfl
      rw [hy]
      simp only [h8, ↓reduceIte]
      have : a = nib k i - 8 := by rw [← ha, magH]; simp [h8]
      rw [this] at hR
      exact hR
    · have hy : tmv C K.M.n base s₅ K.E.y = -tmv C K.M.n base s₂ K.E.y := by
        show toM _ _ _ = -toM _ _ _
        rw [vy, decide_eq_true (show nib k i < 2 ^ (4 - 1) by omega)]
        simp only [↓reduceIte]
        rw [toM_sub (by omega), toM_zero]
        grind
      rw [hy]
      simp only [h8, ↓reduceIte]
      have : a = 8 - nib k i := by rw [← ha, magH]; simp [h8]
      rw [this] at hR
      exact hRpNeg hR

/-- `winEntryR_ok` in projective coordinates. -/
theorem winEntry_ok {K : WinCfg} {C : Curve} {base : Addr} {size k i : Nat} (hL : WinLay K size)
    (hX : WinX K size) (hC : Law C) {P : Point C} (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base) (hi : i < K.J) (hx : s.gpr .rbx = BitVec.ofNat 64 i)
    (hbits : ∀ t < 4 * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hz : wordsVal s.mem base K.zero K.M.n = 0) (hT : TblOk K C base P 8 s) :
    WP isa (.block ((WinCfg.tc K).digit ++ WinCfg.select K)) s fun s₂ =>
      WP isa (.block (WinCfg.tc K).negY) s₂ (EntryPostW K C base size P k i s) :=
  winEntryR_ok hL hX (rep_infinity' hC) Rep.negY hpn hone_lt hone hs hM hi hx hbits hz hT

end VG.Proof.Weierstrass.X86_64
