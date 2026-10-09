import VerifiedGarbage.Proof.Rsa.X86_64.Div

/-!
# RSA private keys on x86-64: the binary extended Euclidean algorithm

`invStep`, one step of `inverse`, is `KeyMath.invStep` on the arrays
(`invStepCode_ok`): `u`, `v`, `x₁` and `x₂` (`w` words each), while
`x₁, x₂ < m` and the word `w` of `u` is zero. Its parts: the masks and the
swaps (`invSwap_ok`), the subtractions (`invSub_ok`) and the halvings
(`invHalf_ok`). `inverse` is `KeyMath.invIter` for `128 w` steps from
`(a, m, 1, 0)` (`inverse_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem mask_and' (a b : Bool) : mask a &&& mask b = mask (a && b) := by
  cases a <;> cases b <;> rfl

/-- The mask of a word's low bit. -/
theorem mask_low (x : BitVec 64) : BitVec.setWidth 64 (0 : BitVec 32) - (x &&& 1) =
    mask (decide (x.toNat % 2 = 1)) := by
  have h2 : x &&& 1 = BitVec.ofNat 64 (x.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat]
    omega_arith
  rw [h2]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

/-- The masks and the swaps: `(u, v, x₁, x₂)` swapped to `(v, u, x₂, x₁)`
if `u` is odd and below `v`, and the mask of `u` odd in `sMo`. -/
theorem invSwap_ok {s : State} {B : Addr} {Z w : Nat} {iU iV iX₁ iX₂ : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z)
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (dUV : iU ≠ iV) (dX : iX₁ ≠ iX₂)
    (d₁ : iU ≠ iX₁) (d₂ : iU ≠ iX₂) (d₃ : iV ≠ iX₁) (d₄ : iV ≠ iX₂) {u v x₁ x₂ : Nat} {sw : Bool}
    (hu : wv s.mem B (slot w iU) w = u) (hv : wv s.mem B (slot w iV) w = v)
    (hx₁ : wv s.mem B (slot w iX₁) w = x₁) (hx₂ : wv s.mem B (slot w iX₂) w = x₂)
    (hsw : sw = (decide (u % 2 = 1) && decide (u < v))) :
    WP isa (seqs (invSwapP iU iV iX₁ iX₂)) s fun t =>
      word t.mem B (8 * sMo) = mask (decide (u % 2 = 1)) ∧
      wv t.mem B (slot w iU) w = (if sw then v else u) ∧ wv t.mem B (slot w iV) w = (if sw then u else v) ∧
      wv t.mem B (slot w iX₁) w = (if sw then x₂ else x₁) ∧ wv t.mem B (slot w iX₂) w = (if sw then x₁ else x₂) ∧
      Frm B [(slot w iU, 8 * w), (slot w iV, 8 * w), (slot w iX₁, 8 * w), (slot w iX₂, 8 * w), (8 * sMo, 8)]
        s.mem t.mem ∧
      Keep [.rax, .rbx, .rdx, .rbp, .r10, .r14, .r15] s t := by
  have hn := hs.nowrap
  have sU := Nat.le_trans (slot_lt (w := w) hU) hZ
  have sV := Nat.le_trans (slot_lt (w := w) hV) hZ
  have sX₁ := Nat.le_trans (slot_lt (w := w) hX₁) hZ
  have sX₂ := Nat.le_trans (slot_lt (w := w) hX₂) hZ
  have pUV := slot_sep (w := w) dUV
  have pX := slot_sep (w := w) dX
  have p₁ := slot_sep (w := w) d₁
  have p₂ := slot_sep (w := w) d₂
  have p₃ := slot_sep (w := w) d₃
  have p₄ := slot_sep (w := w) d₄
  have hU0 := hdr_lt_slot w iU (show sMo < 32 by decide)
  have hX0 := hdr_lt_slot w iX₁ (show sMo < 32 by decide)
  have hX0' := hdr_lt_slot w iX₂ (show sMo < 32 by decide)
  have hV0 := hdr_lt_slot w iV (show sMo < 32 by decide)
  have eMo : sMo = 29 := rfl
  simp only [invSwapP, seqs, List.append_assoc]
  -- `rbx := U`, the mask of `u` odd into `sMo`, `r10 := V`, `rbp := 0`.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (base_ok iU (r := .rbx) (by decide) hdi h9)
    fun s₁ ⟨hbx, m₁, k₁⟩ => WP.block_append_iff.mpr (WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
      t.mem = s₁.mem.writeW (off B (8 * sMo)) (mask (decide (u % 2 = 1)))) (by
        have hs₁ := hs.congr k₁.2.2
        have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
        have e0 : (s₁.mem.readW (off B (slot w iU)) 64).toNat % 2 = u % 2 := by
          rw [m₁, ← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide), hu]
        xrun [State.ea, at0, hdr, hbx, hdi₁, hdrOff, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
          hs₁.ld (d := slot w iU) (by omega_arith), hs₁.st (d := 8 * sMo) (by omega_arith), mask_low, e0]) rfl)
      fun s₂ ⟨m₂, k₂⟩ => WP.block_append_iff.mpr (WP.mono (base_ok iV (r := .r10) (by decide)
        (((k₁.trans k₂).gpr (by decide)).trans hdi) (((k₁.trans k₂).gpr (by decide)).trans h9))
        fun s₃ ⟨h10, m₃, k₃⟩ => WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask false ∧ t.mem = s₃.mem)
          (by xrun) rfl) fun s₄ ⟨⟨hbp, m₄⟩, k₄⟩ => ?_))))
  have k04 := ((k₁.trans k₂).trans k₃).trans k₄
  have hm₄ : s₄.mem = s.mem.writeW (off B (8 * sMo)) (mask (decide (u % 2 = 1))) := by rw [m₄, m₃, m₂, m₁]
  have o₄ := writeW_outside s.mem B (mask (decide (u % 2 = 1))) (d := 8 * sMo) (by omega_arith)
  have eU : wv s₄.mem B (slot w iU) w = u := by
    rw [hm₄]
    exact (o₄.wv (Or.inr hU0) (by omega_arith)).trans hu
  have eV : wv s₄.mem B (slot w iV) w = v := by
    rw [hm₄]
    exact (o₄.wv (Or.inr hV0) (by omega_arith)).trans hv
  have hs₄ := hs.congr k04.2.2
  -- `rbp := ` the mask of `u < v`.
  refine WP.seq (WP.mono (cmpLoop_ok hs₄ ((k₂.trans k₃).trans k₄ |>.gpr (by decide) |>.trans hbx)
    ((k₄.gpr (by decide)).trans h10) ((k04.gpr (by decide)).trans h12) hbp hw1 (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₅ ⟨hbp₅, m₅, k₅⟩ => ?_)
  rw [eU, eV] at hbp₅
  -- `r15 := ` the swap's mask.
  have hl : InRegions (s₅.rd ++ s₅.wr) (off B (8 * sMo)) 8 := (hs.congr (k04.trans k₅).2.2).ld (by omega_arith)
  have hdi₅ : s₅.gpr .rdi = B := ((k04.trans k₅).gpr (by decide)).trans hdi
  have hmo₅ : word s₅.mem B (8 * sMo) = mask (decide (u % 2 = 1)) := by rw [m₅, hm₄, word_writeW_self]
  refine WP.seq (WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = mask sw ∧ t.mem = s₅.mem) (by
    xrun [State.ea, hdr, hdi₅, hdrOff, hl, hbp₅, hmo₅, mask_and']
    rw [hsw, Bool.and_comm]) rfl) fun s₆ ⟨⟨h15, m₆⟩, k₆⟩ => ?_)
  have k06 := (k04.trans k₅).trans k₆
  -- The swap of `U` and `V`.
  refine WP.seq (WP.mono (cswap_ok (hs.congr k06.2.2) ((k₂.trans k₃ |>.trans k₄ |>.trans k₅ |>.trans k₆).gpr
    (by decide) |>.trans hbx) ((k₄.trans k₅ |>.trans k₆).gpr (by decide) |>.trans h10) h15
    ((k06.gpr (by decide)).trans h12) hw1 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₇ ⟨hU₇, hV₇, f₇, k₇⟩ => ?_)
  have k07 := k06.trans k₇
  rw [m₆, m₅, eU, eV] at hU₇ hV₇
  -- The bases of `X₁` and `X₂`.
  refine WP.seq (WP.mono (Q := fun (t : State) => t.gpr .rbx = off B (slot w iX₁) ∧ t.gpr .r10 = off B (slot w iX₂) ∧
      t.mem = s₇.mem ∧ Keep [.rbx, .r10] s₇ t) ?_ fun t h => ?_)
  · rw [WP.block_append_iff]
    refine WP.mono (base_ok iX₁ (r := .rbx) (by decide) ((k07.gpr (by decide)).trans hdi)
      ((k07.gpr (by decide)).trans h9)) fun t₁ ⟨e₁, n₁, j₁⟩ => WP.mono (base_ok iX₂ (r := .r10) (by decide)
        (((k07.trans j₁).gpr (by decide)).trans hdi) (((k07.trans j₁).gpr (by decide)).trans h9))
        fun t₂ ⟨e₂, n₂, j₂⟩ => ⟨(j₂.gpr (by decide)).trans e₁, e₂, n₂.trans n₁, (j₁.trans j₂).mono (by decide)⟩
  obtain ⟨hbx₈, h10₈, m₈, k₈⟩ := h
  -- The swap of `X₁` and `X₂`.
  refine WP.mono (cswap_ok (hs.congr (k07.trans k₈).2.2) hbx₈ h10₈ ((k₇.trans k₈).gpr (by decide) |>.trans h15)
    (((k07.trans k₈).gpr (by decide)).trans h12) hw1 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t ⟨hX₁t, hX₂t, f₉, k₉⟩ => ?_
  rw [m₈] at hX₁t hX₂t f₉
  -- What the swap of `U` and `V` left of `X₁` and `X₂`.
  have fx : ∀ i, i = iX₁ ∨ i = iX₂ → wv s₇.mem B (slot w i) w = wv s.mem B (slot w i) w := by
    intro i hi
    have hi' : i < 16 := by rcases hi with rfl | rfl <;> with_reducible assumption
    have hsep : ∀ r ∈ [(slot w iU, 8 * w), (slot w iV, 8 * w)], slot w i + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w i := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> rcases hi with rfl | rfl <;> omega_arith
    rw [f₇.wv_eq hsep (by have := Nat.le_trans (slot_lt (w := w) hi') hZ; omega_arith), m₆, m₅, hm₄]
    exact o₄.wv (by have := hdr_lt_slot w i (show sMo < 32 by decide); omega_arith)
      (by have := Nat.le_trans (slot_lt (w := w) hi') hZ; omega_arith)
  have hUt : ∀ i, i = iU ∨ i = iV → wv t.mem B (slot w i) w = wv s₇.mem B (slot w i) w := by
    intro i hi
    have hi' : i < 16 := by rcases hi with rfl | rfl <;> with_reducible assumption
    exact f₉.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> rcases hi with rfl | rfl <;> omega_arith)
      (by have := Nat.le_trans (slot_lt (w := w) hi') hZ; omega_arith)
  refine ⟨?_, by rw [hUt iU (.inl rfl)]; exact hU₇, by rw [hUt iV (.inr rfl)]; exact hV₇,
    by rw [hX₁t, fx iX₁ (.inl rfl), fx iX₂ (.inr rfl), hx₁, hx₂],
    by rw [hX₂t, fx iX₁ (.inl rfl), fx iX₂ (.inr rfl), hx₁, hx₂], ?_, ((k07.trans k₈).trans k₉).mono (by decide)⟩
  · have e₁ : word t.mem B (8 * sMo) = word s₇.mem B (8 * sMo) :=
      f₉.word_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
    have e₂ : word s₇.mem B (8 * sMo) = word s₆.mem B (8 * sMo) :=
      f₇.word_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
    rw [e₁, e₂, m₆, hmo₅]
  · intro x hx
    have a := hx (slot w iU, 8 * w) (by simp)
    have b := hx (slot w iV, 8 * w) (by simp)
    have c := hx (slot w iX₁, 8 * w) (by simp)
    have d := hx (slot w iX₂, 8 * w) (by simp)
    have e := hx (8 * sMo, 8) (by simp)
    dsimp only at a b c d e
    rw [f₉ x (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> with_reducible assumption),
      f₇ x (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> with_reducible assumption),
      m₆, m₅, hm₄, writeW_outside s.mem B _ (by omega_arith) x (by omega_arith)]

/-- Three distinct arrays among sixteen are apart. -/
theorem slot_far {w i j : Nat} (h : i ≠ j) : slot w i + 8 * (w + 2) ≤ slot w j ∨ slot w j + 8 * (w + 2) ≤ slot w i :=
  slot_sep h

/-- `u -= v` if `u` is odd (the mask in `sMo`), leaving the mask in `r15`. -/
theorem invSubU_ok {s : State} {B : Addr} {Z w : Nat} {iU iV : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) (hU : iU < 16) (hV : iV < 16) (dUV : iU ≠ iV)
    {odd : Bool} (hmo : word s.mem B (8 * sMo) = mask odd) :
    WP isa (seqs (invSubUP iU iV)) s fun t =>
      wv t.mem B (slot w iU) w + (if odd then wv s.mem B (slot w iV) w else 0) =
        wv s.mem B (slot w iU) w + 2 ^ (64 * w) * (if odd ∧ wv s.mem B (slot w iU) w < wv s.mem B (slot w iV) w
          then 1 else 0) ∧
      t.gpr .r15 = mask odd ∧ Outside B (slot w iU) (8 * w) s.mem t.mem ∧
      Keep [.rax, .rdx, .rsi, .rbp, .r8, .r10, .r14, .r15] s t := by
  have hn := hs.nowrap
  have sU := Nat.le_trans (slot_lt (w := w) hU) hZ
  have sV := Nat.le_trans (slot_lt (w := w) hV) hZ
  have p1 := slot_far (w := w) dUV
  have hmo0 := hdr_lt_slot w 0 (show sMo < 32 by decide)
  have hmo1 := Nat.le_trans (slot_lt (w := w) (show 0 < 16 by decide)) hZ
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sMo)) 8 := hs.ld (by omega_arith)
  simp only [invSubUP, seqs, List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.r15, .rbp] (Q := fun t => t.gpr .r15 = mask odd ∧
      t.gpr .rbp = mask false ∧ t.mem = s.mem) (by xrun [State.ea, hdr, hdi, hdrOff, hl, hmo]) rfl)
    fun s₀ ⟨⟨h15₀, hbp₀, m₀⟩, k₀⟩ => WP.mono (base3_ok iU iV iU (r₁ := .r8) (r₂ := .r10) (r₃ := .rsi) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) ((k₀.gpr (by decide)).trans hdi)
      ((k₀.gpr (by decide)).trans h9) (by decide) (by decide)) fun s₁ ⟨h8, h10, hsi, m₁, k₁⟩ => ?_))
  have k01 := k₀.trans k₁
  refine WP.mono (subM_ok (hs.congr k01.2.2) hsi h8 h10 ((k₁.gpr (by decide)).trans h15₀)
    ((k01.gpr (by decide)).trans h12) ((k₁.gpr (by decide)).trans hbp₀) hw1 (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (Or.inl (Nat.le_refl _)) (by omega_arith)) fun t ⟨b₁, _, hv, o, k₂⟩ => ?_
  rw [m₁, m₀] at hv o
  have u2 := wv_lt t.mem B (slot w iU) w
  have v0 := wv_lt s.mem B (slot w iV) w
  have u0 := wv_lt s.mem B (slot w iU) w
  have hb1 := Bool.toNat_le b₁
  refine ⟨?_, (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h15₀), o, (k01.trans k₂).mono (by decide)⟩
  cases odd <;> simp only [Bool.false_eq_true, ite_false, ite_true, false_and, true_and] at hv ⊢
  · cases b₁ <;> simp only [Bool.toNat_false, Bool.toNat_true] at hv <;> omega_arith
  · split <;> rename_i h <;> cases b₁ <;> simp only [Bool.toNat_false, Bool.toNat_true] at hv <;> omega_arith

/-- `x₁ := x₁ - x₂ mod m` if `u` is odd (the mask in `r15`). -/
theorem invSubX_ok {s : State} {B : Addr} {Z w : Nat} {iX₁ iX₂ iM iT : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z)
    (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT)
    {odd : Bool} (h15 : s.gpr .r15 = mask odd) :
    WP isa (seqs (invSubXP iX₁ iX₂ iM iT)) s fun t =>
      (wv s.mem B (slot w iX₁) w < wv s.mem B (slot w iM) w → wv s.mem B (slot w iX₂) w < wv s.mem B (slot w iM) w →
        wv t.mem B (slot w iX₁) w = if odd then
          subMod (wv s.mem B (slot w iM) w) (wv s.mem B (slot w iX₁) w) (wv s.mem B (slot w iX₂) w)
          else wv s.mem B (slot w iX₁) w) ∧
      Frm B [(slot w iX₁, 8 * w), (slot w iT, 8 * w)] s.mem t.mem ∧
      Keep [.rax, .rbx, .rdx, .rsi, .rbp, .r8, .r10, .r14, .r15] s t := by
  have hn := hs.nowrap
  have sX₁ := Nat.le_trans (slot_lt (w := w) hX₁) hZ
  have sX₂ := Nat.le_trans (slot_lt (w := w) hX₂) hZ
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have sT := Nat.le_trans (slot_lt (w := w) hT) hZ
  have p9 := slot_far (w := w) dX
  have p10 := slot_far (w := w) dX₁M
  have p11 := slot_far (w := w) dX₁T
  have p12 := slot_far (w := w) dX₂T
  have p13 := slot_far (w := w) dMT
  simp only [invSubXP, seqs, List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask false ∧
      t.mem = s.mem) (by xrun) rfl)
    fun s₃ ⟨⟨hbp₃, m₃⟩, k₃⟩ => WP.mono (base3_ok iX₁ iX₂ iT (r₁ := .r8) (r₂ := .r10) (r₃ := .rsi) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) ((k₃.gpr (by decide)).trans hdi)
      ((k₃.gpr (by decide)).trans h9) (by decide) (by decide)) fun s₄ ⟨h8₄, h10₄, hsi₄, m₄, k₄⟩ => ?_))
  have k04 := k₃.trans k₄
  refine WP.seq (WP.mono (subM_ok (hs.congr k04.2.2) hsi₄ h8₄ h10₄ ((k04.gpr (by decide)).trans h15)
    ((k04.gpr (by decide)).trans h12) ((k₄.gpr (by decide)).trans hbp₃) hw1 (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith)) fun s₅ ⟨b₂, hb₂, hv₅, o₅, k₅⟩ => ?_)
  rw [m₄, m₃] at hv₅ o₅
  have k05 := k04.trans k₅
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.r15, .rbp] (Q := fun t => t.gpr .r15 = mask b₂ ∧
      t.gpr .rbp = mask false ∧ t.mem = s₅.mem) (by xrun [hb₂]) rfl)
    fun s₆ ⟨⟨h15₆, hbp₆, m₆⟩, k₆⟩ => WP.mono (base3_ok iT iM iX₁ (r₁ := .r8) (r₂ := .r10) (r₃ := .rbx) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (((k05.trans k₆).gpr (by decide)).trans hdi)
      (((k05.trans k₆).gpr (by decide)).trans h9) (by decide) (by decide)) fun s₇ ⟨h8₇, h10₇, hbx₇, m₇, k₇⟩ => ?_))
  have k07 := (k05.trans k₆).trans k₇
  have hT₇ : wv s₇.mem B (slot w iT) w = wv s₅.mem B (slot w iT) w := by rw [m₇, m₆]
  have hM₇ : wv s₇.mem B (slot w iM) w = wv s.mem B (slot w iM) w := by
    have e2 := o₅.wv (d := slot w iM) (k := w) (by omega_arith) (by omega_arith)
    rw [m₇, m₆, e2]
  refine WP.mono (addM_ok (hs.congr k07.2.2) hbx₇ h10₇ h8₇ ((k₇.gpr (by decide)).trans h15₆)
    ((k07.gpr (by decide)).trans h12) ((k₇.gpr (by decide)).trans hbp₆) hw1 (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨c, _, hvt, ot, kt⟩ => ?_
  rw [hT₇, hM₇] at hvt
  have x1 := wv_lt t.mem B (slot w iX₁) w
  have t5 := wv_lt s₅.mem B (slot w iT) w
  have x10 := wv_lt s.mem B (slot w iX₁) w
  have hb2 := Bool.toNat_le b₂
  have hc := Bool.toNat_le c
  refine ⟨fun h1 h2 => ?_, ?_, (k07.trans kt).mono (by decide)⟩
  · clear hn sX₁ sX₂ sM sT p9 p10 p11 p12 p13
    unfold subMod
    cases odd <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hv₅ ⊢
    · cases b₂ <;> cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, ite_false,
        ite_true, Bool.false_eq_true, Nat.zero_add, Nat.add_zero] at hv₅ hvt <;> omega_arith
    · split <;> cases b₂ <;> cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one,
        ite_false, ite_true, Bool.false_eq_true, Nat.zero_add, Nat.add_zero] at hv₅ hvt <;> omega_arith
  · intro x hx
    have b := hx (slot w iX₁, 8 * w) (by simp)
    have d := hx (slot w iT, 8 * w) (by simp)
    dsimp only at b d
    rw [ot x (by omega_arith), m₇, m₆, o₅ x (by omega_arith)]

/-- Two bases. -/
theorem base2_ok {s : State} {B : Addr} {w : Nat} (i j : Nat) {r₁ r₂ : Reg} (h₁ : r₁ ≠ .r9) (h₂ : r₂ ≠ .r9)
    (h₁₂ : r₂ ≠ r₁) (hdi : s.gpr .rdi = B) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) (hr1 : r₁ ≠ .rdi) :
    WP isa (.block (base i r₁ ++ base j r₂)) s fun t =>
      t.gpr r₁ = off B (slot w i) ∧ t.gpr r₂ = off B (slot w j) ∧ t.mem = s.mem ∧ Keep [r₁, r₂] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (base_ok i h₁ hdi h9) fun t₁ ⟨e₁, m₁, k₁⟩ => ?_
  have g1 : ∀ r, r ≠ r₁ → t₁.gpr r = s.gpr r := fun r h => k₁.gpr (by simp [h])
  refine WP.mono (base_ok j h₂ ((g1 _ (Ne.symm hr1)).trans hdi) ((g1 _ (Ne.symm h₁)).trans h9))
    fun t ⟨e₂, m₂, k₂⟩ => ?_
  have g2 : ∀ r, r ≠ r₂ → t.gpr r = t₁.gpr r := fun r h => k₂.gpr (by simp [h])
  exact ⟨(g2 _ (Ne.symm h₁₂)).trans e₁, e₂, m₂.trans m₁, (k₁.trans k₂).mono (by simp)⟩

/-- `u /= 2`, if the word `w` of `u` is zero. -/
theorem invHalfU_ok {s : State} {B : Addr} {Z w : Nat} {iU : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) (hU : iU < 16)
    (h0 : word s.mem B (slot w iU + 8 * w) = 0) :
    WP isa (seqs (invHalfUP iU)) s fun t =>
      wv t.mem B (slot w iU) w = wv s.mem B (slot w iU) w / 2 ∧ Outside B (slot w iU) (8 * w) s.mem t.mem ∧
      Keep [.rax, .rdx, .rsi, .r8, .r14] s t := by
  have hn := hs.nowrap
  have sU := Nat.le_trans (slot_lt (w := w) hU) hZ
  simp only [invHalfUP, seqs]
  refine WP.seq (WP.mono (base2_ok iU iU (r₁ := .r8) (r₂ := .rsi) (by decide) (by decide) (by decide) hdi h9
    (by decide)) fun s₁ ⟨h8, hsi, m₁, k₁⟩ => ?_)
  refine WP.mono (shr_ok (hs.congr k₁.2.2) hsi h8 ((k₁.gpr (by decide)).trans h12) hw1 (by omega_arith) (by omega_arith)
    (by omega_arith) (Or.inl (Nat.le_refl _))) fun t ⟨hv, o, k₂⟩ => ?_
  rw [m₁, h0, ← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide)] at hv
  rw [m₁] at o
  refine ⟨?_, o, (k₁.trans k₂).mono (by decide)⟩
  simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_mod, Nat.mul_zero, Nat.add_zero] at hv
  omega_arith

theorem adc0 (c : Bool) : (BitVec.setWidth 64 (0 : BitVec 32) + 0 +
    BitVec.setWidth 64 (BitVec.ofBool c)).toNat = c.toNat := by cases c <;> decide

/-- `x₁ := x₁ / 2 (mod m)`. -/
theorem invHalfX_ok {s : State} {B : Addr} {Z w : Nat} {iX₁ iM iT : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) (hX₁ : iX₁ < 16) (hM : iM < 16) (hT : iT < 16)
    (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT) (dMT : iM ≠ iT) :
    WP isa (seqs (invHalfXP iX₁ iM iT)) s fun t =>
      wv t.mem B (slot w iX₁) w = halfMod (wv s.mem B (slot w iM) w) (wv s.mem B (slot w iX₁) w) ∧
      Frm B [(slot w iX₁, 8 * w), ar w iT] s.mem t.mem ∧
      Keep [.rax, .rbx, .rdx, .rsi, .rbp, .r8, .r10, .r14, .r15] s t := by
  have hn := hs.nowrap
  have sX₁ := Nat.le_trans (slot_lt (w := w) hX₁) hZ
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have sT := Nat.le_trans (slot_lt (w := w) hT) hZ
  have p10 := slot_far (w := w) dX₁M
  have p11 := slot_far (w := w) dX₁T
  have p13 := slot_far (w := w) dMT
  simp only [invHalfXP, seqs, List.append_assoc]
  -- `r8 := X₁`, `r15 := ` the mask of `x₁` odd, `rbp := 0`, `r10 := M`, `rbx := T`.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (base_ok iX₁ (r := .r8) (by decide) hdi h9)
    fun s₁ ⟨h8, m₁, k₁⟩ => WP.block_append_iff.mpr (WP.mono (WP.keep [.rax, .r15, .rbp] (Q := fun t =>
      t.gpr .r15 = mask (decide (wv s.mem B (slot w iX₁) w % 2 = 1)) ∧ t.gpr .rbp = mask false ∧ t.mem = s₁.mem)
      (by
        have e0 : (s₁.mem.readW (off B (slot w iX₁)) 64).toNat % 2 = wv s.mem B (slot w iX₁) w % 2 := by
          rw [m₁, ← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide)]
        xrun [State.ea, at0, h8, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
          (hs.congr k₁.2.2).ld (d := slot w iX₁) (by omega_arith), mask_low, e0]) rfl)
      fun s₂ ⟨⟨h15, hbp, m₂⟩, k₂⟩ => WP.mono (base2_ok iM iT (r₁ := .r10) (r₂ := .rbx) (by decide) (by decide)
        (by decide) (((k₁.trans k₂).gpr (by decide)).trans hdi) (((k₁.trans k₂).gpr (by decide)).trans h9)
        (by decide)) fun s₃ ⟨h10, hbx, m₃, k₃⟩ => ?_)))
  have k03 := (k₁.trans k₂).trans k₃
  -- `T := (M & mask) + X₁`.
  refine WP.seq (WP.mono (addM_ok (hs.congr k03.2.2) hbx h10 ((k₂.trans k₃).gpr (by decide) |>.trans h8)
    ((k₃.gpr (by decide)).trans h15) ((k03.gpr (by decide)).trans h12) ((k₃.gpr (by decide)).trans hbp) hw1
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun s₄ ⟨c, hc, hv₄, o₄, k₄⟩ => ?_)
  rw [m₃, m₂, m₁] at hv₄ o₄
  have k04 := k03.trans k₄
  have hs₄ := hs.congr k04.2.2
  -- `T_w := c`, `r8 := T`, `rsi := X₁`.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.rax, .rbp] (Q := fun t =>
      t.mem = s₄.mem.writeW (off B (slot w iT + 8 * w)) (BitVec.ofNat 64 c.toNat)) (by
      have ebx : s₄.gpr .rbx = off B (slot w iT) := (k₄.gpr (by decide)).trans hbx
      have e12 : s₄.gpr .r12 = BitVec.ofNat 64 w := (k04.gpr (by decide)).trans h12
      unfold cfFromRbp
      xrun [State.ea, ix, ebx, e12, addr0 (b := off B (slot w iT)) rfl rfl, hc, cf_mask,
        hs₄.st (d := slot w iT + 8 * w) (by omega_arith), sx0]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [adc0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Bool.toNat_le c; omega_arith)]) rfl)
    fun s₅ ⟨m₅, k₅⟩ => WP.mono (base2_ok iT iX₁ (r₁ := .r8) (r₂ := .rsi) (by decide) (by decide) (by decide)
      (((k04.trans k₅).gpr (by decide)).trans hdi) (((k04.trans k₅).gpr (by decide)).trans h9) (by decide))
      fun s₆ ⟨h8₆, hsi₆, m₆, k₆⟩ => ?_))
  have k06 := (k04.trans k₅).trans k₆
  -- `X₁ := T / 2`.
  refine WP.mono (shr_ok (hs.congr k06.2.2) hsi₆ h8₆ ((k06.gpr (by decide)).trans h12) hw1 (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith)) fun t ⟨hv, o, k₇⟩ => ?_
  have hT₆ : wv s₆.mem B (slot w iT) w = wv s₄.mem B (slot w iT) w := by
    rw [m₆, m₅]
    exact (writeW_outside s₄.mem B (d := slot w iT + 8 * w) _ (by omega_arith)).wv (Or.inl (Nat.le_refl _)) (by omega_arith)
  have hTw : word s₆.mem B (slot w iT + 8 * w) = BitVec.ofNat 64 c.toNat := by rw [m₆, m₅, word_writeW_self]
  have hT0 : (word s₆.mem B (slot w iT)).toNat % 2 = wv s₄.mem B (slot w iT) w % 2 := by
    rw [← hT₆, ← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide)]
  have hcl := Bool.toNat_le c
  rw [hT₆, hTw, hT0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c.toNat < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show c.toNat < 2 by omega_arith)] at hv
  refine ⟨?_, ?_, (k06.trans k₇).mono (by decide)⟩
  · unfold halfMod
    rcases Nat.mod_two_eq_zero_or_one (wv s.mem B (slot w iX₁) w) with h | h
    · rw [show decide (wv s.mem B (slot w iX₁) w % 2 = 1) = false by simp [h]] at hv₄
      simp only [Bool.false_eq_true, ite_false] at hv₄
      simp only [h, ite_true]; omega_arith
    · rw [show decide (wv s.mem B (slot w iX₁) w % 2 = 1) = true by simp [h]] at hv₄
      simp only [ite_true] at hv₄
      simp only [show ¬ (wv s.mem B (slot w iX₁) w % 2 = 0) by omega_arith, ite_false]; omega_arith
  · intro x hx
    have a := hx (slot w iX₁, 8 * w) (by simp)
    have b := hx (ar w iT) (by simp)
    dsimp only at a b
    rw [o x (by omega_arith), m₆, m₅, writeW_outside s₄.mem B _ (by omega_arith) x (by omega_arith), o₄ x (by omega_arith)]

/-- What the swaps and the subtractions leave: `(u', v', x₁', x₂')`. -/
def subState (m : Nat) (st : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  let (u, v, x₁, x₂) := st
  if u % 2 = 1 then
    if u < v then (v - u, u, subMod m x₂ x₁, x₁) else (u - v, v, subMod m x₁ x₂, x₂)
  else (u, v, x₁, x₂)

/-- The swaps and the subtractions of a step of `inverse`. -/
theorem invFirst_ok {s : State} {B : Addr} {Z w : Nat} {iU iV iX₁ iX₂ iM iT : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z)
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT) :
    WP isa (seqs (invSwapP iU iV iX₁ iX₂ ++ invSubP iU iV iX₁ iX₂ iM iT)) s fun t =>
      (wv s.mem B (slot w iX₁) w < wv s.mem B (slot w iM) w → wv s.mem B (slot w iX₂) w < wv s.mem B (slot w iM) w →
        (wv t.mem B (slot w iU) w, wv t.mem B (slot w iV) w, wv t.mem B (slot w iX₁) w, wv t.mem B (slot w iX₂) w) =
          subState (wv s.mem B (slot w iM) w) (wv s.mem B (slot w iU) w, wv s.mem B (slot w iV) w,
            wv s.mem B (slot w iX₁) w, wv s.mem B (slot w iX₂) w)) ∧
      Frm B [(slot w iU, 8 * w), (slot w iV, 8 * w), (slot w iX₁, 8 * w), (slot w iX₂, 8 * w), (slot w iT, 8 * w),
        (8 * sMo, 8)] s.mem t.mem ∧
      Keep [.rax, .rbx, .rdx, .rsi, .rbp, .r8, .r10, .r14, .r15] s t := by
  have hn := hs.nowrap
  have sU := Nat.le_trans (slot_lt (w := w) hU) hZ
  have sV := Nat.le_trans (slot_lt (w := w) hV) hZ
  have sX₁ := Nat.le_trans (slot_lt (w := w) hX₁) hZ
  have sX₂ := Nat.le_trans (slot_lt (w := w) hX₂) hZ
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have sT := Nat.le_trans (slot_lt (w := w) hT) hZ
  have hU0 := hdr_lt_slot w iU (show sMo < 32 by decide)
  have hV0 := hdr_lt_slot w iV (show sMo < 32 by decide)
  have hX10 := hdr_lt_slot w iX₁ (show sMo < 32 by decide)
  have hX20 := hdr_lt_slot w iX₂ (show sMo < 32 by decide)
  have hM0 := hdr_lt_slot w iM (show sMo < 32 by decide)
  have hT0 := hdr_lt_slot w iT (show sMo < 32 by decide)
  rw [invSubP]
  refine wp_seqs_append (by simp [invSwapP]) (by simp [invSubUP]) (WP.mono (invSwap_ok hs hdi h12 h9 hw1 hw hZ hU hV
    hX₁ hX₂ dUV dX dUX₁ dUX₂ dVX₁ dVX₂ rfl rfl rfl rfl rfl) fun s₁ ⟨hmo, hU₁, hV₁, hX₁₁, hX₂₁, f₁, k₁⟩ => ?_)
  refine wp_seqs_append (by simp [invSubUP]) (by simp [invSubXP]) (WP.mono (invSubU_ok (hs.congr k₁.2.2)
    ((k₁.gpr (by decide)).trans hdi) ((k₁.gpr (by decide)).trans h12) ((k₁.gpr (by decide)).trans h9) hw1 hw hZ
    hU hV dUV hmo) fun s₂ ⟨hU₂, h15₂, o₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine WP.mono (invSubX_ok (hs.congr k12.2.2) ((k12.gpr (by decide)).trans hdi)
    ((k12.gpr (by decide)).trans h12) ((k12.gpr (by decide)).trans h9) hw1 hw hZ hX₁ hX₂ hM hT dX dX₁M dX₁T dX₂T dMT
    h15₂) fun t ⟨hX₁t, f₃, k₃⟩ => ?_
  -- What each part leaves of the others.
  have eM₁ : wv s₁.mem B (slot w iM) w = wv s.mem B (slot w iM) w := f₁.wv_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · have := slot_far (w := w) dUM; omega_arith
    · have := slot_far (w := w) dVM; omega_arith
    · have := slot_far (w := w) dX₁M; omega_arith
    · have := slot_far (w := w) dX₂M; omega_arith
    · omega_arith) (by omega_arith)
  have eV₂ : wv s₂.mem B (slot w iV) w = wv s₁.mem B (slot w iV) w :=
    o₂.wv (by have := slot_far (w := w) dUV; omega_arith) (by omega_arith)
  have eX₁₂ : wv s₂.mem B (slot w iX₁) w = wv s₁.mem B (slot w iX₁) w :=
    o₂.wv (by have := slot_far (w := w) dUX₁; omega_arith) (by omega_arith)
  have eX₂₂ : wv s₂.mem B (slot w iX₂) w = wv s₁.mem B (slot w iX₂) w :=
    o₂.wv (by have := slot_far (w := w) dUX₂; omega_arith) (by omega_arith)
  have eM₂ : wv s₂.mem B (slot w iM) w = wv s₁.mem B (slot w iM) w :=
    o₂.wv (by have := slot_far (w := w) dUM; omega_arith) (by omega_arith)
  have eU₃ : wv t.mem B (slot w iU) w = wv s₂.mem B (slot w iU) w := f₃.wv_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only
    · have := slot_far (w := w) dUX₁; omega_arith
    · have := slot_far (w := w) dUT; omega_arith) (by omega_arith)
  have eV₃ : wv t.mem B (slot w iV) w = wv s₂.mem B (slot w iV) w := f₃.wv_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only
    · have := slot_far (w := w) dVX₁; omega_arith
    · have := slot_far (w := w) dVT; omega_arith) (by omega_arith)
  have eX₂₃ : wv t.mem B (slot w iX₂) w = wv s₂.mem B (slot w iX₂) w := f₃.wv_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only
    · have := slot_far (w := w) dX; omega_arith
    · have := slot_far (w := w) dX₂T; omega_arith) (by omega_arith)
  rw [eX₁₂, eX₂₂, eM₂, eM₁, hX₁₁, hX₂₁] at hX₁t
  rw [hV₁, hU₁] at hU₂
  refine ⟨fun hx₁ hx₂ => ?_, ?_, ((k12.trans k₃)).mono (by decide)⟩
  · rw [eU₃, eV₃, eX₂₃, eV₂, eX₂₂, hV₁, hX₂₁]
    have := hX₁t (by split <;> omega_arith) (by split <;> omega_arith)
    rw [this]
    have hu := wv_lt s₂.mem B (slot w iU) w
    unfold subState
    dsimp only
    generalize wv s.mem B (slot w iU) w = u at hU₂ ⊢
    generalize wv s.mem B (slot w iV) w = v at hU₂ ⊢
    generalize wv s₂.mem B (slot w iU) w = u' at hU₂ hu ⊢
    rcases Nat.mod_two_eq_zero_or_one u with ho | ho
    · simp only [ho, decide_false, Bool.false_and, Bool.false_eq_true, ite_false, false_and, Nat.mul_zero,
        Nat.add_zero, show (0 : Nat) ≠ 1 by decide] at hU₂ ⊢
      rw [hU₂]
    · by_cases hlt : u < v
      · simp only [ho, hlt, decide_true, Bool.and_self, ite_true, show ¬ v < u by omega_arith, and_false, ite_false,
          Nat.mul_zero, Nat.add_zero] at hU₂ ⊢
        refine Prod.ext (by dsimp only; omega_arith) rfl
      · simp only [ho, hlt, decide_true, decide_false, Bool.and_false, Bool.false_eq_true, ite_true, ite_false,
          and_false, Nat.mul_zero, Nat.add_zero] at hU₂ ⊢
        refine Prod.ext (by dsimp only; omega_arith) rfl
  · intro x hx
    have a := hx (slot w iU, 8 * w) (by simp)
    have b := hx (slot w iV, 8 * w) (by simp)
    have c := hx (slot w iX₁, 8 * w) (by simp)
    have d := hx (slot w iX₂, 8 * w) (by simp)
    have e := hx (slot w iT, 8 * w) (by simp)
    have g := hx (8 * sMo, 8) (by simp)
    dsimp only at a b c d e g
    have h3 : ∀ r ∈ [(slot w iX₁, 8 * w), (slot w iT, 8 * w)], ofs B x < r.1 ∨ r.1 + r.2 ≤ ofs B x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> with_reducible assumption
    have h1 : ∀ r ∈ [(slot w iU, 8 * w), (slot w iV, 8 * w), (slot w iX₁, 8 * w), (slot w iX₂, 8 * w), (8 * sMo, 8)],
        ofs B x < r.1 ∨ r.1 + r.2 ≤ ofs B x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl) <;> with_reducible assumption
    rw [f₃ x h3, o₂ x a, f₁ x h1]

/-- `KeyMath.invStep` is the subtraction, then the halvings. -/
theorem invStep_eq (m : Nat) (st : Nat × Nat × Nat × Nat) :
    VG.Proof.Rsa.invStep m st = ((subState m st).1 / 2, (subState m st).2.1, halfMod m (subState m st).2.2.1,
      (subState m st).2.2.2) := by
  obtain ⟨u, v, x₁, x₂⟩ := st
  unfold VG.Proof.Rsa.invStep subState
  dsimp only
  split
  · split <;> rfl
  · rfl

/-- One step of `inverse`: `KeyMath.invStep`, while `x₁, x₂ < m` and the
word `w` of `u` is zero. -/
theorem invStepCode_ok {s : State} {B : Addr} {Z w k : Nat} {iU iV iX₁ iX₂ iM iT : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (h13 : s.gpr .r13 = BitVec.ofNat 64 k) (h11 : s.gpr .r11 = BitVec.ofNat 64 (128 * w))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hk : k < 128 * w) (hZ : slot w 16 ≤ Z)
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT) (hU0 : word s.mem B (slot w iU + 8 * w) = 0) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.invStep iU iV iX₁ iX₂ iM iT) s fun t =>
      t.zf = some (decide (k + 1 = 128 * w)) ∧ t.gpr .r13 = BitVec.ofNat 64 (k + 1) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧
      Frm B [(slot w iU, 8 * w), (slot w iV, 8 * w), (slot w iX₁, 8 * w), (slot w iX₂, 8 * w), ar w iT,
        (8 * sMo, 8)] s.mem t.mem ∧ Keep stepRegs s t ∧
      (wv s.mem B (slot w iX₁) w < wv s.mem B (slot w iM) w → wv s.mem B (slot w iX₂) w < wv s.mem B (slot w iM) w →
        (wv t.mem B (slot w iU) w, wv t.mem B (slot w iV) w, wv t.mem B (slot w iX₁) w, wv t.mem B (slot w iX₂) w) =
          VG.Proof.Rsa.invStep (wv s.mem B (slot w iM) w) (wv s.mem B (slot w iU) w, wv s.mem B (slot w iV) w,
            wv s.mem B (slot w iX₁) w, wv s.mem B (slot w iX₂) w)) := by
  have hn := hs.nowrap
  have sU := Nat.le_trans (slot_lt (w := w) hU) hZ
  have sV := Nat.le_trans (slot_lt (w := w) hV) hZ
  have sX₁ := Nat.le_trans (slot_lt (w := w) hX₁) hZ
  have sX₂ := Nat.le_trans (slot_lt (w := w) hX₂) hZ
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have sT := Nat.le_trans (slot_lt (w := w) hT) hZ
  have hU0' := hdr_lt_slot w iU (show sMo < 32 by decide)
  have hX10 := hdr_lt_slot w iX₁ (show sMo < 32 by decide)
  have hM0 := hdr_lt_slot w iM (show sMo < 32 by decide)
  have hT0 := hdr_lt_slot w iT (show sMo < 32 by decide)
  unfold VG.Impl.Rsa.X86_64.Keys.invStep
  rw [show invSwapP iU iV iX₁ iX₂ ++ (invSubP iU iV iX₁ iX₂ iM iT ++ (invHalfP iU iX₁ iM iT ++ [.block countP])) =
    (invSwapP iU iV iX₁ iX₂ ++ invSubP iU iV iX₁ iX₂ iM iT) ++ (invHalfUP iU ++ (invHalfXP iX₁ iM iT ++
      [.block countP])) by simp [invHalfP]]
  refine wp_seqs_append (by simp [invSwapP]) (by simp [invHalfUP]) (WP.mono (invFirst_ok hs hdi h12 h9 hw1 hw hZ hU hV
    hX₁ hX₂ hM hT dUV dUX₁ dUX₂ dUM dUT dVX₁ dVX₂ dVM dVT dX dX₁M dX₁T dX₂M dX₂T dMT) fun s₁ ⟨hv₁, f₁, k₁⟩ => ?_)
  have hU0₁ : word s₁.mem B (slot w iU + 8 * w) = 0 := by
    rw [f₁.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
      · omega_arith
      · have := slot_far (w := w) dUV; omega_arith
      · have := slot_far (w := w) dUX₁; omega_arith
      · have := slot_far (w := w) dUX₂; omega_arith
      · have := slot_far (w := w) dUT; omega_arith
      · omega_arith) (by omega_arith)]
    exact hU0
  refine wp_seqs_append (by simp [invHalfUP]) (by simp [invHalfXP]) (WP.mono (invHalfU_ok (hs.congr k₁.2.2)
    ((k₁.gpr (by decide)).trans hdi) ((k₁.gpr (by decide)).trans h12) ((k₁.gpr (by decide)).trans h9) hw1 hw hZ
    hU hU0₁) fun s₂ ⟨hU₂, o₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine wp_seqs_append (by simp [invHalfXP]) (by simp) (WP.mono (invHalfX_ok (hs.congr k12.2.2)
    ((k12.gpr (by decide)).trans hdi) ((k12.gpr (by decide)).trans h12) ((k12.gpr (by decide)).trans h9) hw1 hw hZ
    hX₁ hM hT dX₁M dX₁T dMT) fun s₃ ⟨hX₃, f₃, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  simp only [seqs]
  refine WP.mono (WP.keep [.r13] (Q := fun t => t.zf = some (decide (k + 1 = 128 * w)) ∧
      t.gpr .r13 = BitVec.ofNat 64 (k + 1) ∧ t.mem = s₃.mem) (by
    unfold countP
    xrun [(k13.gpr (by decide) : s₃.gpr .r13 = _), h13, (k13.gpr (by decide) : s₃.gpr .r11 = _), h11, ofNat_add_one,
      ofNat_sub_beq (show k + 1 < 2 ^ 64 by omega_arith) (show 128 * w < 2 ^ 64 by omega_arith)]) rfl)
    fun t ⟨⟨hz, h13t, mt⟩, k₄⟩ => ⟨hz, h13t, (k₄.gpr (by decide)).trans ((k13.gpr (by decide)).trans h12), ?_,
      (k13.trans k₄).mono (by decide), fun hx₁ hx₂ => ?_⟩
  · intro x hx
    have a := hx (slot w iU, 8 * w) (by simp)
    have b := hx (slot w iV, 8 * w) (by simp)
    have c := hx (slot w iX₁, 8 * w) (by simp)
    have d := hx (slot w iX₂, 8 * w) (by simp)
    have e := hx (ar w iT) (by simp)
    have g := hx (8 * sMo, 8) (by simp)
    dsimp only at a b c d e g
    have h3 : ∀ r ∈ [(slot w iX₁, 8 * w), ar w iT], ofs B x < r.1 ∨ r.1 + r.2 ≤ ofs B x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> with_reducible assumption
    have h1 : ∀ r ∈ [(slot w iU, 8 * w), (slot w iV, 8 * w), (slot w iX₁, 8 * w), (slot w iX₂, 8 * w),
        (slot w iT, 8 * w), (8 * sMo, 8)], ofs B x < r.1 ∨ r.1 + r.2 ≤ ofs B x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl | rfl) <;> first | with_reducible assumption | (dsimp only; omega_arith)
    rw [mt, f₃ x h3, o₂ x a, f₁ x h1]
  · have e := hv₁ hx₁ hx₂
    rw [invStep_eq, ← e]
    have eM₁ : wv s₁.mem B (slot w iM) w = wv s.mem B (slot w iM) w := f₁.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
      · have := slot_far (w := w) dUM; omega_arith
      · have := slot_far (w := w) dVM; omega_arith
      · have := slot_far (w := w) dX₁M; omega_arith
      · have := slot_far (w := w) dX₂M; omega_arith
      · have := slot_far (w := w) dMT; omega_arith
      · omega_arith) (by omega_arith)
    have eM₂ : wv s₂.mem B (slot w iM) w = wv s₁.mem B (slot w iM) w :=
      o₂.wv (by have := slot_far (w := w) dUM; omega_arith) (by omega_arith)
    have eX₂ : wv s₂.mem B (slot w iX₁) w = wv s₁.mem B (slot w iX₁) w :=
      o₂.wv (by have := slot_far (w := w) dUX₁; omega_arith) (by omega_arith)
    have f3 : ∀ i, i ≠ iX₁ → i ≠ iT → i < 16 → wv t.mem B (slot w i) w = wv s₂.mem B (slot w i) w := by
      intro i h1 h2 hi
      rw [mt]
      exact f₃.wv_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only
        · have := slot_far (w := w) h1; omega_arith
        · have := slot_far (w := w) h2; omega_arith) (by have := Nat.le_trans (slot_lt (w := w) hi) hZ; omega_arith)
    have o2 : ∀ i, i ≠ iU → i < 16 → wv s₂.mem B (slot w i) w = wv s₁.mem B (slot w i) w := by
      intro i h1 hi
      exact o₂.wv (by have := slot_far (w := w) h1; omega_arith) (by have := Nat.le_trans (slot_lt (w := w) hi) hZ; omega_arith)
    rw [f3 iU dUX₁ dUT hU, hU₂, f3 iV dVX₁ dVT hV, o2 iV (Ne.symm dUV) hV, f3 iX₂ (Ne.symm dX) dX₂T hX₂,
      o2 iX₂ (Ne.symm dUX₂) hX₂, mt, hX₃, eM₂, eM₁, eX₂]

/-- The invariant of `inverse`'s loop after `j` steps from `s`. -/
structure InvInv (s : State) (B : Addr) (Z w iU iV iX₁ iX₂ iT a m : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  rdi : t.gpr .rdi = B
  r12 : t.gpr .r12 = BitVec.ofNat 64 w
  r9 : t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))
  r13 : t.gpr .r13 = BitVec.ofNat 64 j
  r11 : t.gpr .r11 = BitVec.ofNat 64 (128 * w)
  frm : Frm B [(slot w iU, 8 * w), (slot w iV, 8 * w), (slot w iX₁, 8 * w), (slot w iX₂, 8 * w), ar w iT,
    (8 * sMo, 8)] s.mem t.mem
  keep : Keep (.r9 :: .r11 :: stepRegs) s t
  u0 : word t.mem B (slot w iU + 8 * w) = 0
  val : m % 2 = 1 → 1 < m → (wv t.mem B (slot w iU) w, wv t.mem B (slot w iV) w, wv t.mem B (slot w iX₁) w,
    wv t.mem B (slot w iX₂) w) = invIter m j (a, m, 1, 0)

/-- `inverse`: from `(a, m, 1, 0)` in `[u], [v], [x₁], [x₂]` (the word `w`
of `[u]` zero), `[m]` odd and above 1: `[v] = gcd(a, m)` and
`[x₂] a ≡ [v] (mod m)`, `[x₂] < m`. -/
theorem inverse_ok {s : State} {B : Addr} {Z w : Nat} {iU iV iX₁ iX₂ iM iT : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hW : word s.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hS : word s.mem B (8 * sStride) = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z)
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT) (hU0 : word s.mem B (slot w iU + 8 * w) = 0)
    (hVM : wv s.mem B (slot w iV) w = wv s.mem B (slot w iM) w) (hX1 : wv s.mem B (slot w iX₁) w = 1)
    (hX2 : wv s.mem B (slot w iX₂) w = 0) :
    WP isa (inverse iU iV iX₁ iX₂ iM iT) s fun t =>
      t.gpr .rdi = B ∧
      Frm B [(slot w iU, 8 * w), (slot w iV, 8 * w), (slot w iX₁, 8 * w), (slot w iX₂, 8 * w), ar w iT,
        (8 * sMo, 8)] s.mem t.mem ∧ Keep (.r9 :: .r11 :: stepRegs) s t ∧
      (wv s.mem B (slot w iM) w % 2 = 1 → 1 < wv s.mem B (slot w iM) w →
        wv t.mem B (slot w iV) w = Nat.gcd (wv s.mem B (slot w iU) w) (wv s.mem B (slot w iM) w) ∧
        ((wv s.mem B (slot w iM) w : Nat) : Int) ∣
          (wv t.mem B (slot w iX₂) w : Int) * wv s.mem B (slot w iU) w - wv t.mem B (slot w iV) w ∧
        wv t.mem B (slot w iX₂) w < wv s.mem B (slot w iM) w) := by
  have hn := hs.nowrap
  have sU := Nat.le_trans (slot_lt (w := w) hU) hZ
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have hM0 := hdr_lt_slot w iM (show sMo < 32 by decide)
  have h256 : 8 * 32 ≤ Z := by have := hdr_lt_slot w 16 (show 31 < 32 by decide); omega_arith
  unfold inverse
  -- The registers.
  have e₁ : WP isa (.block invInit) s fun (t : State) =>
      t.gpr .rdi = B ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧
      t.gpr .r11 = BitVec.ofNat 64 (128 * w) ∧ t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s.mem ∧
      Keep [.r12, .r9, .r11, .r13] s t := by
    rw [invInit, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (ws_ok hs hdi h256 hW hS) fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
    refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 w ∧ t.mem = s₁.mem)
      (by xrun [h12]) rfl) fun s₃ ⟨⟨h11, m₃⟩, k₃⟩ => ?_
    refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 (128 * w) ∧ t.mem = s₃.mem)
      (by
        xrun [h11, ofNat_dbl, List.replicate]
        congr 1; omega_arith) rfl) fun s₄ ⟨⟨h11', m₄⟩, k₄⟩ => ?_
    refine WP.mono (WP.keep [.r13] (Q := fun t => t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s₄.mem)
      (by xrun) rfl) fun t ⟨⟨h13, m₅⟩, k₅⟩ => ?_
    have kk := ((k₁.trans k₃).trans k₄).trans k₅
    exact ⟨(kk.gpr (by decide)).trans hdi, ((k₃.trans k₄).trans k₅ |>.gpr (by decide)).trans h12,
      ((k₃.trans k₄).trans k₅ |>.gpr (by decide)).trans h9, (k₅.gpr (by decide)).trans h11', h13,
      by rw [m₅, m₄, m₃, m₁], kk.mono (by decide)⟩
  refine WP.seq (WP.mono e₁ fun s₁ ⟨hdi₁, h12₁, h9₁, h11₁, h13₁, m₁, k₁⟩ => ?_)
  have fM : ∀ {t : State}, Frm B [(slot w iU, 8 * w), (slot w iV, 8 * w), (slot w iX₁, 8 * w), (slot w iX₂, 8 * w),
      ar w iT, (8 * sMo, 8)] s.mem t.mem → wv t.mem B (slot w iM) w = wv s.mem B (slot w iM) w := fun f =>
    f.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
      · have := slot_far (w := w) dUM; omega_arith
      · have := slot_far (w := w) dVM; omega_arith
      · have := slot_far (w := w) dX₁M; omega_arith
      · have := slot_far (w := w) dX₂M; omega_arith
      · have := slot_far (w := w) dMT; omega_arith
      · omega_arith) (by omega_arith)
  refine wp_upto (a := 0) (N := 128 * w) (by omega_arith)
    (InvInv s B Z w iU iV iX₁ iX₂ iT (wv s.mem B (slot w iU) w) (wv s.mem B (slot w iM) w))
    (fun j _ hj t hI => ?_) (fun t hI => ⟨hI.rdi, hI.frm, hI.keep, fun hodd h1 => ?_⟩)
    ⟨hs.congr k₁.2.2, hdi₁, h12₁, h9₁, h13₁, h11₁, by rw [m₁]; exact Frm.refl _ _ _, k₁.mono (by decide),
      by rw [m₁]; exact hU0, fun _ _ => by rw [m₁, hVM, hX1, hX2]; rfl⟩
  · refine WP.mono (invStepCode_ok hI.scr hI.rdi hI.r12 hI.r9 hI.r13 hI.r11 hw1 hw hj hZ hU hV hX₁ hX₂ hM hT dUV dUX₁
      dUX₂ dUM dUT dVX₁ dVX₂ dVM dVT dX dX₁M dX₁T dX₂M dX₂T dMT hI.u0) fun t' ⟨hz, h13', h12', f', k', hv'⟩ =>
      ⟨hz, hI.scr.congr k'.2.2, (k'.gpr (by decide)).trans hI.rdi, h12', (k'.gpr (by decide)).trans hI.r9, h13',
        (k'.gpr (by decide)).trans hI.r11, hI.frm.trans f', (hI.keep.trans k').mono (by decide), ?_,
        fun hodd h1 => ?_⟩
    · rw [f'.word_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
        · omega_arith
        · have := slot_far (w := w) dUV; omega_arith
        · have := slot_far (w := w) dUX₁; omega_arith
        · have := slot_far (w := w) dUX₂; omega_arith
        · have := slot_far (w := w) dUT; omega_arith
        · have := hdr_lt_slot w iU (show sMo < 32 by decide); omega_arith) (by omega_arith)]
      exact hI.u0
    · have hv := hI.val hodd h1
      have hinv := invIter_inv hodd (invI_start (a := wv s.mem B (slot w iU) w) hodd h1) j
      rw [← hv] at hinv
      rw [fM hI.frm] at hv'
      rw [hv' hinv.x₁_lt hinv.x₂_lt, hv]
      rfl
  · have hv := hI.val hodd h1
    have hd := invIter_done (a := wv s.mem B (slot w iU) w) (K := 128 * w) hodd (by
      have := wv_lt s.mem B (slot w iU) w
      have := wv_lt s.mem B (slot w iM) w
      rw [show 128 * w = 64 * w + 64 * w by omega_arith, Nat.pow_add]
      exact Nat.mul_lt_mul'' (by omega_arith) (by omega_arith))
    rw [Nat.mod_eq_of_lt h1, ← hv] at hd
    exact ⟨hd.2.1, hd.2.2.1, hd.2.2.2⟩

end VG.Proof.Rsa.X86_64
