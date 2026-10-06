import VerifiedGarbage.Proof.Rsa.AArch64.RpCands

/-!
# `vg_rsa_recover_primes` on AArch64: the factors

`fin`, after the candidates: `y` out of Montgomery form and `u = y - 1`
(`finA_ok`), `p = gcd(u, n)` and `q = n / p` (`finB_ok`), the larger first
(`finC_ok`), both written masked by whether a candidate found `y`.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Proof.Bignum (mont_cancel)

/-- `u = y - 1` from `y` in Montgomery form, and the mask of `ok` into
`sMask`. -/
theorem finA_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t : Nat}
    (hc : Cst s B Z w minv N el r t) {res : Option Nat} (hc3 : word s.mem B (8 * sC3) = mask res.isSome)
    (hy : ∀ y, res = some y → wv s.mem B (slot w aY) w = y * 2 ^ (64 * w) % N ∧ y < N ∧ 1 ≤ y) :
    WP isa (seqs [.block [ldh .x3 sC3, sth .x3 sMask], M.mm aY aY aOne, zeroA fU,
      .block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base aY .x16 ++ base aOne .x17 ++
        base fU .x13), countLoop .x14 subBody]) s fun u =>
      Frm B (rg w [aAcc, aTmp, aY, fU] [sMask]) s.mem u.mem ∧ Keep mmRegs s u ∧
      word u.mem B (8 * sMask) = mask res.isSome ∧ word u.mem B (slot w fU + 8 * w) = 0 ∧
      (∀ y, res = some y → wv u.mem B (slot w fU) w = y - 1) := by
  have hZ16 := hc.hZ16
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have h256 := hc.ws.h256
  have hn := hc.ws.scr.nowrap
  have hR := hc.coprime
  have hN1 : 1 < N := by have := hc.n1; omega
  simp only [seqs]
  -- The mask.
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun u => u.mem = s.mem.writeW (off B (8 * sMask))
      (mask res.isSome)) (by
    brun [hc.ws.x0, hdr_enc (show sC3 < 32 by decide), hdr_enc (show sMask < 32 by decide),
      hc.ws.scr.ld (d := 8 * sC3) (by simp only [sC3, sFn]; omega),
      hc.ws.scr.st (d := 8 * sMask) (by simp only [sMask, sFn]; omega), hc3])
    (by decide) (by decide) (by decide +kernel)) fun u₁ ⟨m₁, k₁⟩ => ?_)
  have hf₁ : Frm B (rg w [] [sMask]) s.mem u₁.mem := by
    rw [m₁]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sMask, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hc₁ := hc.congr hf₁ (by decide) (by decide) k₁ (by decide)
  -- `y`.
  have hg₁ := hc₁.good
  have hY₁ : wv u₁.mem B (slot w aY) w = wv s.mem B (slot w aY) w :=
    hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)
  refine WP.seq (WP.mono (M.mm_ok hg₁.1 hg₁.2 hw1 (by omega) (o := aY) (a := aY) (b := aOne) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₁.hinv
    (by rw [hc₁.hone, hc₁.hn]; exact hN1)) fun u₂ ⟨_, hlt₂, hm₂, ha₂, k₂⟩ => ?_)
  rw [hc₁.hn] at hlt₂ hm₂
  rw [hc₁.hone, hY₁, Nat.mul_one] at hm₂
  have hf₂ : Frm B (rg w [aAcc, aTmp, aY] []) u₁.mem u₂.mem := Frm.rg_of_arrays ha₂ _ _ (by decide)
  have hc₂ := hc₁.congr hf₂ (by decide) (by simp) k₂ (by decide)
  have hy₂ : ∀ y, res = some y → wv u₂.mem B (slot w aY) w = y := fun y hres => by
    obtain ⟨e, hyN, _⟩ := hy y hres
    rw [e, Nat.mod_mod] at hm₂
    have := mont_cancel hR hm₂
    rwa [Nat.mod_eq_of_lt hlt₂, Nat.mod_eq_of_lt hyN] at this
  -- `u = 0`.
  refine WP.seq (WP.mono (zeroA_ok hc₂.ws (j := fU) (by decide)) fun u₃ ⟨z₃, o₃, _, _, _, k₃⟩ => ?_)
  have hf₃ : Frm B (rg w [fU] []) u₂.mem u₃.mem := Frm.rg_of_out o₃ (Nat.le_refl _) _ _ (by decide)
  have hc₃ := hc₂.congr hf₃ (by decide) (by simp) k₃ (by decide)
  -- `u = y - 1`.
  refine WP.seq (WP.mono (subSet_ok hc₃.ws aY aOne fU) fun u₄ ⟨⟨h16, h17, h13, h14, _, _, hc₄, m₄⟩, k₄⟩ => ?_)
  have hs₄ := hc₃.ws.scr.congr k₄.wr
  have sY := hc₃.ws.sl (j := aY) (by decide)
  have sO := hc₃.ws.sl (j := aOne) (by decide)
  have sU := hc₃.ws.sl (j := fU) (by decide)
  refine WP.mono (subLoop_ok hs₄ h16 h17 h13 h14 hc₄ (by omega) (by omega) (by omega) (by omega) (by omega)
    (by have := slot_sep (w := w) (show fU ≠ aY by decide); omega)
    (by have := slot_sep (w := w) (show fU ≠ aOne by decide); omega)) fun u ⟨hv, o₅, k₅⟩ => ?_
  have hf₅ : Frm B (rg w [fU] []) u₄.mem u.mem := Frm.rg_of_out o₅ (by omega) _ _ (by decide)
  rw [m₄] at hv o₅
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hf₄ : Frm B (rg w [] []) u₃.mem u₄.mem := by rw [m₄]; exact Frm.refl _ _ _
    exact ((((hf₁.rg_trans hf₂).rg_trans hf₃).rg_trans hf₄).rg_trans hf₅).rg_mono (by decide) (by decide)
  · exact ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)
  · rw [hf₅.rg_word (by decide) (by simp), m₄, hf₃.rg_word (by decide) (by simp),
      hf₂.rg_word (by decide) (by simp), m₁, word_writeW_self]
  · rw [o₅.word (Or.inr (by omega)) (by omega)]
    exact word_above_zero (n := w) (L := w + 2) (by omega) (by rw [z₃]; exact Nat.two_pow_pos _)
  · intro y hres
    obtain ⟨_, hyN, hy1⟩ := hy y hres
    have e3 : wv u₃.mem B (slot w aY) w = y := by
      rw [hf₃.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hy₂ y hres
    rw [e3, hc₃.hone] at hv
    have := wv_lt u.mem B (slot w fU) w
    have hyR : y < 2 ^ (64 * w) := by have := wv_lt u₂.mem B (slot w aY) w; rw [hy₂ y hres] at this; exact this
    cases hb : (!u.c)
    · rw [hb] at hv; simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv; omega
    · rw [hb] at hv; simp only [Bool.toNat_true, Nat.mul_one] at hv; omega

/-- `1` written over a zero number. -/
theorem wv_set_one {m : Mem} {B : Addr} {e w : Nat} (hw : 1 ≤ w) (hz : wv m B e (w + 2) = 0)
    (hn : e + 8 * (w + 2) ≤ 2 ^ 64) : wv (m.writeW (off B e) (1 : BitVec 64)) B e w = 1 := by
  rw [wv_low hw, word_writeW_self, (writeW_outside m B (1 : BitVec 64) (d := e) (by omega)).wv (Or.inr (by omega))
    (by omega)]
  have hz' : ∀ q < w + 2, word m B (e + 8 * q) = 0 := (wv_eq_zero_iff _ _ _ _).mp hz
  rw [wv_zero (n := w - 1) fun q hq => by
    have := hz' (1 + q) (by omega)
    rwa [show e + 8 * (1 + q) = e + 8 + 8 * q by omega] at this]
  rfl

/-- `p = gcd(u, n)` and `q = n / p`. -/
theorem finB_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w) (hn : wv s.mem B (slot w aN) w = N)
    (hodd : N % 2 = 1) (hN1 : 1 < N) (hU0 : word s.mem B (slot w fU + 8 * w) = 0) :
    WP isa (seqs [zeroA fV, copyA fV aN, zeroA fX₁, .block (setOneA fX₁), zeroA fX₂, inverse fU fV fX₁ fX₂ aN fT,
      zeroA fQ, copyA fQ aN, divmod fQ fR fV fT]) s fun u =>
      Frm B (rg w [fV, fX₁, fX₂, fU, fT, fQ, fR] []) s.mem u.mem ∧ Keep mmRegs s u ∧ Ws u B Z w ∧
      wv u.mem B (slot w fV) w = Nat.gcd (wv s.mem B (slot w fU) w) N ∧
      wv u.mem B (slot w fQ) w = N / Nat.gcd (wv s.mem B (slot w fU) w) N ∧
      wv u.mem B (slot w aN) w = N := by
  have hZ16 : slot w 16 ≤ 2 ^ 64 := by have := h.scr.nowrap; have := h.hZ; omega
  have hw1 := h.w1
  have hw2 := h.w2
  have hZ := h.hZ
  have sV := h.sl (j := fV) (by decide)
  have hnw := h.scr.nowrap
  simp only [seqs]
  -- `v = n`.
  refine WP.seq (WP.mono (zeroA_ok h (j := fV) (by decide)) fun u₁ ⟨_, o₁, _, _, _, k₁⟩ => ?_)
  have f₁ : Frm B (rg w [fV] []) s.mem u₁.mem := Frm.rg_of_out o₁ (Nat.le_refl _) _ _ (by decide)
  have h₁ := h.congrG f₁ (by simp) k₁ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₁ (o := fV) (a := aN) (by decide) (by decide) (by decide))
    fun u₂ ⟨c₂, o₂, _, _, k₂⟩ => ?_)
  have f₂ : Frm B (rg w [fV] []) u₁.mem u₂.mem := Frm.rg_of_out o₂ (by omega) _ _ (by decide)
  have h₂ := h₁.congrG f₂ (by simp) k₂ (by decide)
  -- `x₁ = 1`, `x₂ = 0`.
  refine WP.seq (WP.mono (zeroA_ok h₂ (j := fX₁) (by decide)) fun u₃ ⟨z₃, o₃, _, _, _, k₃⟩ => ?_)
  have f₃ : Frm B (rg w [fX₁] []) u₂.mem u₃.mem := Frm.rg_of_out o₃ (Nat.le_refl _) _ _ (by decide)
  have h₃ := h₂.congrG f₃ (by simp) k₃ (by decide)
  refine WP.seq (WP.mono (setOneA_ok h₃ (j := fX₁) (by decide)) fun u₄ ⟨m₄, k₄⟩ => ?_)
  have sX₁ := h.sl (j := fX₁) (by decide)
  have f₄ : Frm B (rg w [fX₁] []) u₃.mem u₄.mem := by
    rw [m₄]; exact Frm.rg_of_out (writeW_outside _ _ _ (by omega)) (by omega) _ _ (by decide)
  have h₄ := h₃.congrG f₄ (by simp) k₄ (by decide)
  have vX₁ : wv u₄.mem B (slot w fX₁) w = 1 := by rw [m₄]; exact wv_set_one (by omega) z₃ (by omega)
  refine WP.seq (WP.mono (zeroA_ok h₄ (j := fX₂) (by decide)) fun u₅ ⟨z₅, o₅, _, _, _, k₅⟩ => ?_)
  have f₅ : Frm B (rg w [fX₂] []) u₄.mem u₅.mem := Frm.rg_of_out o₅ (Nat.le_refl _) _ _ (by decide)
  have h₅ := h₄.congrG f₅ (by simp) k₅ (by decide)
  have f15 : Frm B (rg w [fV, fX₁, fX₂] []) s.mem u₅.mem :=
    ((((f₁.rg_trans f₂).rg_trans f₃).rg_trans f₄).rg_trans f₅).rg_mono (by decide) (by decide)
  have vN₅ : wv u₅.mem B (slot w aN) w = N := by
    rw [f15.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hn]
  have vU₅ : wv u₅.mem B (slot w fU) w = wv s.mem B (slot w fU) w :=
    f15.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)
  have vV₅ : wv u₅.mem B (slot w fV) w = N := by
    rw [f₅.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      f₄.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      f₃.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), c₂,
      f₁.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hn]
  have vX₁₅ : wv u₅.mem B (slot w fX₁) w = 1 := by
    rw [f₅.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), vX₁]
  have vX₂₅ : wv u₅.mem B (slot w fX₂) w = 0 := by
    have := wv_add u₅.mem B (slot w fX₂) w 2; omega
  have vU0₅ : word u₅.mem B (slot w fU + 8 * w) = 0 := by
    rw [f15.rg_wordA hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hU0
  -- The inverse: `v = gcd(u, n)`.
  refine WP.seq (WP.mono (inverse_ok h₅ (iU := fU) (iV := fV) (iX₁ := fX₁) (iX₂ := fX₂) (iM := aN) (iT := fT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) vU0₅ (by rw [vV₅, vN₅]) vX₁₅ vX₂₅) fun u₆ ⟨_, f₆', k₆, hv₆⟩ => ?_)
  have f₆ : Frm B (rg w [fU, fV, fX₁, fX₂, fT] []) u₅.mem u₆.mem := f₆'.widen (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
    · exact rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
    · exact rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
    · exact rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
    · exact rg_cover_arr _ (by decide) (Nat.le_refl _) (Nat.le_refl _))
  have h₆ := h₅.congrG f₆ (by simp) k₆ (by decide)
  rw [vN₅, vU₅] at hv₆
  obtain ⟨hg₆, -, -⟩ := hv₆ hodd hN1
  have vN₆ : wv u₆.mem B (slot w aN) w = N := by
    rw [f₆.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), vN₅]
  -- `q = n / v`.
  refine WP.seq (WP.mono (zeroA_ok h₆ (j := fQ) (by decide)) fun u₇ ⟨_, o₇, _, _, _, k₇⟩ => ?_)
  have f₇ : Frm B (rg w [fQ] []) u₆.mem u₇.mem := Frm.rg_of_out o₇ (Nat.le_refl _) _ _ (by decide)
  have h₇ := h₆.congrG f₇ (by simp) k₇ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₇ (o := fQ) (a := aN) (by decide) (by decide) (by decide))
    fun u₈ ⟨c₈, o₈, _, _, k₈⟩ => ?_)
  have f₈ : Frm B (rg w [fQ] []) u₇.mem u₈.mem := Frm.rg_of_out o₈ (by omega) _ _ (by decide)
  have h₈ := h₇.congrG f₈ (by simp) k₈ (by decide)
  have vQ₈ : wv u₈.mem B (slot w fQ) w = N := by
    rw [c₈, f₇.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), vN₆]
  have vV₈ : wv u₈.mem B (slot w fV) w = Nat.gcd (wv s.mem B (slot w fU) w) N := by
    rw [f₈.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      f₇.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hg₆]
  have hg0 : 0 < Nat.gcd (wv s.mem B (slot w fU) w) N := Nat.gcd_pos_of_pos_right _ (by omega)
  refine WP.mono (divmod_ok h₈ (iQ := fQ) (iR := fR) (iD := fV) (iT := fT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun u ⟨_, f₉', k₉, hv₉⟩ => ?_
  have f₉ : Frm B (rg w [fQ, fR, fT] []) u₈.mem u.mem := f₉'.widen (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact rg_cover_arr _ (by decide) (Nat.le_refl _) (Nat.le_refl _)
    · exact rg_cover_arr _ (by decide) (Nat.le_refl _) (Nat.le_refl _)
    · exact rg_cover_arr _ (by decide) (Nat.le_refl _) (Nat.le_refl _))
  rw [vV₈, vQ₈] at hv₉
  obtain ⟨-, hq₉⟩ := hv₉ hg0
  refine ⟨?_, ?_, h₈.congrG f₉ (by simp) k₉ (by decide), ?_, hq₉, ?_⟩
  · exact (((((f15.rg_trans f₆).rg_trans f₇).rg_trans f₈).rg_trans f₉)).rg_mono (by decide) (by decide)
  · exact ((((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k₈).trans k₉).mono
      (by decide)
  · rw [f₉.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), vV₈]
  · rw [f₉.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      f₈.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      f₇.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), vN₆]

/-- The bases of a comparison of `[a]` and `[b]` over `w` words, from the
carry set. -/
theorem cmpSet_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (a b : Nat) :
    WP isa (.block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base a .x16 ++ base b .x17)) s
      fun t => (t.gpr .x16 = off B (slot w a) ∧ t.gpr .x17 = off B (slot w b) ∧
        t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x12 = BitVec.ofNat 64 w ∧
        t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .x7 = 0 ∧ t.c = true ∧
        t.mem = s.mem) ∧ Keep [.x3, .x7, .x11, .x12, .x14, .x16, .x17] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x7, .x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧
      t.c = true ∧ t.mem = t₁.mem) (by brun [h12]) (by decide) (by decide) (by decide +kernel))
    fun t₂ ⟨⟨h14, h7, hc, m₂⟩, k₂⟩ => ?_
  have h0₂ : t₂.gpr .x0 = B := ((k₁.trans k₂).gpr .x0 (by decide)).trans h.x0
  refine WP.mono (base2_ok a b .x16 .x17 h0₂ ((k₂.gpr .x11 (by decide)).trans h11))
    fun t ⟨⟨h16, h17, m₃, c₃⟩, k₃⟩ => ⟨⟨h16, h17, (k₃.gpr .x14 (by decide)).trans h14,
      (k₃.gpr .x12 (by decide)).trans ((k₂.gpr .x12 (by decide)).trans h12),
      (k₃.gpr .x11 (by decide)).trans ((k₂.gpr .x11 (by decide)).trans h11), (k₃.gpr .x7 (by decide)).trans h7,
      c₃.trans hc, by rw [m₃, m₂, m₁]⟩, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- The mask of a borrow, `x14 := w`, and the bases of `[a]` and `[b]`. -/
theorem swapSet_ok {s : State} {B : Addr} {w : Nat} (a b : Nat) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h7 : s.gpr .x7 = 0) :
    WP isa (.block (borrowMask ++ [mov .x14 .x12] ++ base a .x16 ++ base b .x17)) s fun t =>
      (t.gpr .x15 = mask (!s.c) ∧ t.gpr .x16 = off B (slot w a) ∧ t.gpr .x17 = off B (slot w b) ∧
        t.gpr .x14 = BitVec.ofNat 64 w ∧ t.mem = s.mem) ∧ Keep [.x4, .x14, .x15, .x16, .x17] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (borrowMask_ok s h7) fun t₁ ⟨⟨h15, m₁, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.mem = t₁.mem)
    (by brun [(k₁.gpr .x12 (by decide)).trans h12]) (by decide) (by decide) (by decide +kernel))
    fun t₂ ⟨⟨h14, m₂⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  refine WP.mono (base2_ok a b .x16 .x17 ((k12.gpr .x0 (by decide)).trans h0) ((k12.gpr .x11 (by decide)).trans h11))
    fun t ⟨⟨h16, h17, m₃, _⟩, k₃⟩ => ⟨⟨(k₃.gpr .x15 (by decide)).trans ((k₂.gpr .x15 (by decide)).trans h15), h16,
      h17, (k₃.gpr .x14 (by decide)).trans h14, by rw [m₃, m₂, m₁]⟩, (k12.trans k₃).mono (by decide)⟩

/-- The larger of `[fV]` and `[fQ]` into `fV`, the smaller into `fQ`. -/
theorem finC_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (seqs [.block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base fV .x16 ++ base fQ .x17),
      cmpLoop, .block (borrowMask ++ [mov .x14 .x12] ++ base fV .x16 ++ base fQ .x17), countLoop .x14 cswapBody]) s
      fun u =>
      Frm B (rg w [fV, fQ] []) s.mem u.mem ∧ Keep mmRegs s u ∧ Ws u B Z w ∧
      wv u.mem B (slot w fV) w = max (wv s.mem B (slot w fV) w) (wv s.mem B (slot w fQ) w) ∧
      wv u.mem B (slot w fQ) w = min (wv s.mem B (slot w fV) w) (wv s.mem B (slot w fQ) w) := by
  have hw1 := h.w1
  have hw2 := h.w2
  have sV := h.sl (j := fV) (by decide)
  have sQ := h.sl (j := fQ) (by decide)
  have sep := slot_sep (w := w) (show fV ≠ fQ by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (cmpSet_ok h fV fQ) fun u₁ ⟨⟨h16, h17, h14, h12, h11, h7, hc, m₁⟩, k₁⟩ => ?_)
  have hs₁ := h.scr.congr k₁.wr
  refine WP.seq (WP.mono (VG.Proof.Bignum.AArch64.cmpLoop_ok hs₁ h16 h17 h14 hc (by omega) (by omega) (by omega)
    (by omega)) fun u₂ ⟨hc₂, m₂, k₂⟩ => ?_)
  rw [m₁] at hc₂
  -- The mask of `[fV] < [fQ]` and the bases.
  have k12 := k₁.trans k₂
  refine WP.seq (WP.mono (swapSet_ok fV fQ ((k12.gpr .x0 (by decide)).trans h.x0)
    ((k₂.gpr .x11 (by decide)).trans h11) ((k₂.gpr .x12 (by decide)).trans h12)
    ((k₂.gpr .x7 (by decide)).trans h7)) fun u₃ ⟨⟨h15, h16₃, h17₃, h14₃, m₃⟩, k₃⟩ => ?_)
  rw [hc₂, Bool.not_not] at h15
  have k13 := k12.trans k₃
  refine WP.mono (cswap_ok (h.scr.congr k13.wr) h16₃ h17₃ h15 h14₃ (by omega) (by omega) (by omega) (by omega)
    (by omega)) fun u ⟨hx, hy, f₄', k₄⟩ => ?_
  rw [m₃, m₂, m₁] at hx hy f₄'
  have f₄ : Frm B (rg w [fV, fQ] []) s.mem u.mem := f₄'.widen (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
    · exact rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega))
  refine ⟨f₄, (k13.trans k₄).mono (by decide), h.congrG f₄ (by simp) (k13.trans k₄) (by decide), ?_, ?_⟩
  · rw [hx]; split <;> rename_i hc <;> simp only [decide_eq_true_eq] at hc <;> omega
  · rw [hy]; split <;> rename_i hc <;> simp only [decide_eq_true_eq] at hc <;> omega

end VG.Proof.Rsa.AArch64
