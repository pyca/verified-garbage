import VerifiedGarbage.Proof.Rsa.AArch64.RpSq

/-!
# `vg_rsa_recover_primes` on AArch64: a candidate

`candBody` for the candidate `g = c + 2`: `y = g^r mod n` (`candA_ok`), the
start of the squarings from it (`candB_ok`), the squarings and the count of
the candidates (`candBody_ok`): `recoverStep n t r g`, the mask of whether it
found `y`, `y` in Montgomery form if so, and `x15` nonzero to go on unless
it did or it was the last.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Proof.Bignum (mont_cancel mont_sq powMod_eq)
open VG.Spec.Rsa (powMod recoverStep)
open VG.Proof.Rsa (sqStart sqIter sqRes sq_result)

/-- `gBlk`: `g = c + 2` into `x9`, `x13 := 0` and `w` into `x12`. -/
theorem gBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {c : Nat}
    (hcand : word s.mem B (8 * sCand) = BitVec.ofNat 64 c) :
    WP isa (.block gBlk) s fun u =>
      (u.gpr .x9 = BitVec.ofNat 64 (c + 2) ∧ u.gpr .x13 = BitVec.ofNat 64 0 ∧ u.gpr .x12 = BitVec.ofNat 64 w ∧
        u.mem = s.mem) ∧ Keep [.x9, .x12, .x13] s u := by
  have h256 := h.h256
  have hn := h.scr.nowrap
  refine WP.keep [.x9, .x12, .x13] (by
    brun [gBlk, h.x0, hdr_enc (show sCand < 32 by decide), hdr_enc (show sW < 32 by decide),
      h.scr.ld (d := 8 * sCand) (by simp only [sCand, sFn]; omega), h.scr.ld (d := 8 * sW) (by simp only [sW]; omega),
      hcand, h.hw, BitVec.ofNat_add_ofNat]) (by decide) (by decide) (by decide +kernel)

/-- The candidate's `y = g^r mod n`, in Montgomery form in `Y`. -/
theorem candA_ok (M : Mont) {u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t c : Nat}
    (hc : Cst u B Z w minv N el r t) (hcand : word u.mem B (8 * sCand) = BitVec.ofNat 64 c) (hc100 : c < 100) :
    WP isa (seqs [.block gBlk, setWord aX, M.mm aXm aX aR2, copyA aG aXm, copyA aY aO, expLoop M.mm]) u
      fun u' => Frm B (rg w [aX, aAcc, aTmp, aXm, aG, aY] [sC1, sC2, sC3]) u.mem u'.mem ∧ Keep mmRegs u u' ∧
        wv u'.mem B (slot w aY) w = powMod (c + 2) r N * 2 ^ (64 * w) % N := by
  have hZ16 := hc.hZ16
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have hR := hc.coprime
  have hN : 2 ^ 64 ≤ N := hc.n1
  simp only [seqs]
  refine WP.seq (WP.mono (gBlk_ok hc.ws hcand) fun u₁ ⟨⟨h9, h13, h12, m₁⟩, k₁⟩ => ?_)
  have hc₁ := hc.congr (js := []) (hs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) (by simp) k₁ (by decide)
  have hg₁ := hc₁.good
  refine WP.seq (WP.mono (setWord_ok hc₁.ws.scr hc₁.ws.x0 hg₁.1.hdr hg₁.2 h12 (by omega)
    (o := aX) (by decide) (i := 0) (by omega) h13) fun u₂ ⟨hx₂, o₂, k₂⟩ => ?_)
  rw [h9, BitVec.toNat_ofNat, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (by omega)] at hx₂
  have hf₂ : Frm B (rg w [aX] []) u₁.mem u₂.mem := Frm.rg_of_out o₂ (Nat.le_refl _) _ _ (by decide)
  have hc₂ := hc₁.congr hf₂ (by decide) (by simp) k₂ (by decide)
  have hg₂ := hc₂.good
  -- `g R mod n`.
  refine WP.seq (WP.mono (M.mm_ok hg₂.1 hg₂.2 hw1 (by omega) (o := aXm) (a := aX) (b := aR2) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₂.hinv
    (by rw [hc₂.hn]; exact hc₂.hr2lt)) fun u₃ ⟨_, hlt₃, hm₃, ha₃, k₃⟩ => ?_)
  rw [hc₂.hn] at hlt₃ hm₃
  rw [hx₂] at hm₃
  have hXm : wv u₃.mem B (slot w aXm) w % N = (c + 2) * 2 ^ (64 * w) % N := VG.Proof.Rsa.g_mont hR hc₂.hr2 hm₃
  have hf₃ : Frm B (rg w [aAcc, aTmp, aXm] []) u₂.mem u₃.mem := Frm.rg_of_arrays ha₃ _ _ (by decide)
  have hc₃ := hc₂.congr hf₃ (by decide) (by simp) k₃ (by decide)
  refine WP.seq (WP.mono (copyA_ok hc₃.ws (o := aG) (a := aXm) (by decide) (by decide) (by decide))
    fun u₄ ⟨hg₄, o₄, _, _, k₄⟩ => ?_)
  have hf₄ : Frm B (rg w [aG] []) u₃.mem u₄.mem := Frm.rg_of_out o₄ (by omega) _ _ (by decide)
  have hc₄ := hc₃.congr hf₄ (by decide) (by simp) k₄ (by decide)
  refine WP.seq (WP.mono (copyA_ok hc₄.ws (o := aY) (a := aO) (by decide) (by decide) (by decide))
    fun u₅ ⟨hy₅, o₅, _, _, k₅⟩ => ?_)
  have hf₅ : Frm B (rg w [aY] []) u₄.mem u₅.mem := Frm.rg_of_out o₅ (by omega) _ _ (by decide)
  have hc₅ := hc₄.congr hf₅ (by decide) (by simp) k₅ (by decide)
  rw [hc₄.ho] at hy₅
  have hG₅ : wv u₅.mem B (slot w aG) w = wv u₃.mem B (slot w aXm) w := by
    rw [hf₅.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hg₄]
  refine WP.mono (expLoop_ok M hc₅ (g := c + 2) (by rw [hG₅]; exact hlt₃) (by rw [hG₅]; exact hXm) hy₅)
    fun u' ⟨hf₆, k₆, hlt₆, hy₆⟩ => ⟨?_, ?_, ?_⟩
  · have hf₁ : Frm B (rg w [] []) u.mem u₁.mem := by rw [m₁]; exact Frm.refl _ _ _
    exact (((((hf₁.rg_trans hf₂).rg_trans hf₃).rg_trans hf₄).rg_trans hf₅).rg_trans hf₆).rg_mono
      (by decide) (by decide)
  · exact (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).mono (by decide)
  · rw [← Nat.mod_eq_of_lt hlt₆, hy₆, powMod_eq, Nat.mod_mul_mod]

/-- `chkBlk`: `done := y = -1 ∨ y = 1`, `ok := 0` and `k := 0`. -/
theorem chkBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {e1 : Bool}
    (hc2 : word s.mem B (8 * sC2) = mask e1) :
    WP isa (.block chkBlk) s fun u =>
      u.mem = ((s.mem.writeW (off B (8 * sC2)) (mask (decide (s.gpr .x9 = 0) || e1))).writeW (off B (8 * sC3))
        (mask false)).writeW (off B (8 * sC1)) (mask false) ∧ Keep [.x3, .x4, .x7, .x15] s u := by
  have h256 := h.h256
  have hn := h.scr.nowrap
  refine WP.mono (WP.keep [.x3, .x4, .x7, .x15] (Q := fun u => u.mem = ((s.mem.writeW (off B (8 * sC2))
      (mask (decide (s.gpr .x9 = 0) || e1))).writeW (off B (8 * sC3)) (mask false)).writeW (off B (8 * sC1))
        (mask false)) (by
    brun [chkBlk, zeroMask, borrowMask, h.x0, hdr_enc (show sC1 < 32 by decide), hdr_enc (show sC2 < 32 by decide),
      hdr_enc (show sC3 < 32 by decide), h.scr.ld (d := 8 * sC2) (by simp only [sC2, sFn]; omega),
      h.scr.st (d := 8 * sC2) (by simp only [sC2, sFn]; omega), h.scr.st (d := 8 * sC3) (by simp only [sC3, sFn]; omega),
      h.scr.st (d := 8 * sC1) (by simp only [sC1, sFn]; omega), hc2, csel_mask', subs_one_c, Bool.not_not,
      mask_or_mask]
    rfl) (by decide) (by decide) (by decide +kernel)) fun u ⟨a, b⟩ => ⟨a, b⟩

/-- The start of the squarings from `y` in Montgomery form in `Y`. -/
theorem candB_ok {u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t y : Nat}
    (hc : Cst u B Z w minv N el r t) (hY : wv u.mem B (slot w aY) w = y * 2 ^ (64 * w) % N) (hy : y < N) :
    WP isa (seqs (eqA aY aO ++ (([.block (zeroMask ++ [sth .x15 sC2])] : List (Prog isa)) ++
      (eqA aY aNg ++ ([.block chkBlk] : List (Prog isa)))))) u fun u' =>
      Frm B (rg w [] [sC1, sC2, sC3]) u.mem u'.mem ∧ Keep mmRegs u u' ∧
      word u'.mem B (8 * sC2) = mask (sqStart N y).2.1 ∧ word u'.mem B (8 * sC3) = mask (sqStart N y).2.2 ∧
      word u'.mem B (8 * sC1) = BitVec.ofNat 64 0 := by
  have hR := hc.coprime
  have hN1 : 1 < N := by have := hc.n1; omega
  have h256 := hc.ws.h256
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok hc.ws (a := aY) (b := aO) (by decide)
    (by decide)) fun u₁ ⟨hz₁, m₁, _, _, k₁⟩ => ?_)
  rw [hY, hc.ho, VG.Proof.Rsa.eq_one_mont hR hN1 hy rfl] at hz₁
  have hc₁ := hc.congr (js := []) (hs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) (by simp) k₁ (by decide)
  refine wp_seqs_append (by simp) (by simp [eqA]) (WP.mono (zstore_ok hc₁.ws (i := sC2) (by decide) (by decide))
    fun u₂ ⟨⟨_, m₂⟩, k₂⟩ => ?_)
  rw [show decide (u₁.gpr .x9 = 0) = decide (y = 1) from decide_eq_decide.mpr hz₁] at m₂
  have hf₂ : Frm B (rg w [] [sC2]) u₁.mem u₂.mem := by
    rw [m₂]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hc₂ := hc₁.congr hf₂ (by decide) (by decide) k₂ (by decide)
  have hY₂ : wv u₂.mem B (slot w aY) w = y * 2 ^ (64 * w) % N := by
    rw [hf₂.rg_wv hc.hZ16 (by decide) (by decide) (by decide) (by omega), m₁, hY]
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok hc₂.ws (a := aY) (b := aNg) (by decide)
    (by decide)) fun u₃ ⟨hz₃, m₃, _, _, k₃⟩ => ?_)
  rw [hY₂, hc₂.hng, VG.Proof.Rsa.eq_neg_mont hR hN1 hy rfl] at hz₃
  have hc₃ := hc₂.congr (js := []) (hs := []) (by rw [m₃]; exact Frm.refl _ _ _) (by simp) (by simp) k₃ (by decide)
  refine WP.mono (chkBlk_ok hc₃.ws (e1 := decide (y = 1)) (by rw [m₃, m₂, word_writeW_self]))
    fun u' ⟨m₄, k₄⟩ => ?_
  rw [show decide (u₃.gpr .x9 = 0) = decide (y = N - 1) from decide_eq_decide.mpr hz₃] at m₄
  have hf₄ : Frm B (rg w [] [sC1, sC2, sC3]) u₃.mem u'.mem := by
    rw [m₄]
    exact ((Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) [] [sC1, sC2, sC3] (by decide)).trans
      (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC3, sFn]; omega)) [] [sC1, sC2, sC3] (by decide))).trans
      (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC1, sFn]; omega)) [] [sC1, sC2, sC3] (by decide))
  have hw3 : ∀ m : Mem, ∀ v₁ v₂ : BitVec 64, word ((m.writeW (off B (8 * sC3)) v₁).writeW (off B (8 * sC1)) v₂) B
      (8 * sC2) = word m B (8 * sC2) := fun m v₁ v₂ => by
    rw [(writeW_outside _ B _ (d := 8 * sC1) (by simp only [sC1, sFn]; omega)).word
      (Or.inr (by simp only [sC1, sC2, sFn]; omega)) (by simp only [sC2, sFn]; omega),
      (writeW_outside _ B _ (d := 8 * sC3) (by simp only [sC3, sFn]; omega)).word
      (Or.inl (by simp only [sC2, sC3, sFn]; omega)) (by simp only [sC2, sFn]; omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hf₁ : Frm B (rg w [] []) u.mem u₁.mem := by rw [m₁]; exact Frm.refl _ _ _
    have hf₃ : Frm B (rg w [] []) u₂.mem u₃.mem := by rw [m₃]; exact Frm.refl _ _ _
    exact (((hf₁.rg_trans hf₂).rg_trans hf₃).rg_trans hf₄).rg_mono (by decide) (by decide)
  · exact (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)
  · rw [m₄, hw3, word_writeW_self, sqStart, Bool.or_comm]
  · rw [m₄, (writeW_outside _ B _ (d := 8 * sC1) (by simp only [sC1, sFn]; omega)).word
      (Or.inr (by simp only [sC1, sC3, sFn]; omega)) (by simp only [sC3, sFn]; omega), word_writeW_self]
    rfl
  · rw [m₄, word_writeW_self]; rfl

theorem mask_xor_true (a : Bool) : mask a ^^^ mask true = mask (!a) := by
  cases a <;> rfl

/-- `candNext`: the candidates tried `+= 1`, and `x15` the mask of going on:
fewer than 100 tried and not `ok`. -/
theorem candNext_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {c : Nat} {ok : Bool}
    (hcand : word s.mem B (8 * sCand) = BitVec.ofNat 64 c) (hc3 : word s.mem B (8 * sC3) = mask ok)
    (hc : c < 100) :
    WP isa (.block candNext) s fun u =>
      (u.gpr .x15 = mask (decide (c + 1 < 100) && !ok) ∧
        u.mem = s.mem.writeW (off B (8 * sCand)) (BitVec.ofNat 64 (c + 1))) ∧ Keep [.x3, .x4, .x7, .x15] s u := by
  have h256 := h.h256
  have hn := h.scr.nowrap
  have ec : (BitVec.ofNat 64 (c + 1)).toNat = c + 1 := by rw [BitVec.toNat_ofNat]; omega
  have e100 : (BitVec.setWidth 64 (100#16)).toNat = 100 := rfl
  have hr3 : ∀ v, (s.mem.writeW (off B (8 * sCand)) v).readW (off B (8 * sC3)) 64 = mask ok := fun v => by
    have o := writeW_outside s.mem B v (d := 8 * sCand) (by simp only [sCand, sFn]; omega)
    have := o.word (d := 8 * sC3) (Or.inr (by simp only [sCand, sC3, sFn]; omega)) (by simp only [sC3, sFn]; omega)
    rw [hc3] at this
    exact this
  have e : candNext = ([ldh .x3 sCand, .addImm .x .x3 .x3 1, sth .x3 sCand, movi .x4 100, movi .x7 0,
      .subs .x .x3 .x3 .x4] ++ borrowMask) ++ [ldh .x3 sC3, .logic .eor .x .x3 .x3 .x4, .logic .and .x .x15 .x15 .x3] :=
    rfl
  rw [e, WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x7, .x15] (Q := fun u => u.gpr .x15 = mask (decide (c + 1 < 100)) ∧
      u.gpr .x4 = mask true ∧ u.mem = s.mem.writeW (off B (8 * sCand)) (BitVec.ofNat 64 (c + 1))) (by
    brun [borrowMask, h.x0, hdr_enc (show sCand < 32 by decide),
      h.scr.ld (d := 8 * sCand) (by simp only [sCand, sFn]; omega),
      h.scr.st (d := 8 * sCand) (by simp only [sCand, sFn]; omega), hcand, BitVec.ofNat_add_ofNat,
      csel_mask', subs_c_nat _ (show c + 1 < 2 ^ 64 by omega), ec, e100, Bool.not_not]) (by decide) (by decide) (by decide +kernel)) fun u₁ ⟨⟨h15, h4, m₁⟩, k₁⟩ => ?_
  refine WP.mono (WP.keep [.x3, .x15] (Q := fun u => u.gpr .x15 = mask (decide (c + 1 < 100) && !ok) ∧
      u.mem = u₁.mem) (by
    brun [(k₁.gpr .x0 (by decide)).trans h.x0, hdr_enc (show sC3 < 32 by decide),
      (h.scr.congr k₁.wr).ld (d := 8 * sC3) (by simp only [sC3, sFn]; omega), m₁, hr3, h15, h4, mask_xor_true,
      mask_and']) (by decide) (by decide) (by decide +kernel)) fun u ⟨⟨h15', m₂⟩, k₂⟩ =>
      ⟨⟨h15', by rw [m₂, m₁]⟩, (k₁.trans k₂).mono (by decide)⟩

/-- The arrays and slots a candidate changes. -/
def candJs : List Nat := [aX, aAcc, aTmp, aXm, aG, aY]
def candHs : List Nat := [sMask, sC1, sC2, sC3, sCand]

theorem cand_hs : ∀ i ∈ candHs, rSlot i = true ∧ i ≠ sMinv ∧ i ≠ sT := by decide

/-- A candidate, `g = c + 2`: `recoverStep n t r g`. -/
theorem candBody_ok (M : Mont) {u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t c : Nat}
    (hc : Cst u B Z w minv N el r t) (hcand : word u.mem B (8 * sCand) = BitVec.ofNat 64 c) (hc100 : c < 100) :
    WP isa (candBody M.mm) u fun u' =>
      u'.gpr .x15 = mask (decide (c + 1 < 100) && !(recoverStep N t r (c + 2)).isSome) ∧
      Frm B (rg w candJs candHs) u.mem u'.mem ∧ Keep mmRegs u u' ∧
      word u'.mem B (8 * sCand) = BitVec.ofNat 64 (c + 1) ∧
      word u'.mem B (8 * sC3) = mask (recoverStep N t r (c + 2)).isSome ∧
      (∀ y, recoverStep N t r (c + 2) = some y →
        wv u'.mem B (slot w aY) w = y * 2 ^ (64 * w) % N ∧ y < N) := by
  have hZ16 := hc.hZ16
  have hN : 0 < N := by have := hc.n1; omega
  have he2 := hc.e2
  have hw2 := hc.ws.w2
  have h256 := hc.ws.h256
  rw [show candBody M.mm = seqs ([.block gBlk, setWord aX, M.mm aXm aX aR2, copyA aG aXm, copyA aY aO,
      expLoop M.mm] ++ ((eqA aY aO ++ ([.block (zeroMask ++ [sth .x15 sC2])] ++ (eqA aY aNg ++ [.block chkBlk]))) ++
        [.loop (sqBody M.mm) (.nonzero .x .x3), .block candNext])) by
    simp only [candBody, List.append_assoc, List.cons_append, List.nil_append]]
  refine wp_seqs_append (by simp) (by simp [eqA]) (WP.mono (candA_ok M hc hcand hc100) fun u₁ ⟨hf₁, k₁, hY₁⟩ => ?_)
  have hc₁ := hc.congr hf₁ (by decide) (by decide) k₁ (by decide)
  have hy0 : powMod (c + 2) r N < N := by rw [powMod_eq]; exact Nat.mod_lt _ hN
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (candB_ok hc₁ hY₁ hy0)
    fun u₂ ⟨hf₂, k₂, hc2, hc3, hc1⟩ => ?_)
  have hc₂ := hc₁.congr hf₂ (by decide) (by decide) k₂ (by decide)
  have hY₂ : wv u₂.mem B (slot w aY) w = powMod (c + 2) r N * 2 ^ (64 * w) % N := by
    rw [hf₂.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hY₁]
  simp only [seqs]
  refine WP.seq (WP.mono (count_loop (cr := .x3) (n := 64 * (w + (el + 7) / 8)) (by have := hc.ws.w1; omega)
    (SqI u₂ B w N t (sqStart N (powMod (c + 2) r N))) (fun k hk v hv => sqBody_ok M hc₂ hk hv)
    ⟨Frm.refl _ _ _, Keep.refl _ _, hY₂, hy0, hc1, hc2, hc3⟩) fun v hv => ?_)
  have hc₃ := hc₂.congr hv.frm (by decide) sq_hs hv.keep (by decide)
  have hres := sq_result (n := N) (r := r) (g := c + 2) hc.t1 (Nat.le_of_lt hc.t2)
  have hy := hv.y
  have hylt := hv.ylt
  have hc3v := hv.c3
  generalize sqIter N t (64 * (w + (el + 7) / 8)) (sqStart N (powMod (c + 2) r N)) = st at hres hy hylt hc3v
  obtain ⟨yk, done, ok⟩ := st
  dsimp only at hy hylt hc3v
  have hcand₃ : word v.mem B (8 * sCand) = BitVec.ofNat 64 c := by
    rw [hv.frm.rg_word (by decide) (by decide), hf₂.rg_word (by decide) (by decide),
      hf₁.rg_word (by decide) (by decide)]; exact hcand
  have hok : (recoverStep N t r (c + 2)).isSome = ok := by
    rw [← hres]; cases ok <;> rfl
  refine WP.mono (candNext_ok hc₃.ws hcand₃ hc3v hc100) fun u' ⟨⟨h15, m₄⟩, k₄⟩ => ?_
  have hf₄ : Frm B (rg w [] [sCand]) v.mem u'.mem := by
    rw [m₄]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sCand, sFn]; omega))
      _ _ (List.mem_singleton_self _)
  refine ⟨by rw [h15, hok], ?_, ?_, by rw [m₄, word_writeW_self], ?_, ?_⟩
  · exact (((hf₁.rg_trans hf₂).rg_trans hv.frm).rg_trans hf₄).rg_mono (by decide) (by decide)
  · exact (((k₁.trans k₂).trans hv.keep).trans k₄).mono (by decide)
  · rw [hf₄.rg_word (by decide) (by decide), hc3v, hok]
  · intro y hsome
    rw [← hres] at hsome
    cases ok
    · cases hsome
    · simp only [sqRes, ite_true, Option.some.injEq] at hsome
      subst hsome
      rw [hf₄.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]
      exact ⟨hy, hylt⟩

end VG.Proof.Rsa.AArch64
