import VerifiedGarbage.Proof.Rsa.X86_64.RpCst

/-!
# `vg_rsa_recover_primes` on x86-64: `y = g^r`

`expLoop`: for each word of `r` from the top, and each of its bits from the
top, `Y := Y² · (bit ? G : O)` in Montgomery form, the multiplicand chosen
by a mask: `Y ≡ g^r R` (`expLoop_ok`), for `G ≡ g R` and `Y ≡ R` on entry.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt)
open VG.Proof.Bignum (mont_cancel mont_sq)

/-! ## Bits -/

/-- The top bit of a word shifted left by `j`. -/
theorem top_bit {W j : Nat} (hj : j < 64) : W * 2 ^ j % 2 ^ 64 / 2 ^ 63 = W / 2 ^ (63 - j) % 2 := by
  have e1 : 2 ^ 64 = 2 ^ (64 - j) * 2 ^ j := by rw [← Nat.pow_add]; congr 1; omega
  have e2 : 2 ^ 63 = 2 ^ (63 - j) * 2 ^ j := by rw [← Nat.pow_add]; congr 1; omega
  have e3 : 2 ^ (64 - j) = 2 ^ (63 - j) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
  rw [e1, Nat.mul_mod_mul_right, e2, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos j), e3,
    Nat.mod_mul_right_div_self]

/-- Bit `63 - j` of word `i` of `r`. -/
theorem word_bit (r i : Nat) {j : Nat} (hj : j < 64) :
    r / 2 ^ (64 * i) % 2 ^ 64 / 2 ^ (63 - j) % 2 = r / 2 ^ (64 * i + (63 - j)) % 2 := by
  have e : 2 ^ 64 = 2 ^ (63 - j) * 2 ^ (j + 1) := by rw [← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (show 1 ≤ j + 1 by omega)),
    Nat.pow_one, Nat.div_div_eq_div_mul, ← Nat.pow_add]

/-- One more bit of `r`. -/
theorem prefix_step (r a : Nat) : r / 2 ^ a = 2 * (r / 2 ^ (a + 1)) + r / 2 ^ a % 2 := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]; omega

/-- One more bit of a word's prefix. -/
theorem prefix_step' (e : Nat) {j : Nat} (hj : j < 64) :
    e / 2 ^ (64 - (j + 1)) = 2 * (e / 2 ^ (64 - j)) + e / 2 ^ (63 - j) % 2 := by
  have := prefix_step e (63 - j)
  rw [show 63 - j + 1 = 64 - j by omega, show 63 - j = 64 - (j + 1) by omega] at this
  rw [show 63 - j = 64 - (j + 1) by omega]
  exact this

/-- A Montgomery multiplication of `Y ≡ x^E R` by `X ≡ x^b R`. -/
theorem mont_mulp {Y Y' X x E b R m : Nat} (hR : Nat.Coprime R m) (hY : Y % m = x ^ E * R % m)
    (hX : X % m = x ^ b * R % m) (h : Y' * R % m = Y * X % m) : Y' % m = x ^ (E + b) * R % m := by
  apply mont_cancel hR
  rw [h, Nat.mul_mod, hY, hX, ← Nat.mul_mod, Nat.pow_add, Nat.mul_mul_mul_comm, Nat.mul_assoc (x ^ E * x ^ b)]

theorem shr63 (x : BitVec 64) : x >>> 63 = BitVec.ofNat 64 (x.toNat / 2 ^ 63) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by have := x.isLt; omega)]

theorem bit_sub_one {b : Nat} (hb : b ≤ 1) : BitVec.ofNat 64 b - 1 = mask (decide (b = 0)) := by
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> decide

theorem dbl_mod (V : Nat) : BitVec.ofNat 64 V + BitVec.ofNat 64 V = BitVec.ofNat 64 (V * 2 % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-! ## A bit -/

/-- `bitSel`: the top bit of `sC2` out of it, `rbp` the mask of it clear,
and the bases of the multiplicand and of `G`. -/
theorem bitSel_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {V : Nat}
    (hc2 : word s.mem B (8 * sC2) = BitVec.ofNat 64 V) (hV : V < 2 ^ 64) :
    WP isa (.block bitSel) s fun t =>
      t.gpr .rbp = mask (decide (V / 2 ^ 63 = 0)) ∧ t.gpr .r8 = off B (slot w aXm) ∧
      t.gpr .rsi = off B (slot w aG) ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.mem = s.mem.writeW (off B (8 * sC2)) (BitVec.ofNat 64 (V * 2 % 2 ^ 64)) ∧
      Keep [.rax, .rdx, .rbp, .r12, .r9, .r8, .rsi] s t := by
  have h256 := h.h256
  have hn := h.scr.nowrap
  unfold bitSel
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx, .rbp] (Q := fun t => t.gpr .rbp = mask (decide (V / 2 ^ 63 = 0)) ∧
      t.mem = s.mem.writeW (off B (8 * sC2)) (BitVec.ofNat 64 (V * 2 % 2 ^ 64))) (by
    xrun [State.ea, hdr, h.rdi, hdrOff, h.scr.ld (d := 8 * sC2) (by simp only [sC2, sFn]; omega),
      h.scr.st (d := 8 * sC2) (by simp only [sC2, sFn]; omega), hc2, shr63, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hV, bit_sub_one (show V / 2 ^ 63 ≤ 1 by omega), dbl_mod]) rfl)
    fun t₁ ⟨⟨hbp, m₁⟩, k₁⟩ => ?_
  have hw₁ : Ws t₁ B Z w := h.congrG (js := []) (hs := [sC2]) (by
    rw [m₁]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) _ _
      (List.mem_singleton_self _)) (by decide) k₁ (by decide)
  refine WP.block_append_iff.mpr (WP.mono hw₁.ws_ok fun t₂ ⟨h12, h9, m₂, k₂⟩ => WP.block_append_iff.mpr ?_)
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans hw₁.rdi
  refine WP.mono (base_ok aXm (r := .r8) (by decide) hdi₂ h9) fun t₃ ⟨h8, m₃, k₃⟩ => ?_
  refine WP.mono (base_ok aG (r := .rsi) (by decide) ((k₃.gpr (by decide)).trans hdi₂)
    ((k₃.gpr (by decide)).trans h9)) fun t ⟨hsi, m₄, k₄⟩ => ?_
  exact ⟨(k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hbp)),
    (k₄.gpr (by decide)).trans h8, hsi, (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans h12),
    by rw [m₄, m₃, m₂, m₁], (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩

/-- Bit `63 - j` of a number's low word. -/
theorem low_bit (e : Nat) {j : Nat} (hj : j < 64) : e % 2 ^ 64 / 2 ^ (63 - j) % 2 = e / 2 ^ (63 - j) % 2 := by
  have := word_bit e 0 hj
  simpa using this

/-- A counter in header slot `i`, decremented: `ZF` set when it reaches 0. -/
theorem ctrDec_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {i a : Nat} (hi : 16 ≤ i) (hi' : i < 32)
    (hc : word s.mem B (8 * i) = BitVec.ofNat 64 a) (ha : 1 ≤ a) (ha' : a < 2 ^ 63) :
    WP isa (.block [.mov .rax (.mem (hdr i)), .alu .sub .rax (.imm 1), .store (hdr i) .rax]) s fun t =>
      t.zf = some (decide (a = 1)) ∧ t.mem = s.mem.writeW (off B (8 * i)) (BitVec.ofNat 64 (a - 1)) ∧
      Keep [.rax] s t := by
  have h256 := h.h256
  have e1 : BitVec.ofNat 64 a - 1 = BitVec.ofNat 64 (a - 1) := ofNat64_pred ha (by omega)
  have e2 : (BitVec.ofNat 64 a - 1 == 0) = decide (a = 1) := ofNat_sub_beq (N := 1) (by omega) (by omega)
  rw [e1] at e2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (a = 1)) ∧
      t.mem = s.mem.writeW (off B (8 * i)) (BitVec.ofNat 64 (a - 1))) (by
    xrun [State.ea, hdr, h.rdi, hdrOff, h.scr.ld (d := 8 * i) (by omega), h.scr.st (d := 8 * i) (by omega), hc,
      e2, e1]) rfl) fun t ⟨⟨hz, mt⟩, k⟩ => ⟨hz, mt, k⟩

/-- After `j` bits of `e`'s low word `V`, from `t₀`. -/
structure BitInv (t₀ : State) (B : Addr) (w N g e V j : Nat) (u : State) : Prop where
  frm : Frm B (rg w [aAcc, aTmp, aXm, aY] [sC2, sC3]) t₀.mem u.mem
  keep : Keep mmRegs t₀ u
  ylt : wv u.mem B (slot w aY) w < N
  y : wv u.mem B (slot w aY) w % N = g ^ (e / 2 ^ (64 - j)) * 2 ^ (64 * w) % N
  c2 : word u.mem B (8 * sC2) = BitVec.ofNat 64 (V * 2 ^ j % 2 ^ 64)
  c3 : word u.mem B (8 * sC3) = BitVec.ofNat 64 (64 - j)

theorem bit_hs : ∀ i ∈ [sC2, sC3], rSlot i = true ∧ i ≠ sMinv ∧ i ≠ sT := by decide

/-- A bit. -/
theorem bitBody_ok (M : Mont) {t₀ u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t g e V j : Nat}
    (hc : Cst t₀ B Z w minv N el r t) (hGlt : wv t₀.mem B (slot w aG) w < N)
    (hG : wv t₀.mem B (slot w aG) w % N = g * 2 ^ (64 * w) % N) (hV : V = e % 2 ^ 64) (hj : j < 64)
    (hI : BitInv t₀ B w N g e V j u) :
    WP isa (bitBody M.mm) u fun u' => u'.zf = some (decide (j + 1 = 64)) ∧ BitInv t₀ B w N g e V (j + 1) u' := by
  have hZ16 := hc.hZ16
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have hR := hc.coprime
  have hcu : Cst u B Z w minv N el r t := hc.congr hI.frm (by decide) bit_hs hI.keep (by decide)
  have hGu : wv u.mem B (slot w aG) w = wv t₀.mem B (slot w aG) w :=
    hI.frm.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)
  simp only [bitBody, seqs]
  -- The multiplicand `1`.
  refine WP.seq (WP.mono (copyA_ok hcu.ws (o := aXm) (a := aO) (by decide) (by decide) (by decide))
    fun u₁ ⟨hx₁, o₁, k₁⟩ => ?_)
  have hf₁ : Frm B (rg w [aXm] []) u.mem u₁.mem := Frm.rg_of_out o₁ (by omega) _ _ (by decide)
  have hc₁ := hcu.congr hf₁ (by decide) (by simp) k₁ (by decide)
  rw [hcu.ho] at hx₁
  have hc2₁ : word u₁.mem B (8 * sC2) = BitVec.ofNat 64 (V * 2 ^ j % 2 ^ 64) := by
    rw [hf₁.rg_word (by decide) (by simp)]; exact hI.c2
  -- The bit.
  refine WP.seq (WP.mono (bitSel_ok hc₁.ws hc2₁ (Nat.mod_lt _ (by decide)))
    fun u₂ ⟨hbp, h8, hsi, h12, m₂, k₂⟩ => ?_)
  have hf₂ : Frm B (rg w [] [sC2]) u₁.mem u₂.mem := by
    rw [m₂]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hc₂ := hc₁.congr hf₂ (by decide) (by decide) k₂ (by decide)
  have hs₂ := hc₂.ws.scr
  have sXm := hc₂.ws.sl (j := aXm) (by decide)
  have sG := hc₂.ws.sl (j := aG) (by decide)
  refine WP.seq (WP.mono (sel_ok hs₂ h8 hsi hbp h12 (by omega) (by omega) (by omega) (by omega)
    (by have := slot_far (w := w) (show aXm ≠ aG by decide); omega)) fun u₃ ⟨hx₃, o₃, k₃⟩ => ?_)
  have hf₃ : Frm B (rg w [aXm] []) u₂.mem u₃.mem := Frm.rg_of_out o₃ (by omega) _ _ (by decide)
  have hc₃ := hc₂.congr hf₃ (by decide) (by simp) k₃ (by decide)
  -- The multiplicand: `G ≡ g R` or `R mod n ≡ g^0 R`.
  have hb : V * 2 ^ j % 2 ^ 64 / 2 ^ 63 = e / 2 ^ (63 - j) % 2 := by rw [top_bit hj, hV, low_bit e hj]
  have hX : wv u₃.mem B (slot w aXm) w % N = g ^ (e / 2 ^ (63 - j) % 2) * 2 ^ (64 * w) % N ∧
      wv u₃.mem B (slot w aXm) w < N := by
    rw [hx₃, hf₂.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hx₁,
      hf₂.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega),
      hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hGu, hb]
    have hNp : 0 < N := by have := hc.n1; omega
    rcases Nat.mod_two_eq_zero_or_one (e / 2 ^ (63 - j)) with h0 | h1
    · simp only [h0, decide_true, ite_true, Nat.pow_zero, Nat.one_mul, Nat.mod_mod]
      exact ⟨trivial, Nat.mod_lt _ hNp⟩
    · simp only [h1, Nat.one_ne_zero, decide_false, Bool.false_eq_true, ite_false, Nat.pow_one]
      exact ⟨hG, hGlt⟩
  have hY₃ : wv u₃.mem B (slot w aY) w = wv u.mem B (slot w aY) w := by
    rw [hf₃.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega),
      hf₂.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega),
      hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]
  -- `Y := Y²`.
  have hg₃ := hc₃.good
  refine WP.seq (WP.mono (M.mm_ok hg₃.1 hg₃.2 hw1 (by omega) (o := aY) (a := aY) (b := aY) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₃.hinv
    (by rw [hY₃, hc₃.hn]; exact hI.ylt)) fun u₄ ⟨hg₄, hlt₄, hm₄, ha₄, k₄⟩ => ?_)
  rw [hc₃.hn] at hlt₄ hm₄
  have hf₄ : Frm B (rg w [aAcc, aTmp, aY] []) u₃.mem u₄.mem := Frm.rg_of_arrays ha₄ _ _ (by decide)
  have hc₄ := hc₃.congr hf₄ (by decide) (by simp) k₄ (by decide)
  have hY₄ : wv u₄.mem B (slot w aY) w % N = g ^ (2 * (e / 2 ^ (64 - j))) * 2 ^ (64 * w) % N :=
    mont_sq hR (by rw [hY₃]; exact hI.y) hm₄
  -- `Y := Y · X`.
  have hX₄ : wv u₄.mem B (slot w aXm) w = wv u₃.mem B (slot w aXm) w :=
    hf₄.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)
  have hg₄' := hc₄.good
  refine WP.seq (WP.mono (M.mm_ok hg₄'.1 hg₄'.2 hw1 (by omega) (o := aY) (a := aY) (b := aXm) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₄.hinv
    (by rw [hX₄, hc₄.hn]; exact hX.2)) fun u₅ ⟨hg₅, hlt₅, hm₅, ha₅, k₅⟩ => ?_)
  rw [hc₄.hn] at hlt₅ hm₅
  have hf₅ : Frm B (rg w [aAcc, aTmp, aY] []) u₄.mem u₅.mem := Frm.rg_of_arrays ha₅ _ _ (by decide)
  have hc₅ := hc₄.congr hf₅ (by decide) (by simp) k₅ (by decide)
  have hY₅ := mont_mulp hR hY₄ (by rw [hX₄]; exact hX.1) hm₅
  rw [← prefix_step' e hj] at hY₅
  -- The bits left.
  have hc3₅ : word u₅.mem B (8 * sC3) = BitVec.ofNat 64 (64 - j) := by
    rw [hf₅.rg_word (by decide) (by simp), hf₄.rg_word (by decide) (by simp), hf₃.rg_word (by decide) (by simp),
      hf₂.rg_word (by decide) (by decide), hf₁.rg_word (by decide) (by simp)]; exact hI.c3
  refine WP.mono (ctrDec_ok hc₅.ws (i := sC3) (by decide) (by decide) hc3₅ (by omega) (by omega))
    fun u' ⟨hz, m₆, k₆⟩ => ⟨by rw [hz]; congr 1; exact decide_eq_decide.mpr (by omega), ?_⟩
  have hf₆ : Frm B (rg w [] [sC3]) u₅.mem u'.mem := by
    rw [m₆]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC3, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((((((hI.frm.rg_trans hf₁).rg_trans hf₂).rg_trans hf₃).rg_trans hf₄).rg_trans hf₅).rg_trans
      hf₆).rg_mono (by decide) (by decide))
  · exact ((((((hI.keep.trans k₁).trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).mono (by decide)
  · rw [hf₆.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hlt₅
  · rw [hf₆.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hY₅
  · rw [hf₆.rg_word (by decide) (by decide), hf₅.rg_word (by decide) (by simp),
      hf₄.rg_word (by decide) (by simp), hf₃.rg_word (by decide) (by simp), m₂, word_writeW_self]
    congr 1
    rw [show 2 ^ (j + 1) = 2 ^ j * 2 from Nat.pow_succ .., ← Nat.mul_assoc, Nat.mod_mul_mod]
  · rw [m₆, word_writeW_self]; congr 1

/-! ## A word -/

/-- `wordHead`: word `i` of `M` into `sC2`, for `sC1 = i + 1`, and 64 bits
left in `sC3`. -/
theorem wordHead_ok {u : State} {B : Addr} {Z w : Nat} (h : Ws u B Z w) {i : Nat}
    (hc1 : word u.mem B (8 * sC1) = BitVec.ofNat 64 (i + 1)) (hi : slot w aM + 8 * i + 8 ≤ Z) (hi' : i + 1 < 2 ^ 63) :
    WP isa (.block wordHead) u fun u' =>
      u'.mem = (u.mem.writeW (off B (8 * sC2)) (word u.mem B (slot w aM + 8 * i))).writeW (off B (8 * sC3))
        (BitVec.ofNat 64 64) ∧ Keep [.r12, .r9, .rbx, .rax] u u' := by
  have h256 := h.h256
  unfold wordHead
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun u₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aM (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9)
    fun u₂ ⟨hbx, m₂, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := h.scr.congr k12.2.2
  have hdi₂ : u₂.gpr .rdi = B := (k12.gpr (by decide)).trans h.rdi
  have e1 : BitVec.ofNat 64 (i + 1) - 1 = BitVec.ofNat 64 i := by
    rw [ofNat64_pred (by omega) (by omega)]; rfl
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem =
      (u.mem.writeW (off B (8 * sC2)) (word u.mem B (slot w aM + 8 * i))).writeW (off B (8 * sC3))
        (BitVec.ofNat 64 64)) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * sC1) (by simp only [sC1, sCnt, sFn]; omega),
      hs₂.st (d := 8 * sC2) (by simp only [sC2, sFn]; omega), hs₂.st (d := 8 * sC3) (by simp only [sC3, sFn]; omega),
      m₂, m₁, hc1, e1, ix, addr0 hbx rfl, hs₂.ld (d := slot w aM + 8 * i) hi]
    rfl) rfl) fun u' ⟨mt, k₃⟩ => ⟨mt, (k12.trans k₃).mono (by decide)⟩

/-- After `k` words of `r` (from the top), from `t₀`. -/
structure WordInv (t₀ : State) (B : Addr) (w N g r Bw k : Nat) (u : State) : Prop where
  frm : Frm B (rg w [aAcc, aTmp, aXm, aY] [sC1, sC2, sC3]) t₀.mem u.mem
  keep : Keep mmRegs t₀ u
  ylt : wv u.mem B (slot w aY) w < N
  y : wv u.mem B (slot w aY) w % N = g ^ (r / 2 ^ (64 * (Bw - k))) * 2 ^ (64 * w) % N
  c1 : word u.mem B (8 * sC1) = BitVec.ofNat 64 (Bw - k)

theorem word_hs : ∀ i ∈ [sC1, sC2, sC3], rSlot i = true ∧ i ≠ sMinv ∧ i ≠ sT := by decide

/-- A word. -/
theorem wordStep_ok (M : Mont) {t₀ u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t g k : Nat}
    (hc : Cst t₀ B Z w minv N el r t) (hGlt : wv t₀.mem B (slot w aG) w < N)
    (hG : wv t₀.mem B (slot w aG) w % N = g * 2 ^ (64 * w) % N) (hk : k < w + (el + 7) / 8)
    (hI : WordInv t₀ B w N g r (w + (el + 7) / 8) k u) :
    WP isa (.seq (.block wordHead) (.seq (.loop (bitBody M.mm) .ne) (.block wordNext))) u fun u' =>
      u'.zf = some (decide (k + 1 = w + (el + 7) / 8)) ∧ WordInv t₀ B w N g r (w + (el + 7) / 8) (k + 1) u' := by
  have hZ16 := hc.hZ16
  have he2 := hc.e2
  have hw2 := hc.ws.w2
  obtain ⟨Bw, hBw⟩ : ∃ Bw, w + (el + 7) / 8 = Bw := ⟨_, rfl⟩
  have hm := hc.hm
  rw [hBw] at hk hI hm ⊢
  have hBw2 : Bw ≤ 2 * (w + 2) := by omega
  have hcu : Cst u B Z w minv N el r t := hc.congr hI.frm (by decide) word_hs hI.keep (by decide)
  obtain ⟨i, hi⟩ : ∃ i, Bw - k = i + 1 := ⟨Bw - k - 1, by omega⟩
  have hc1 := hI.c1
  rw [hi] at hc1
  have sM := slot_lt (w := w) (show aM + 1 < 16 by decide)
  have eM1 : slot w (aM + 1) = slot w aM + 8 * (w + 2) := by simp only [slot, hdrBytes, aM]; omega
  have hZ := hcu.ws.hZ
  refine WP.seq (WP.mono (wordHead_ok hcu.ws hc1 (by omega) (by omega)) fun u₁ ⟨m₁, k₁⟩ => ?_)
  -- The word.
  have hW : (word u.mem B (slot w aM + 8 * i)).toNat = r / 2 ^ (64 * i) % 2 ^ 64 := by
    have := word_of_wv u.mem B (slot w aM) Bw (q := i) (by omega)
    have hmu := hcu.hm
    rw [hBw] at hmu
    rw [hmu] at this
    exact this
  have hf₁ : Frm B (rg w [] [sC2, sC3]) u.mem u₁.mem := by
    rw [m₁]
    exact (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) [] [sC2, sC3] (by decide)).trans
      (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC3, sFn]; omega)) [] [sC2, sC3] (by decide))
  have hc₁ := hcu.congr hf₁ (by decide) (by decide) k₁ (by decide)
  have hGu : wv u₁.mem B (slot w aG) w = wv t₀.mem B (slot w aG) w := by
    rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega),
      hI.frm.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]
  -- The bits of the word.
  have hpow : r / 2 ^ (64 * i) / 2 ^ (64 - 0) = r / 2 ^ (64 * (Bw - k)) := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, hi, Nat.sub_zero, Nat.mul_succ]
  have hW' : word u.mem B (slot w aM + 8 * i) = BitVec.ofNat 64 (r / 2 ^ (64 * i) % 2 ^ 64 * 2 ^ 0 % 2 ^ 64) := by
    rw [← hW, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (BitVec.isLt _), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hB0 : BitInv u₁ B w N g (r / 2 ^ (64 * i)) (r / 2 ^ (64 * i) % 2 ^ 64) 0 u₁ := by
    refine ⟨Frm.refl _ _ _, Keep.refl _ _, ?_, ?_, ?_, ?_⟩
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hI.ylt
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hpow]; exact hI.y
    · rw [m₁, (writeW_outside _ B _ (d := 8 * sC3) (by simp only [sC3, sFn]; omega)).word
        (Or.inl (by simp only [sC2, sC3, sFn]; omega)) (by simp only [sC2, sFn]; omega), word_writeW_self, hW']
    · rw [m₁, word_writeW_self]
  refine WP.seq (wp_upto (a := 0) (N := 64) (by decide) (BitInv u₁ B w N g (r / 2 ^ (64 * i)) (r / 2 ^ (64 * i) % 2 ^ 64))
    (fun j _ hj v hv => bitBody_ok M hc₁ (by rw [hGu]; exact hGlt) (by rw [hGu]; exact hG) rfl hj hv)
    (fun v hv => ?_) hB0)
  have hc₂ := hc₁.congr hv.frm (by decide) bit_hs hv.keep (by decide)
  have hc1₂ : word v.mem B (8 * sC1) = BitVec.ofNat 64 (i + 1) := by
    rw [hv.frm.rg_word (by decide) (by decide), hf₁.rg_word (by decide) (by decide)]; exact hc1
  refine WP.mono (ctrDec_ok hc₂.ws (i := sC1) (by decide) (by decide) hc1₂ (by omega) (by omega))
    fun u' ⟨hz, m₃, k₃⟩ => ⟨by rw [hz]; congr 1; exact decide_eq_decide.mpr (by omega), ?_⟩
  have hf₃ : Frm B (rg w [] [sC1]) v.mem u'.mem := by
    rw [m₃]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC1, sCnt, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (((hI.frm.rg_trans hf₁).rg_trans hv.frm).rg_trans hf₃).rg_mono (by decide) (by decide)
  · exact (((hI.keep.trans k₁).trans hv.keep).trans k₃).mono (by decide)
  · rw [hf₃.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hv.ylt
  · rw [hf₃.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), show Bw - (k + 1) = i by omega]
    have := hv.y
    rwa [Nat.sub_self, Nat.pow_zero, Nat.div_one] at this
  · rw [m₃, word_writeW_self, show Bw - (k + 1) = i by omega, Nat.add_sub_cancel]

/-! ## The exponentiation -/

/-- `expLoop`: `Y ≡ g^r R`, from `Y = R mod n` and `G ≡ g R`. -/
theorem expLoop_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t g : Nat}
    (hc : Cst s B Z w minv N el r t) (hGlt : wv s.mem B (slot w aG) w < N)
    (hG : wv s.mem B (slot w aG) w % N = g * 2 ^ (64 * w) % N) (hY : wv s.mem B (slot w aY) w = 2 ^ (64 * w) % N) :
    WP isa (expLoop M.mm) s fun u => Frm B (rg w [aAcc, aTmp, aXm, aY] [sC1, sC2, sC3]) s.mem u.mem ∧
      Keep mmRegs s u ∧ wv u.mem B (slot w aY) w < N ∧
      wv u.mem B (slot w aY) w % N = g ^ r * 2 ^ (64 * w) % N := by
  have hZ16 := hc.hZ16
  have he2 := hc.e2
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have h256 := hc.ws.h256
  have hN : 0 < N := by have := hc.n1; omega
  unfold expLoop expInit
  refine WP.seq (WP.mono (Q := fun (u : State) => u.mem = s.mem.writeW (off B (8 * sC1))
      (BitVec.ofNat 64 (w + (el + 7) / 8)) ∧ Keep mmRegs s u)
    (WP.block_append_iff.mpr (WP.mono (bw_ok hc.ws hc.hel (by omega)) fun s₁ ⟨hax, m₁, k₁⟩ => ?_))
    fun s₁ ⟨m₁, k₁⟩ => ?_)
  · have hs₁ := hc.ws.scr.congr k₁.2.2
    have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hc.ws.rdi
    refine WP.mono (WP.keep [] (Q := fun u => u.mem = s.mem.writeW (off B (8 * sC1))
        (BitVec.ofNat 64 (w + (el + 7) / 8))) (by
      xrun [State.ea, hdr, hdi₁, hdrOff, hs₁.st (d := 8 * sC1) (by simp only [sC1, sCnt, sFn]; omega), hax, m₁])
      rfl) fun u ⟨mu, k₂⟩ => ⟨mu, (k₁.trans k₂).mono (by decide)⟩
  have hf₁ : Frm B (rg w [] [sC1]) s.mem s₁.mem := by
    rw [m₁]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC1, sCnt, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hr : r < 2 ^ (64 * (w + (el + 7) / 8)) := hc.hm ▸ wv_lt _ _ _ _
  have h0 : WordInv s B w N g r (w + (el + 7) / 8) 0 s₁ := by
    refine ⟨hf₁.rg_mono (by decide) (by decide), k₁, ?_, ?_, ?_⟩
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hY]; exact Nat.mod_lt _ hN
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hY, Nat.sub_zero,
        Nat.div_eq_of_lt hr, Nat.pow_zero, Nat.one_mul, Nat.mod_mod]
    · rw [m₁, word_writeW_self, Nat.sub_zero]
  refine wp_upto (a := 0) (N := w + (el + 7) / 8) (by omega) (WordInv s B w N g r (w + (el + 7) / 8))
    (fun k _ hk u hu => wordStep_ok M hc hGlt hG hk hu) (fun u hu => ?_) h0
  refine ⟨hu.frm, hu.keep, hu.ylt, ?_⟩
  have := hu.y
  rwa [Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at this

end VG.Proof.Rsa.X86_64
