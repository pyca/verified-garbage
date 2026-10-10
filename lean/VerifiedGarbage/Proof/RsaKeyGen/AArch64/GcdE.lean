import VerifiedGarbage.Proof.RsaKeyGen.AArch64.ModE
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close

/-!
# A candidate on AArch64: `gcd(c − 1, e)`

`loadE` reads `e` into `x3` (`loadE_ok`). `gcdE` copies `c` to `aX`, clears
its low bit (`c` is odd), reduces `c − 1` modulo the odd `e > 1` in `kG`
(`modWords_ok`), runs the binary gcd (`gcdLoop_ok`) and leaves
`gcd(c − 1, e)` in `kG` (`gcdE_ok`). `gcdCheck` leaves `x3 = 0` iff
`gcd(c − 1, e) = 1` (`gcdCheck_ok`).
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX)

/-- `loadE`: `e` (`e_len ≤ 8` octets at `kE`, most significant first) into
`x3`. -/
theorem loadE_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {eP : Addr} {eB : List Byte}
    (hE : word s.mem B (8 * kE) = eP) (hEl : word s.mem B (8 * kElen) = BitVec.ofNat 64 eB.length)
    (hl1 : 1 ≤ eB.length) (hl8 : eB.length ≤ 8) (hsrc : Src s B Z eP eB) :
    WP isa (seqs loadE) s fun t => (t.gpr .x3).toNat = Spec.Rsa.os2ip eB ∧ t.mem = s.mem ∧
      Keep [.x1, .x2, .x3, .x4] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_arith)
  unfold loadE
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = eP ∧
      t.gpr .x2 = BitVec.ofNat 64 eB.length ∧ t.gpr .x3 = 0 ∧ t.mem = s.mem)
    (by brun [h.x0, hdr_enc (show kE < 32 by decide), hdr_enc (show kElen < 32 by decide), hl kE (by decide),
      hl kElen (by decide), hE, hEl]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h1, h2, h3, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .x2) (N := eB.length) (by omega_arith) (by omega_arith)
    (fun i t => (t.gpr .x3).toNat = pre eB i ∧ t.gpr .x1 = eP + BitVec.ofNat 64 i ∧ t.mem = s.mem ∧
      Keep [.x1, .x2, .x3, .x4] s t) ?_
    ⟨by rw [h3]; rfl, by rw [h1]; exact (BitVec.add_zero eP).symm, hm₁, k₁.mono (by decide)⟩ h2)
    fun t ⟨h3', _, hm, k⟩ => ⟨by rw [h3', pre_len], hm, k⟩
  intro i hi t ⟨hb, h1', hm, k⟩ _
  have hpre : pre eB i < 2 ^ 56 := by
    have := pre_lt eB (i := i) (by omega_arith)
    calc pre eB i < 256 ^ i := this
      _ ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega_arith)
      _ = 2 ^ 56 := by decide
  have hrd : InRegions (t.rd ++ t.wr) (eP + BitVec.ofNat 64 i) 1 := by
    rw [k.rd, k.wr]; exact hsrc.rd i hi
  have hbyte : t.mem (eP + BitVec.ofNat 64 i) = eB[i] := by rw [hm]; exact hsrc.val i hi
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x1, .x3, .x4] (Q := fun t₁ =>
      t₁.gpr .x3 = (t.gpr .x3 <<< 8) + ((t.mem.read (eP + BitVec.ofNat 64 i) 1).setWidth 32).setWidth 64 ∧
      t₁.gpr .x1 = eP + BitVec.ofNat 64 i + BitVec.ofNat 64 1 ∧ t₁.mem = t.mem)
    (by brun [h1', hrd]) (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨h3₁, h1₁, m₁⟩, k₁⟩ => ?_)
  refine WP.mono (dec_ok t₁ .x2) fun t' ⟨⟨h2', m', _⟩, k'⟩ => ⟨⟨?_, ?_, by rw [m', m₁, hm], ?_⟩, ?_⟩
  · have e1 : (t.gpr .x3 <<< 8).toNat = (t.gpr .x3).toNat * 256 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega_arith
    have hb' : (((t.mem.read (eP + BitVec.ofNat 64 i) 1).setWidth 32).setWidth 64 : BitVec 64).toNat =
        eB[i].toNat := by
      rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, VG.Proof.MlKem.AArch64.read_one, hbyte]
      have := eB[i].isLt
      omega_arith
    have := eB[i].isLt
    rw [k'.gpr .x3 (by decide), h3₁, BitVec.toNat_add, e1, hb', hb, pre_succ eB hi,
      Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rw [k'.gpr .x1 (by decide), h1₁, BitVec.add_assoc, ← BitVec.ofNat_add]
  · exact ((k.trans k₁).trans k').mono (by decide)
  · rw [h2', k₁.gpr .x2 (by decide)]

/-- A number with its low word replaced: the difference of the words. -/
theorem wv_low_word {m m' : Mem} {B : Addr} {d w : Nat} (hw : 1 ≤ w)
    (hrest : ∀ i, 1 ≤ i → i < w → word m' B (d + 8 * i) = word m B (d + 8 * i)) :
    wv m' B d w + (word m B d).toNat = wv m B d w + (word m' B d).toNat := by
  have e := wv_add m B d 1 (w - 1)
  have e' := wv_add m' B d 1 (w - 1)
  rw [show 1 + (w - 1) = w by omega_arith] at e e'
  have hr : wv m' B (d + 8 * 1) (w - 1) = wv m B (d + 8 * 1) (w - 1) := wv_congr fun i hi => by
    rw [show d + 8 * 1 + 8 * i = d + 8 * (i + 1) by omega_arith]; exact hrest (i + 1) (by omega_arith) (by omega_arith)
  rw [e, e', hr]
  simp [wv]
  omega_arith

theorem xor_one_odd {x : BitVec 64} (h : x.toNat % 2 = 1) : (x ^^^ 1).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_xor, show (1 : BitVec 64).toNat = 1 from rfl]
  generalize x.toNat = n at h
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  rcases i with _ | i
  · simp only [Nat.testBit_zero]
    rw [show (n - 1) % 2 = 0 by omega_arith]; simp [h]
  · rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ, show n / 2 = (n - 1) / 2 by omega_arith]
    simp

/-- The head of `modLoop` after the copy: `c − 1` in `aX` (the low bit of the
odd copy cleared), `x10` past its top word, `x14 := w`, `x13 := e` from
`kG`, `x3 := 0`, `x7 := 0` and `x8` all ones. -/
theorem modPrep_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {E : Nat}
    (hG : word s.mem B (8 * kG) = BitVec.ofNat 64 E) (hodd : (word s.mem B (slot w aX)).toNat % 2 = 1) :
    WP isa (.block (ws ++ base aX .x16 ++ [ld .x3 .x16, movi .x4 1, .logic .eor .x .x3 .x3 .x4, st .x3 .x16,
      .lsl .x .x5 .x12 3, .add .x .x10 .x16 .x5, mov .x14 .x12, ldh .x13 kG, movi .x3 0, movi .x7 0,
      .subImm .x .x8 .x7 1])) s fun t =>
      (wv t.mem B (slot w aX) w + 1 = wv s.mem B (slot w aX) w ∧ Outside B (slot w aX) 8 s.mem t.mem ∧
        t.gpr .x10 = off B (slot w aX + 8 * w) ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧
        t.gpr .x13 = BitVec.ofNat 64 E ∧ t.gpr .x3 = 0 ∧ t.gpr .x7 = 0 ∧ t.gpr .x8 = mask true) ∧
      Keep [.x11, .x12, .x16, .x3, .x4, .x5, .x10, .x14, .x13, .x7, .x8] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  have hw1 := h.w1
  have hw2 := h.w2
  have sX := h.sl (show aX < 16 by decide)
  have hG8 : 8 * kG + 8 ≤ slot w aX := hdr_lt_slot w aX (by decide)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  refine WP.mono (base_ok aX .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.wr
  have h0₂ : s₂.gpr .x0 = B := (k12.gpr .x0 (by decide)).trans h.x0
  have e12 : s₂.gpr .x12 = BitVec.ofNat 64 w := (k₂.gpr .x12 (by decide)).trans h12
  have hm₂ : s₂.mem = s.mem := m₂.trans m₁
  have hG' : (s.mem.writeW (off B (slot w aX)) (word s.mem B (slot w aX) ^^^ 1)).readW (off B (8 * kG)) 64 =
      BitVec.ofNat 64 E := by
    rw [← hG]; exact (writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith)
  have hx10 : off B (slot w aX) + BitVec.ofNat 64 w <<< 3 = off B (slot w aX + 8 * w) := by
    rw [shl_ofNat (show w * 2 ^ 3 < 2 ^ 64 by omega_arith), off_add, show w * 2 ^ 3 = 8 * w by omega_arith]
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x10, .x14, .x13, .x7, .x8] (Q := fun t =>
      t.mem = s.mem.writeW (off B (slot w aX)) (word s.mem B (slot w aX) ^^^ 1) ∧
      t.gpr .x10 = off B (slot w aX + 8 * w) ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧
      t.gpr .x13 = BitVec.ofNat 64 E ∧ t.gpr .x3 = 0 ∧ t.gpr .x7 = 0 ∧ t.gpr .x8 = mask true) (by
    brun [hm₂, h16, e12, h0₂, one16, hs₂.ld (d := slot w aX) (by omega_arith), hs₂.st (d := slot w aX) (by omega_arith),
      hdr_enc (show kG < 32 by decide), hs₂.ld (d := 8 * kG) (by omega_arith), hG', hx10])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨hm, h10, h14, h13, h3, h7, h8⟩, k₃⟩ => ?_
  refine ⟨⟨?_, by rw [hm]; exact writeW_outside _ _ _ (by omega_arith), h10, h14, h13, h3, h7, h8⟩,
    (k12.trans k₃).mono (by decide)⟩
  have hl := wv_low_word (m := s.mem) (m' := t.mem) (B := B) (d := slot w aX) (w := w) (by omega_arith) (fun i h1 h2 => by
    rw [hm]; exact (writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith))
  rw [hm, word_writeW_self, xor_one_odd hodd] at hl
  rw [← hm] at hl
  omega_arith

/-- What `gcdE` and `gcdCheck` change. -/
def gcdRanges (w : Nat) : List (Nat × Nat) := [(slot w aX, 8 * (w + 2)), (8 * kG, 8)]

theorem gcdRanges_mut (w : Nat) : ∀ r ∈ gcdRanges w, KMut r := by
  simp only [gcdRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact KMut.ofSlot w _ _
  · exact KMut.hdr (by simp [kG, sW])

theorem gcd_mod_left (a E : Nat) : Nat.gcd (a % E) E = Nat.gcd a E := by
  rw [← Nat.gcd_rec E a, Nat.gcd_comm]

/-- `gcdE`: `gcd(c − 1, e)` into `kG`, for the odd `c` in `aN` and the odd
`e > 1` in `kG`. -/
theorem gcdE_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {E : Nat}
    (hc : wv s.mem B (slot w aN) w % 2 = 1) (hG : word s.mem B (8 * kG) = BitVec.ofNat 64 E) (hE1 : 1 < E)
    (hEo : E % 2 = 1) (hE64 : E < 2 ^ 64) :
    WP isa (seqs gcdE) s fun t =>
      word t.mem B (8 * kG) = BitVec.ofNat 64 (Nat.gcd (wv s.mem B (slot w aN) w - 1) E) ∧ Ws t B Z w ∧
      Frm B (gcdRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  have hw1 := h.w1
  have hw2 := h.w2
  have sX := h.sl (show aX < 16 by decide)
  have sN := h.sl (show aN < 16 by decide)
  have hG8 : 8 * kG + 8 ≤ slot w aX := hdr_lt_slot w aX (by decide)
  have eX : slot w aX = slot w aN + 8 * (w + 2) := by simp [slot, aX, aN]
  unfold gcdE modLoop
  simp only [List.cons_append, List.nil_append, seqs]
  generalize hcv : wv s.mem B (slot w aN) w = c at hc ⊢
  refine WP.seq (WP.mono (copyA_ok h (o := aX) (a := aN) (by decide) (by decide) (by decide))
    fun s₁ ⟨hv₁, o₁, _, _, k₁⟩ => ?_)
  have f₁ : Frm B (gcdRanges w) s.mem s₁.mem :=
    Frm.of_outside (o₁.mono (o' := slot w aX) (n' := 8 * (w + 2)) (le_refl _) (by omega_arith)) (by simp [gcdRanges])
  have h₁ : Ws s₁ B Z w := h.congr' f₁ (gcdRanges_mut w) k₁ (by decide)
  have hlow : (word s₁.mem B (slot w aX)).toNat % 2 = 1 := by
    have e := wv_add s₁.mem B (slot w aX) 1 (w - 1)
    rw [show 1 + (w - 1) = w by omega_arith, hv₁, hcv] at e
    have : wv s₁.mem B (slot w aX) 1 = (word s₁.mem B (slot w aX)).toNat := by simp [wv]
    rw [this] at e
    have : 2 ^ (64 * 1) * wv s₁.mem B (slot w aX + 8 * 1) (w - 1) % 2 = 0 := by
      rw [Nat.mul_mod]; simp
    omega_arith
  have hG₁ : word s₁.mem B (8 * kG) = BitVec.ofNat 64 E := by rw [o₁.word (by omega_arith) (by omega_arith), hG]
  refine WP.seq (WP.mono (modPrep_ok h₁ hG₁ hlow) fun s₂ ⟨⟨hv₂, o₂, h10, h14, h13, h3, h7, h8⟩, k₂⟩ => ?_)
  rw [hv₁, hcv] at hv₂
  refine WP.seq (WP.mono (modWords_ok (hs.congr (k₁.trans k₂).wr) h10 h14 h7 h8 (by omega_arith) (by omega_arith) (by omega_arith)
    h3 (by rw [h13, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hE64]; exact hE1)) fun s₃ ⟨hr₃, m₃, k₃⟩ => ?_)
  rw [h13, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hE64, show wv s₂.mem B (slot w aX) w = c - 1 by omega_arith] at hr₃
  refine WP.seq (WP.mono (WP.keep [.x9] (Q := fun t => t.gpr .x9 = BitVec.ofNat 64 128 ∧ t.mem = s₃.mem)
    (by brun) (by decide) (by decide) (by decide +kernel)) fun s₄ ⟨⟨h9₄, m₄⟩, k₄⟩ => ?_)
  have k34 := k₃.trans k₄
  have r13 : s₄.gpr .x13 = BitVec.ofNat 64 E := (k34.gpr .x13 (by decide)).trans h13
  refine WP.seq (WP.mono (gcdLoop_ok ((k34.gpr .x7 (by decide)).trans h7) ((k34.gpr .x8 (by decide)).trans h8) h9₄
    (by rw [r13, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hE64]; exact hEo)) fun s₅ ⟨hg₅, m₅, k₅⟩ => ?_)
  rw [r13, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hE64, k₄.gpr .x3 (by decide), hr₃, gcd_mod_left] at hg₅
  have k15 := (((k₁.trans k₂).trans k₃).trans k₄).trans k₅
  have hm₅ : s₅.mem = s₂.mem := by rw [m₅, m₄, m₃]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₅.mem.writeW (off B (8 * kG)) (s₅.gpr .x13)) (by
    brun [((k₂.trans (k₃.trans (k₄.trans k₅))).gpr .x0 (by decide)).trans h₁.x0, hdr_enc (show kG < 32 by decide),
      (hs.congr k15.wr).st (d := 8 * kG) (by omega_arith)]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨hm, k₆⟩ => ?_
  have hg64 : Nat.gcd (c - 1) E < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.gcd_le_right _ (by omega_arith)) hE64
  have hx13 : s₅.gpr .x13 = BitVec.ofNat 64 (Nat.gcd (c - 1) E) := by
    rw [← hg₅, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have f : Frm B (gcdRanges w) s.mem t.mem := by
    refine (f₁.trans (Frm.of_outside (o₂.mono (o' := slot w aX) (n' := 8 * (w + 2)) (le_refl _) (by omega_arith))
      (by simp [gcdRanges]))).trans ?_
    rw [hm, hm₅]
    exact Frm.of_outside (writeW_outside _ _ _ (by omega_arith)) (by simp [gcdRanges])
  refine ⟨by rw [hm, word_writeW_self, hx13], h.congr' f (gcdRanges_mut w) (k15.trans k₆) (by decide), f,
    (k15.trans k₆).mono (by decide)⟩

theorem gcd_even_ne_one {a e : Nat} (ha : a % 2 = 0) (he : e % 2 = 0) : Nat.gcd a e ≠ 1 := by
  intro h
  have h2a : 2 ∣ Nat.gcd a e := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero ha) (Nat.dvd_of_mod_eq_zero he)
  rw [h] at h2a
  exact absurd (Nat.le_of_dvd (by decide) h2a) (by decide)

theorem ofNat_sub_one_beq {g : Nat} (hg : g < 2 ^ 64) :
    (BitVec.ofNat 64 g - BitVec.ofNat 64 1 == 0) = decide (g = 1) := by
  by_cases h : g = 1
  · subst h; rfl
  · rw [decide_eq_false h]
    have : BitVec.ofNat 64 g - BitVec.ofNat 64 1 ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hg] at this
      simp at this; omega_arith
    exact beq_eq_false_iff_ne.mpr this

theorem ofNat_sub_one_ne {g : Nat} (hg : g < 2 ^ 64) :
    (BitVec.ofNat 64 g - BitVec.setWidth 64 (BitVec.ofNat 12 1) != 0) = !decide (g = 1) := by
  rw [show BitVec.setWidth 64 (BitVec.ofNat 12 1) = BitVec.ofNat 64 1 from rfl]
  by_cases h : g = 1
  · subst h; rfl
  · rw [decide_eq_false h]
    have : BitVec.ofNat 64 g - BitVec.ofNat 64 1 ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hg] at this
      simp at this; omega_arith
    rw [Bool.not_false]; exact bne_iff_ne.mpr this

/-- The end of `gcdCheck`: `x3 = kG − 1`. -/
theorem gcdEnd_ok {t : State} {B : Addr} {Z w : Nat} (h : Ws t B Z w) {g : Nat} (hg : g < 2 ^ 64)
    (hG : word t.mem B (8 * kG) = BitVec.ofNat 64 g) :
    WP isa (.block [ldh .x3 kG, .subImm .x .x3 .x3 1]) t fun t' =>
      ((t'.gpr .x3 != 0) = !decide (g = 1) ∧ t'.mem = t.mem) ∧ Keep [.x3] t t' := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  refine WP.keep [.x3] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h.x0, hdr_enc (show kG < 32 by decide), hs.ld (d := 8 * kG) (by simp only [kG]; omega_arith), hG]
  exact ofNat_sub_one_ne hg

/-- `gcdCheck`: `x3 = 0` iff `gcd(c − 1, e) = 1`, for `c` (in `aN`) odd and
at least 3, and `e` at `kE`. -/
theorem gcdCheck_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    (hc : wv s.mem B (slot w aN) w % 2 = 1) (hc3 : 3 ≤ wv s.mem B (slot w aN) w) {eP : Addr} {eB : List Byte}
    (hE : word s.mem B (8 * kE) = eP) (hEl : word s.mem B (8 * kElen) = BitVec.ofNat 64 eB.length)
    (hl1 : 1 ≤ eB.length) (hl8 : eB.length ≤ 8) (hsrc : Src s B Z eP eB) :
    WP isa (seqs gcdCheck) s fun t =>
      (t.gpr .x3 != 0) = !decide (Nat.gcd (wv s.mem B (slot w aN) w - 1) (Spec.Rsa.os2ip eB) = 1) ∧
      Ws t B Z w ∧ Frm B (gcdRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  have hG8 : 8 * kG + 8 ≤ slot w aN := hdr_lt_slot w aN (by decide)
  have sN := h.sl (show aN < 16 by decide)
  unfold gcdCheck
  refine wp_seqs_append (by simp [loadE]) (by simp) (WP.mono (loadE_ok h hE hEl hl1 hl8 hsrc)
    fun s₁ ⟨h3₁, hm₁, k₁⟩ => ?_)
  have h₁ : Ws s₁ B Z w := h.congr' (rs := []) (fun x _ => by rw [hm₁]) (by simp) k₁ (by decide)
  generalize hEv : Spec.Rsa.os2ip eB = E at h3₁ ⊢
  generalize hcv : wv s.mem B (slot w aN) w = c at hc hc3 ⊢
  have hE64 : E < 2 ^ 64 := by rw [← h3₁]; exact (s₁.gpr .x3).isLt
  have hx3 : s₁.gpr .x3 = BitVec.ofNat 64 E := by rw [← h3₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp only [seqs]
  -- `kG := e`, `x5` its low bit.
  refine WP.seq (WP.mono (WP.keep [.x4, .x5] (Q := fun t => t.mem = s₁.mem.writeW (off B (8 * kG)) (s₁.gpr .x3) ∧
      t.gpr .x5 = BitVec.ofNat 64 (E % 2) ∧ t.gpr .x3 = s₁.gpr .x3) (by
    brun [h₁.x0, hdr_enc (show kG < 32 by decide), h₁.scr.st (d := 8 * kG) (by simp only [kG]; omega_arith), one16]
    rw [hx3]; apply BitVec.eq_of_toNat_eq
    rw [and1_toNat]; simp only [BitVec.toNat_ofNat]; omega_arith)
    (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨⟨hm₂, h5₂, h3₂⟩, k₂⟩ => ?_)
  have o₂ : Outside B (8 * kG) 8 s.mem s₂.mem := by rw [hm₂, hm₁]; exact writeW_outside _ _ _ (by omega_arith)
  have f₂ : Frm B (gcdRanges w) s.mem s₂.mem := Frm.of_outside o₂ (by simp [gcdRanges])
  have h₂ : Ws s₂ B Z w := h.congr' f₂ (gcdRanges_mut w) (k₁.trans k₂) (by decide)
  have hG₂ : word s₂.mem B (8 * kG) = BitVec.ofNat 64 E := by rw [hm₂, word_writeW_self, hx3]
  have hc₂ : wv s₂.mem B (slot w aN) w = c := by rw [← hcv]; exact o₂.wv (Or.inr hG8) (by omega_arith)
  have hcm : (c - 1) % 2 = 0 := by omega_arith
  have k12 := k₁.trans k₂
  -- After the branches: `kG` holds a `g` that is 1 iff the gcd is.
  let P : State → Prop := fun t => ∃ g, g < 2 ^ 64 ∧ (g = 1 ↔ Nat.gcd (c - 1) E = 1) ∧
    word t.mem B (8 * kG) = BitVec.ofNat 64 g ∧ Ws t B Z w ∧ Frm B (gcdRanges w) s.mem t.mem ∧ Keep mmRegs s t
  have hbr : WP isa (.ite (.zero .x .x5) (.block [])
      (.seq (.block [.subImm .x .x5 .x3 1]) (.ite (.zero .x .x5) (.block []) (seqs gcdE)))) s₂ P := by
    refine WP.ite (decide (E % 2 = 0)) (by rw [eval_zero, h5₂, ofNat64_beq_zero (by omega_arith)]) (fun he => ?_)
      (fun he => ?_)
    · -- An even `e`: `kG` keeps it.
      simp only [decide_eq_true_eq] at he
      exact WP.block_nil ⟨E, hE64, ⟨fun h => by omega_arith, fun h => absurd h (gcd_even_ne_one hcm he)⟩, hG₂, h₂, f₂,
        k12.mono (by decide)⟩
    · simp only [decide_eq_false_iff_not] at he
      refine WP.seq (WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = BitVec.ofNat 64 E - BitVec.ofNat 64 1 ∧
          t.mem = s₂.mem) (by brun [h3₂, hx3]) (by decide) (by decide) (by decide +kernel))
        fun s₃ ⟨⟨h5₃, hm₃⟩, k₃⟩ => ?_)
      have h₃ : Ws s₃ B Z w := h₂.congr' (rs := []) (fun x _ => by rw [hm₃]) (by simp) k₃ (by decide)
      have hz : (s₃.gpr .x5 == 0) = decide (E = 1) := by rw [h5₃]; exact ofNat_sub_one_beq hE64
      refine WP.ite (decide (E = 1)) (by rw [eval_zero, hz]) (fun h1 => ?_) (fun h1 => ?_)
      · simp only [decide_eq_true_eq] at h1
        subst h1
        exact WP.block_nil ⟨1, by decide, ⟨fun _ => Nat.gcd_one_right _, fun _ => rfl⟩, by rw [hm₃, hG₂],
          h₃, by rw [hm₃]; exact f₂, (k12.trans k₃).mono (by decide)⟩
      · simp only [decide_eq_false_iff_not] at h1
        refine WP.mono (gcdE_ok h₃ (by rw [hm₃, hc₂]; exact hc) (by rw [hm₃]; exact hG₂) (by omega_arith) (by omega_arith) hE64)
          fun t ⟨hg, ht, ft, kt⟩ => ⟨Nat.gcd (c - 1) E, Nat.lt_of_le_of_lt (Nat.gcd_le_right _ (by omega_arith)) hE64,
            Iff.rfl, by rw [hg, hm₃, hc₂], ht, f₂.trans (by rw [hm₃] at ft; exact ft),
            ((k12.trans k₃).trans kt).mono (by decide)⟩
  refine WP.seq (WP.mono hbr fun t ⟨g, hg, hiff, hG, ht, ft, kt⟩ => ?_)
  refine WP.mono (gcdEnd_ok ht hg hG) fun t' ⟨⟨hx, hm⟩, k⟩ => ⟨?_, ht.congr' (rs := []) (fun x _ => by rw [hm])
    (by simp) k (by decide), by rw [hm]; exact ft, (kt.trans k).mono (by decide)⟩
  rw [hx]
  congr 1
  exact decide_eq_decide.mpr hiff

end VG.Proof.RsaKeyGen.AArch64
