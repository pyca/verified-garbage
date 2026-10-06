import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Impl.Rsa.AArch64

/-!
# RSA on AArch64: `R² mod m`

`r2Steps`: `2^(b - 1)` for the bit length `b` of `m` into array `aR2`,
doubled `64 - (b - 1) mod 64 + w` times to `2^w R mod m`, then squared six
times (`r2_ok`): `R² mod m`, for any Montgomery multiplication `M`.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

variable (M : Mont)

theorem sq_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N E : Nat} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hR : Nat.Coprime (2 ^ (64 * w)) N)
    (hn : wv t.mem B (slot w aN) w = N) (hinv : ((word t.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hlt : wv t.mem B (slot w aR2) w < N) (hc : wv t.mem B (slot w aR2) w % N = 2 ^ E * 2 ^ (64 * w) % N) :
    WP isa (M.mm aR2 aR2 aR2) t fun t' => Good t' B Z w minv ∧ wv t'.mem B (slot w aN) w = N ∧
      ((word t'.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧
      wv t'.mem B (slot w aR2) w < N ∧ wv t'.mem B (slot w aR2) w % N = 2 ^ (2 * E) * 2 ^ (64 * w) % N ∧
      Arrays B w [aAcc, aTmp, aR2] t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; omega
  refine WP.mono (M.mm_ok hg hZ hw hw' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hinv (by rw [hn]; exact hlt)) fun t' ⟨hg', hlt', hm, ha, k⟩ => ?_
  rw [hn] at hlt' hm
  refine ⟨hg', by rw [ha.wv_of_not_mem (by decide) (by decide) hn']; exact hn,
    by rw [ha.word0_of_not_mem (by decide) (by decide) hn' (by omega)]; exact hinv, hlt', ?_, ha, k⟩
  exact VG.Proof.Bignum.mont_sq hR hc hm

/-- `n + 1` squarings: `2^E R` becomes `2^(2^(n + 1) E) R`. -/
theorem sqs_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N E : Nat} (n : Nat)
    (hg : Good t B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N)
    (hn : wv t.mem B (slot w aN) w = N) (hinv : ((word t.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hlt : wv t.mem B (slot w aR2) w < N) (hc : wv t.mem B (slot w aR2) w % N = 2 ^ E * 2 ^ (64 * w) % N) :
    WP isa (seqs (List.replicate (n + 1) (M.mm aR2 aR2 aR2))) t fun t' => Good t' B Z w minv ∧
      wv t'.mem B (slot w aR2) w < N ∧
      wv t'.mem B (slot w aR2) w % N = 2 ^ (2 ^ (n + 1) * E) * 2 ^ (64 * w) % N ∧
      Arrays B w [aAcc, aTmp, aR2] t.mem t'.mem ∧ Keep mmRegs t t' := by
  induction n generalizing t E with
  | zero =>
    exact WP.mono (sq_ok M hg hZ hw hw' hR hn hinv hlt hc) fun t' ⟨h1, _, _, h4, h5, h6, h7⟩ =>
      ⟨h1, h4, by rw [h5], h6, h7⟩
  | succ n ih =>
    show WP isa (.seq (M.mm aR2 aR2 aR2) (seqs (List.replicate (n + 1) (M.mm aR2 aR2 aR2)))) t _
    refine WP.seq (WP.mono (sq_ok M hg hZ hw hw' hR hn hinv hlt hc) fun t₁ ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ?_)
    refine WP.mono (ih h1 h2 h3 h4 h5) fun t' ⟨g1, g2, g3, g4, g5⟩ => ⟨g1, g2, ?_, h6.trans g4 |>.mono (by simp),
      (h7.trans g5).mono (by decide)⟩
    rw [g3, show 2 ^ (n + 1 + 1) = 2 ^ (n + 1) * 2 from rfl, Nat.mul_assoc]

theorem r2Steps_eq : r2Steps M.mm = ([
    .block [ldh .x12 sW, ldh .x8 (sArr aN), .subImm .x .x4 .x12 1, .lsl .x .x4 .x4 3, .add .x .x4 .x8 .x4,
      ld .x3 .x4],
    topBit,
    .block [sth .x13 sCnt, .subImm .x .x13 .x12 1],
    setWord aR2,
    .block [ldh .x13 sCnt, ldh .x12 sW, .add .x .x13 .x13 .x12],
    doubles aN aAcc aTmp aR2 sCnt] : List (Prog isa)) ++ List.replicate (5 + 1) (M.mm aR2 aR2 aR2) := rfl

/-- `R² mod m`, for the odd `m` of `w ≥ 2` words, its top word not zero. -/
theorem r2_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw30 : w < 2 ^ 30) (hn : wv s.mem B (slot w aN) w = N)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) (hodd : N % 2 = 1)
    (hlo : 2 ^ (64 * (w - 1)) ≤ N) :
    WP isa (seqs (r2Steps M.mm)) s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w aR2) w < N ∧ wv t.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw' : w < 2 ^ 31 := by omega
  have hs := hg.scr
  have hnw := hs.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hN0 : 0 < N := by omega
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; have := slot_le (w := w) (show 7 < 8 by decide); omega)
  -- The top word `T` of `N`.
  have hsl := slot_le (w := w) (show aN < 8 by decide)
  have hsplit : N = N % 2 ^ (64 * (w - 1)) +
      2 ^ (64 * (w - 1)) * (word s.mem B (slot w aN + 8 * (w - 1))).toNat := by
    have e : wv s.mem B (slot w aN) (w - 1 + 1) = N := by rw [Nat.sub_add_cancel (by omega : 1 ≤ w)]; exact hn
    rw [wv] at e
    have hlt := wv_lt s.mem B (slot w aN) (w - 1)
    rw [← e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  generalize hT : (word s.mem B (slot w aN + 8 * (w - 1))).toNat = T at hsplit
  have hT0 : 0 < T := by
    rcases Nat.eq_zero_or_pos T with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero] at hsplit
      have := Nat.mod_lt N (Nat.two_pow_pos (64 * (w - 1))); omega
    · exact h
  have hT1 : T < 2 ^ 64 := hT ▸ BitVec.isLt _
  have hL : T.log2 < 64 := (Nat.log2_lt (by omega)).mpr hT1
  have hle := Nat.log2_self_le (n := T) (by omega)
  have hv0 := start_lt hw hodd hsplit hle
  have hw8 : (BitVec.ofNat 64 w - BitVec.ofNat 64 1) <<< 3 = BitVec.ofNat 64 (8 * (w - 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  rw [r2Steps_eq]
  -- The top word.
  refine WP.seq (WP.mono (WP.keep [.x3, .x4, .x8, .x12] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 T ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.mem = s.mem) (by
    brun [hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aN < 32 by decide), hl sW (by decide),
      hl (sArr aN) (by decide), hg.hdr.hw, hg.hdr.harr aN (by decide), hw8, off_add,
      hs.ld (show slot w aN + 8 * (w - 1) + 8 ≤ Z by omega)]
    rw [← hT, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨hax, h12₁, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (topBit_ok hax hT0 hT1) fun t₂ ⟨⟨hdx₂, hcx₂, hm₂⟩, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.wr
  have h0₂ : t₂.gpr .x0 = B := (k12.gpr .x0 (by decide)).trans hg.x0
  have h12₂ : t₂.gpr .x12 = BitVec.ofNat 64 w := (k₂.gpr .x12 (by decide)).trans h12₁
  have hm₂' : t₂.mem = s.mem := hm₂.trans hm₁
  have hcntZ : 8 * sCnt + 8 ≤ Z := by
    have := hdr_lt_slot w 0 (show sCnt < 32 by decide); have := slot_le (w := w) (show 0 < 8 by decide); omega
  refine WP.seq (WP.mono (WP.keep [.x13] (Q := fun t => t.gpr .x13 = BitVec.ofNat 64 (w - 1) ∧
      t.mem = s.mem.writeW (off B (8 * sCnt)) (BitVec.ofNat 64 (64 - T.log2))) (by
    brun [h0₂, hdr_enc (show sCnt < 32 by decide), hs₂.st hcntZ, hcx₂, h12₂, hm₂',
      ofNat_sub_one' (show 1 ≤ w by omega) (by omega)]) (by decide) (by decide) (by decide +kernel))
    fun t₃ ⟨⟨hcx₃, hm₃⟩, k₃⟩ => ?_)
  have hs₃ := hs₂.congr k₃.wr
  have hH₃ : Hdr t₃.mem B w minv := by rw [hm₃]; exact Hdr.store hg.hdr (by decide) (by decide) _
  have hdx₃ : t₃.gpr .x9 = BitVec.ofNat 64 (2 ^ T.log2) := (k₃.gpr .x9 (by decide)).trans hdx₂
  refine WP.seq (WP.mono (setWord_ok hs₃ ((k₃.gpr .x0 (by decide)).trans h0₂) hH₃ hZ
    ((k₃.gpr .x12 (by decide)).trans h12₂) hw' (o := aR2) (by decide)
    (i := w - 1) (by omega) hcx₃) fun t₄ ⟨hv₄, ho₄, k₄⟩ => ?_)
  rw [hdx₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hL)] at hv₄
  have hs₄ := hs₃.congr k₄.wr
  have ha₄ : Arrays B w [aR2] t₃.mem t₄.mem :=
    Arrays.of_outside (List.mem_singleton_self _) ho₄ (Nat.le_refl _) (Nat.le_refl _)
  have hH₄ : Hdr t₄.mem B w minv := ha₄.hdr hH₃
  have h0₄ : t₄.gpr .x0 = B := (k₄.gpr .x0 (by decide)).trans ((k₃.gpr .x0 (by decide)).trans h0₂)
  have hcnt₄ : word t₄.mem B (8 * sCnt) = BitVec.ofNat 64 (64 - T.log2) := by
    rw [ha₄.hslot (by decide), hm₃, word_writeW_self]
  refine WP.seq (WP.mono (WP.keep [.x12, .x13] (Q := fun t => t.gpr .x13 = BitVec.ofNat 64 (64 - T.log2 + w) ∧
      t.mem = t₄.mem) (by
    have h0 := hdr_lt_slot w 0 (show 31 < 32 by decide)
    have h0' := slot_le (w := w) (show 0 < 8 by decide)
    brun [h0₄, hdr_enc (show sCnt < 32 by decide), hdr_enc (show sW < 32 by decide),
      hs₄.ld (d := 8 * sCnt) (by unfold sCnt sFn; omega), hs₄.ld (d := 8 * sW) (by unfold sW; omega),
      hcnt₄, hH₄.hw, ← BitVec.ofNat_add]) (by decide) (by decide) (by decide +kernel))
    fun t₅ ⟨⟨hcx₅, hm₅⟩, k₅⟩ => ?_)
  have hs₅ := hs₄.congr k₅.wr
  have hN₄ : wv t₄.mem B (slot w aN) w = N := by
    rw [ha₄.wv_of_not_mem (by decide) (by decide) hn', hm₃, hdrStore_wv _ _ _ (by decide) (by decide) hn']
    exact hn
  have hw0₄ : word t₄.mem B (slot w aN) = word s.mem B (slot w aN) := by
    rw [ha₄.word0_of_not_mem (by decide) (by decide) hn' (by omega), hm₃,
      hdrStore_word _ _ _ (by decide) (by decide) hn']
  refine WP.seq (WP.mono (doubles_ok hs₅ ((k₅.gpr .x0 (by decide)).trans h0₄) (hm₅ ▸ hH₄) hZ hw hw'
    (mo := aN) (acc := aAcc) (tmp := aTmp) (o := aR2) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (sl := sCnt) (by decide) (by decide)
    (c := 64 - T.log2 + w) (by omega) (by omega) hcx₅ (by rw [hm₅, hv₄, hN₄]; exact hv0))
    fun t₆ ⟨hv₆, hf₆, hH₆, k₆⟩ => ?_)
  rw [hm₅, hv₄, hN₄, pow_r2 hL (by omega)] at hv₆
  have hf₆' : Frm B (r2Ranges w) t₅.mem t₆.mem := hf₆
  have hg₆ : Good t₆ B Z w minv := ⟨hs₅.congr k₆.wr, (k₆.gpr .x0 (by decide)).trans ((k₅.gpr .x0 (by decide)).trans h0₄),
    hH₆⟩
  show WP isa (seqs (List.replicate (5 + 1) (M.mm aR2 aR2 aR2))) t₆ _
  refine WP.mono (sqs_ok M 5 hg₆ hZ hw hw' hR (E := w)
    (by rw [hf₆'.r2_wv hn' (by decide) (by decide) (by decide) (by decide), hm₅]; exact hN₄)
    (by rw [hf₆'.r2_word hn' (by decide) (by decide) (by decide) (by decide), hm₅, hw0₄]; exact hinv)
    (by rw [hv₆]; exact Nat.mod_lt _ hN0) (by rw [hv₆, Nat.mod_mod]))
    fun t ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, by rw [h3], ?_,
      ((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans h5).mono (by decide)⟩
  have f₃ : Frm B (r2Ranges w) s.mem t₃.mem := by
    rw [hm₃]; exact Frm.of_outside (writeW_outside _ B _ (by omega)) (by simp [r2Ranges])
  exact (((f₃.trans (Frm.of_arrays ha₄ (by simp [r2Ranges]))).trans (by rw [hm₅]; exact Frm.refl _ _ _)).trans
    hf₆').trans (Frm.of_arrays h4 (by simp [r2Ranges]))

end VG.Proof.Bignum.AArch64
