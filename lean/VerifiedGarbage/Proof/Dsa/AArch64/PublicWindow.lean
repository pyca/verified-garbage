module
public import VerifiedGarbage.Impl.Dsa.AArch64.PublicPower
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp

import VerifiedGarbage.Proof.Dsa.AArch64.PublicSelect
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Correctness of public windows and zero-digit skipping -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.PublicPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.PublicPower

/-- The branch on a number in `x3`. -/
theorem eval_zero_x3 {s : State} {a : Nat} (h : s.gpr .x3 = BitVec.ofNat 64 a) (ha : a < 2 ^ 64) :
    isa.eval (.zero .x .x3) s = some (decide (a = 0)) := by
  show some (s.read .x .x3 == 0) = _
  rw [State.read, h, BitVec.setWidth_eq]
  by_cases h0 : a = 0
  · subst h0; rfl
  · simp only [h0, decide_false, Option.some.injEq, beq_eq_false_iff_ne, ne_eq]
    intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at this
    exact h0 this

/-- Reading the public digit for the branch. -/
theorem test_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v : Nat}
    (hc : CExpCtx s P wx minv X Xc) (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (.block [ldh .x3 Crt.sNib]) s fun t =>
      (t.gpr .x3 = BitVec.ofNat 64 v ∧ t.mem = s.mem) ∧ Keep [.x3] s t := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [hc.good.x0, hdr_enc (show Crt.sNib < 32 by decide), hc.ld (i := Crt.sNib) (by decide), hn]

/-- A zero digit leaves the accumulator unchanged; other digits multiply
by their table entry. This identity holds for every odd modulus. -/
theorem applyWindow_ok (M : Mont) {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64}
    {X Xc : Nat} {Q : Prop} {x E v : Nat}
    (hc : CExpCtx s P wx minv X Xc) (htab : CTab s.mem P wx X Q x)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hv : v < 16)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hY : wv s.mem P (slot wx aY) wx < X)
    (hYv : Q → wv s.mem P (slot wx aY) wx % X = x ^ E * 2 ^ (64 * wx) % X)
    (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (applyWindow M.mm) s fun t => CExpCtx t P wx minv X Xc ∧
      wv t.mem P (slot wx aY) wx < X ∧
      (Q → wv t.mem P (slot wx aY) wx % X = x ^ (E + v) * 2 ^ (64 * wx) % X) ∧
      (∀ k < 32, word t.mem P (8 * k) = word s.mem P (8 * k)) ∧
      Frm P (crtWinRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold applyWindow
  refine WP.seq (WP.mono (test_ok hc hn) fun u ⟨⟨h3, hm⟩, hk⟩ => ?_)
  have hf : Frm P (crtWinRanges wx) s.mem u.mem := hm ▸ Frm.refl _ _ _
  have hu := hc.of_win hf hk.wr (hk.gpr .x0 (by decide))
  have hz := eval_zero_x3 h3 (show v < 2 ^ 64 by omega)
  by_cases hzero : v = 0
  · subst v
    refine WP.ite true (by rw [hz]; rfl) (fun _ => WP.block_nil ?_) (by simp)
    exact ⟨hu, hm ▸ hY, by simpa only [hm, Nat.add_zero] using hYv,
      fun _ _ => by rw [hm], hf, hk.mono (by decide)⟩
  · refine WP.ite false (by rw [hz]; simp [hzero]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (select_ok hu hw hw' hv (hm ▸ htab.tab) (hm ▸ hn))
      fun t ⟨ht, htval, hout, hkt⟩ => ?_)
    have hgt := slot_le (w := wx) (show Crt.aT < 8 by decide)
    have htsep := slot_sep (w := wx) (show aY ≠ Crt.aT by decide)
    have hsz := hc.scrT.nowrap
    have hyEq : wv t.mem P (slot wx aY) wx = wv u.mem P (slot wx aY) wx :=
      hout.wv (by omega) (by have := slot_le (w := wx) (show aY < 8 by decide); omega)
    have htframe : Frm P (crtWinRanges wx) u.mem t.mem :=
      Frm.of_outside (hout.mono (o' := slot wx Crt.aT) (n' := 8 * (wx + 2)) (by omega) (by omega))
        (by simp [crtWinRanges])
    refine WP.mono (crtMulT_ok M (Q := Q) (x := x) (E := E) (v := v) ht hw hw' hR
      (by rw [htval, hm]; exact htab.lt _ hv)
      (fun hq => by rw [hyEq, hm]; exact hYv hq)
      (fun hq => by rw [htval, hm]; exact htab.val hq _ hv))
      fun z ⟨hzctx, hzlt, hzval, hzhdr, hzf, hzk⟩ => ?_
    exact ⟨hzctx, hzlt, hzval, fun k hki => by
      rw [hzhdr k hki, hout.word (by have := hdr_lt_slot wx Crt.aT hki; omega)
        (by have := hdr_lt_slot wx 8 hki; omega), hm],
      (hf.trans htframe).trans hzf, ((hk.trans hkt).trans hzk).mono (by decide)⟩

theorem window_eq (mul : Nat → Nat → Nat → Prog isa) : window mul =
    [mul aY aY aY, mul aY aY aY, mul aY aY aY, mul aY aY aY, .block winMid, applyWindow mul,
      .block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit]] := rfl

/-- One public window: `Y ≡ x^E R` becomes `x^(16 E + v) R` for the window
`v = ⌊V / 16⌋ mod 16` of the value `V` in `sV`, which moves up 4 bits; the
window count `b` drops, into `x3`. -/
theorem pubWin_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E V b : Nat} (hc : CExpCtx t P wx minv X Xc) (htab : CTab t.mem P wx X Q x) (hw : 2 ≤ wx)
    (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hY : wv t.mem P (slot wx aY) wx < X)
    (hYv : Q → wv t.mem P (slot wx aY) wx % X = x ^ E * 2 ^ (64 * wx) % X)
    (hV : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 56)
    (hb : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b) :
    WP isa (seqs (window M.mm)) t fun t' => CExpCtx t' P wx minv X Xc ∧ CTab t'.mem P wx X Q x ∧
      wv t'.mem P (slot wx aY) wx < X ∧
      (Q → wv t'.mem P (slot wx aY) wx % X = x ^ (16 * E + V / 16 % 16) * 2 ^ (64 * wx) % X) ∧
      word t'.mem P (8 * Crt.sV) = BitVec.ofNat 64 (16 * V) ∧
      word t'.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (b - 1) ∧
      t'.gpr .x3 = BitVec.ofNat 64 (b - 1) ∧ Frm P (crtWinRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.scrT.nowrap
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  rw [window_eq]
  simp only [seqs]
  -- Four squarings.
  refine WP.seq (WP.mono (crtSq_ok M hc hw hw' hR hY hYv) fun t₁ ⟨hc₁, hY₁, hYv₁, hh₁, f₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (crtSq_ok M hc₁ hw hw' hR hY₁ hYv₁) fun t₂ ⟨hc₂, hY₂, hYv₂, hh₂, f₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (crtSq_ok M hc₂ hw hw' hR hY₂ hYv₂) fun t₃ ⟨hc₃, hY₃, hYv₃, hh₃, f₃, k₃⟩ => ?_)
  refine WP.seq (WP.mono (crtSq_ok M hc₃ hw hw' hR hY₃ hYv₃) fun t₄ ⟨hc₄, hY₄, hYv₄, hh₄, f₄, k₄⟩ => ?_)
  have hh04 : ∀ k < 32, word t₄.mem P (8 * k) = word t.mem P (8 * k) := fun k hk =>
    (hh₄ k hk).trans ((hh₃ k hk).trans ((hh₂ k hk).trans (hh₁ k hk)))
  have f04 : Frm P (crtWinRanges wx) t.mem t₄.mem := ((f₁.trans f₂).trans f₃).trans f₄
  have k04 : Keep mmRegs t t₄ := (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)
  -- The window, and `sV` up.
  refine WP.seq (WP.mono (winMid_ok (V := V) hc₄ (by rw [hh04 _ (by decide)]; exact hV) (by omega_arith))
    fun t₅ ⟨hm₅, k₅⟩ => ?_)
  have o1 := writeW_outside t₄.mem P (d := 8 * Crt.sV) (BitVec.ofNat 64 (16 * V)) (by decide)
  have o2 := writeW_outside (t₄.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (16 * V))) P (d := 8 * Crt.sNib)
    (BitVec.ofNat 64 (V / 16 % 16)) (by decide)
  rw [← hm₅] at o2
  have f₅ : Frm P (crtWinRanges wx) t₄.mem t₅.mem :=
    (Frm.of_outside o1 (by simp [crtWinRanges])).trans (Frm.of_outside o2 (by simp [crtWinRanges]))
  have hc₅ := hc₄.of_win f₅ k₅.wr (k₅.gpr .x0 (by decide))
  have htab₅ : CTab t₅.mem P wx X Q x := htab.of_win (f04.trans f₅) hn
  have hY₅ : wv t₅.mem P (slot wx aY) wx = wv t₄.mem P (slot wx aY) wx := by
    rw [o2.wv (by have := hdr_lt_slot wx aY (show Crt.sNib < 32 by decide); omega_arith) (by omega_arith),
      o1.wv (by have := hdr_lt_slot wx aY (show Crt.sV < 32 by decide); omega_arith) (by omega_arith)]
  have hh₅ : ∀ k < 32, k ≠ Crt.sV → k ≠ Crt.sNib → word t₅.mem P (8 * k) = word t.mem P (8 * k) :=
    fun k hk h1 h2 => by
      rw [hm₅, hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h2), hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h1),
        hh04 k hk]
  have hv16 : V / 16 % 16 < 16 := Nat.mod_lt _ (by decide)
  refine WP.seq (WP.mono (applyWindow_ok M (E := 16 * E) hc₅ htab₅ hw hw' hv16 hR
    (hY₅ ▸ hY₄)
    (fun hq => by rw [hY₅, hYv₄ hq, show 2 * (2 * (2 * (2 * E))) = 16 * E by omega])
    (by rw [hm₅, word_writeW_self])) fun t₇ ⟨hc₇, hY₇, hYv₇, hh₇, f₇, k₇⟩ => ?_)
  -- The count.
  refine WP.mono (crtBitEnd_ok hc₇ (by
    rw [hh₇ _ (by decide), hh₅ _ (by decide) (by decide) (by decide)]
    exact hb) hb1) fun t' ⟨⟨hm', h3'⟩, k'⟩ => ?_
  have o₈ := writeW_outside t₇.mem P (d := 8 * Crt.sBit) (BitVec.ofNat 64 (b - 1)) (by decide)
  rw [← hm'] at o₈
  have f₈ : Frm P (crtWinRanges wx) t₇.mem t'.mem := Frm.of_outside o₈ (by simp [crtWinRanges])
  have fall : Frm P (crtWinRanges wx) t.mem t'.mem := ((f04.trans f₅).trans f₇).trans f₈
  refine ⟨hc₇.of_win f₈ k'.wr (k'.gpr .x0 (by decide)), htab.of_win fall hn, ?_, ?_, ?_, ?_, h3', fall,
    (((k04.trans k₅).trans k₇).trans k').mono (by decide)⟩
  · rw [o₈.wv (by have := hdr_lt_slot wx aY (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith)]
    exact hY₇
  · intro hq
    rw [o₈.wv (by have := hdr_lt_slot wx aY (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith)]
    exact hYv₇ hq
  · rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₇ _ (by decide),
      hm₅, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm', word_writeW_self]

end VG.Proof.Dsa.AArch64.PublicPower
