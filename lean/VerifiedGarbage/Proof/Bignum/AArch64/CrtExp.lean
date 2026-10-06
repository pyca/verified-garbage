import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild

/-!
# RSA with the CRT on AArch64: the exponentiation in a prime's workspace

In a prime's workspace (`X`, `w_X` words, `R = 2^(64 w_X)`), with
`Y ≡ R` and `[aXc] ≡ x R`, and the table of `CrtBuild.lean`: a window `v`
is four squarings, `[aT] := T_v` (`tabSel_ok`) and `Y := Y T_v R⁻¹`
(`crtWin_ok`); `expLoop` does two windows for every byte of the exponent,
read from the modulus' header (`crtExpLoop_ok`): `Y ≡ x^d R`.

The values hold if `Y ≡ R` and `[aXc] ≡ x R`, which a proposition `Q` (in
the phases, that `X` divides `n`) gives; the bounds hold whatever.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop)

/-! ## A window -/

/-- `Y := Y² R⁻¹`: `x^E R` becomes `x^(2E) R`. -/
theorem crtSq_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E : Nat} (hc : CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hY : wv t.mem P (slot wx aY) wx < X)
    (hYv : Q → wv t.mem P (slot wx aY) wx % X = x ^ E * 2 ^ (64 * wx) % X) :
    WP isa (M.mm aY aY aY) t fun t' => CExpCtx t' P wx minv X Xc ∧ wv t'.mem P (slot wx aY) wx < X ∧
      (Q → wv t'.mem P (slot wx aY) wx % X = x ^ (2 * E) * 2 ^ (64 * wx) % X) ∧
      (∀ k < 32, word t'.mem P (8 * k) = word t.mem P (8 * k)) ∧
      Frm P (crtWinRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  refine WP.mono (M.mm_ok (o := aY) (a := aY) (b := aY) hc.good (Nat.le_refl _) hw (by omega_arith)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hc.n]; exact hY)) fun t₁ ⟨_, hlt₁, hm₁, ha₁, k₁⟩ => ?_
  rw [hc.n] at hlt₁ hm₁
  have f₁ : Frm P (crtWinRanges wx) t.mem t₁.mem := Frm.of_arrays ha₁ (by simp [crtWinRanges])
  exact ⟨hc.of_win f₁ k₁.wr (k₁.gpr .x0 (by decide)), hlt₁, fun hq => VG.Proof.Bignum.mont_sq hR (hYv hq) hm₁,
    fun k hk => ha₁.hslot hk, f₁, k₁⟩

/-- `Y := Y T R⁻¹`: `x^E R` and `T ≡ x^v R` give `x^(E+v) R`. -/
theorem crtMulT_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E v : Nat} (hc : CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hT : wv t.mem P (slot wx Crt.aT) wx < X)
    (hYv : Q → wv t.mem P (slot wx aY) wx % X = x ^ E * 2 ^ (64 * wx) % X)
    (hTv : Q → wv t.mem P (slot wx Crt.aT) wx % X = x ^ v * 2 ^ (64 * wx) % X) :
    WP isa (M.mm aY aY Crt.aT) t fun t' => CExpCtx t' P wx minv X Xc ∧ wv t'.mem P (slot wx aY) wx < X ∧
      (Q → wv t'.mem P (slot wx aY) wx % X = x ^ (E + v) * 2 ^ (64 * wx) % X) ∧
      (∀ k < 32, word t'.mem P (8 * k) = word t.mem P (8 * k)) ∧
      Frm P (crtWinRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  refine WP.mono (M.mm_ok (o := aY) (a := aY) (b := Crt.aT) hc.good (Nat.le_refl _) hw (by omega_arith)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hc.n]; exact hT)) fun t₁ ⟨_, hlt₁, hm₁, ha₁, k₁⟩ => ?_
  rw [hc.n] at hlt₁ hm₁
  have f₁ : Frm P (crtWinRanges wx) t.mem t₁.mem := Frm.of_arrays ha₁ (by simp [crtWinRanges])
  exact ⟨hc.of_win f₁ k₁.wr (k₁.gpr .x0 (by decide)), hlt₁, fun hq => mont_mulT hR (hYv hq) (hTv hq) hm₁,
    fun k hk => ha₁.hslot hk, f₁, k₁⟩

/-- The window's value: `(V >> 4) & 15`. -/
theorem nibMask (V : Nat) (hV : V < 2 ^ 64) :
    (BitVec.ofNat 64 V >>> 4 &&& BitVec.setWidth 64 (15#16)) = BitVec.ofNat 64 (V / 16 % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hV,
    Nat.shiftRight_eq_div_pow, show (BitVec.setWidth 64 (15#16)).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  omega_arith

/-- The block after the squarings: the window into `sNib`, and `sV` up 4 bits. -/
def winMid : List Instr :=
  [ldh .x3 Crt.sV, .lsl .x .x4 .x3 4, sth .x4 Crt.sV, .lsr .x .x3 .x3 4, movi .x4 15, .logic .and .x .x3 .x3 .x4,
    sth .x3 Crt.sNib]

theorem winMid_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc V : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hV : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 60) :
    WP isa (.block winMid) t fun t' =>
      t'.mem = (t.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (16 * V))).writeW (off P (8 * Crt.sNib))
        (BitVec.ofNat 64 (V / 16 % 16)) ∧ Keep [.x3, .x4] t t' := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [winMid, hc.good.x0, hdr_enc (show Crt.sV < 32 by decide), hdr_enc (show Crt.sNib < 32 by decide),
    hc.ld (i := Crt.sV) (by decide), hc.st (i := Crt.sV) (by decide), hc.st (i := Crt.sNib) (by decide), hV,
    shl_ofNat (show V * 2 ^ 4 < 2 ^ 64 by omega), nibMask V (by omega)]
  rw [show V * 2 ^ 4 = 16 * V by omega]

theorem expWin_eq (mul : Nat → Nat → Nat → Prog isa) : expWin mul =
    [mul aY aY aY, mul aY aY aY, mul aY aY aY, mul aY aY aY, .block winMid] ++
    (tabSelect ++ [mul aY aY Crt.aT, .block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit]]) := rfl

/-- One window: `Y ≡ x^E R` becomes `x^(16 E + v) R` for the window
`v = ⌊V / 16⌋ mod 16` of the value `V` in `sV`, which moves up 4 bits; the
window count `b` drops, into `x3`. -/
theorem crtWin_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E V b : Nat} (hc : CExpCtx t P wx minv X Xc) (htab : CTab t.mem P wx X Q x) (hw : 2 ≤ wx)
    (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hY : wv t.mem P (slot wx aY) wx < X)
    (hYv : Q → wv t.mem P (slot wx aY) wx % X = x ^ E * 2 ^ (64 * wx) % X)
    (hV : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 56)
    (hb : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b) :
    WP isa (seqs (expWin M.mm)) t fun t' => CExpCtx t' P wx minv X Xc ∧ CTab t'.mem P wx X Q x ∧
      wv t'.mem P (slot wx aY) wx < X ∧
      (Q → wv t'.mem P (slot wx aY) wx % X = x ^ (16 * E + V / 16 % 16) * 2 ^ (64 * wx) % X) ∧
      word t'.mem P (8 * Crt.sV) = BitVec.ofNat 64 (16 * V) ∧
      word t'.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (b - 1) ∧
      t'.gpr .x3 = BitVec.ofNat 64 (b - 1) ∧ Frm P (crtWinRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.scrT.nowrap
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  rw [expWin_eq]
  refine wp_seqs_append (by simp) (by simp [tabSelect_eq]) ?_
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
  refine WP.mono (winMid_ok (V := V) hc₄ (by rw [hh04 _ (by decide)]; exact hV) (by omega_arith))
    fun t₅ ⟨hm₅, k₅⟩ => ?_
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
  -- `T := T_v`.
  refine wp_seqs_append (by simp [tabSelect_eq]) (by simp) ?_
  refine WP.mono (tabSel_ok hc₅ hw hw' hv16 (by rw [hh₅ _ (by decide) (by decide) (by decide)]; exact htab.tab)
    (by rw [hm₅, word_writeW_self])) fun t₆ ⟨hc₆, hT₆, f₆, k₆⟩ => ?_
  have f₆' : Frm P (crtWinRanges wx) t₅.mem t₆.mem := f₆.mono (selRanges_sub wx)
  have hY₆ : wv t₆.mem P (slot wx aY) wx = wv t₅.mem P (slot wx aY) wx :=
    f₆.wv_eq (fun r hr => by
      have := slot_sep (w := wx) (show aY ≠ Crt.aT by decide)
      simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only; omega_arith
      · simp only [Crt.sEnt, sFn]; have := hdr_lt_slot wx aY (show 31 < 32 by decide); omega_arith
      · simp only [Crt.sJ, sFn]; have := hdr_lt_slot wx aY (show 31 < 32 by decide); omega_arith) (by omega_arith)
  have hh₆ : ∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ → word t₆.mem P (8 * k) = word t₅.mem P (8 * k) :=
    fun k hk h1 h2 => f₆.word_eq (fun r hr => by
      have := hdr_lt_slot wx Crt.aT hk
      simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only; omega_arith
      · simp only [Crt.sEnt, sFn] at h1 ⊢; omega_arith
      · simp only [Crt.sJ, sFn] at h2 ⊢; omega_arith) (by omega_arith)
  have htab₆ : CTab t₆.mem P wx X Q x := htab₅.of_win f₆' hn
  simp only [seqs]
  -- `Y := Y T`.
  refine WP.seq (WP.mono (crtMulT_ok M (Q := Q) (x := x) (E := 16 * E) (v := V / 16 % 16) hc₆ hw hw' hR
    (by rw [hT₆]; exact htab₅.lt _ hv16)
    (fun hq => by rw [hY₆, hY₅, hYv₄ hq, show 2 * (2 * (2 * (2 * E))) = 16 * E by omega_arith])
    (fun hq => by rw [hT₆]; exact htab₅.val hq _ hv16)) fun t₇ ⟨hc₇, hY₇, hYv₇, hh₇, f₇, k₇⟩ => ?_)
  -- The count.
  refine WP.mono (crtBitEnd_ok hc₇ (by
    rw [hh₇ _ (by decide), hh₆ _ (by decide) (by decide) (by decide), hh₅ _ (by decide) (by decide) (by decide)]
    exact hb) hb1) fun t' ⟨⟨hm', h3'⟩, k'⟩ => ?_
  have o₈ := writeW_outside t₇.mem P (d := 8 * Crt.sBit) (BitVec.ofNat 64 (b - 1)) (by decide)
  rw [← hm'] at o₈
  have f₈ : Frm P (crtWinRanges wx) t₇.mem t'.mem := Frm.of_outside o₈ (by simp [crtWinRanges])
  have fall : Frm P (crtWinRanges wx) t.mem t'.mem := (((f04.trans f₅).trans f₆').trans f₇).trans f₈
  refine ⟨hc₇.of_win f₈ k'.wr (k'.gpr .x0 (by decide)), htab.of_win fall hn, ?_, ?_, ?_, ?_, h3', fall,
    ((((k04.trans k₅).trans k₆).trans k₇).trans k').mono (by decide)⟩
  · rw [o₈.wv (by have := hdr_lt_slot wx aY (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith)]
    exact hY₇
  · intro hq
    rw [o₈.wv (by have := hdr_lt_slot wx aY (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith)]
    exact hYv₇ hq
  · rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₇ _ (by decide),
      hh₆ _ (by decide) (by decide) (by decide), hm₅, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      word_writeW_self]
  · rw [hm', word_writeW_self]

/-! ## The windows of a byte -/

/-- After `j` windows of the byte `v` from `t₀`, where `Y ≡ x^E R`. -/
structure CWinInv (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc : Nat) (Q : Prop) (x E v : Nat)
    (j : Nat) (t : State) : Prop where
  ctx : CExpCtx t P wx minv X Xc
  tab : CTab t.mem P wx X Q x
  ylt : wv t.mem P (slot wx aY) wx < X
  y : Q → wv t.mem P (slot wx aY) wx % X = x ^ (E * 16 ^ j + v / 16 ^ (2 - j)) * 2 ^ (64 * wx) % X
  v : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 (v * 16 ^ j)
  b : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (2 - j)
  frm : Frm P (crtWinRanges wx) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

/-- Window `j` of the byte `v`. -/
theorem crtWinStep_ok (M : Mont) {t s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E v : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hv : v < 256) {j : Nat}
    (hj : j < 2) (hI : CWinInv t P wx minv X Xc Q x E v j s) :
    WP isa (seqs (expWin M.mm)) s fun s' => CWinInv t P wx minv X Xc Q x E v (j + 1) s' ∧
      ((s'.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ 2) := by
  have hp : 16 ^ j ≤ 16 := by rcases (show j = 0 ∨ j = 1 by omega_arith) with rfl | rfl <;> decide
  refine WP.mono (crtWin_ok M (E := E * 16 ^ j + v / 16 ^ (2 - j)) hI.ctx hI.tab hw hw' hR hI.ylt hI.y hI.v
    (by have := Nat.mul_le_mul_left v hp; omega_arith) hI.b (by omega_arith))
    fun s' ⟨hc', htab', hY', hYv', hV', hb', h3', hfr', k'⟩ => ⟨⟨hc', htab', hY', ?_, ?_, ?_,
      hI.frm.trans hfr', (hI.keep.trans k').mono (by decide)⟩, ?_⟩
  · intro hq; rw [hYv' hq, win_step hv hj]
  · rw [hV', Nat.pow_succ]; congr 1; rw [Nat.mul_comm 16, Nat.mul_assoc]
  · rw [hb']; congr 1
  · rw [h3', cnt_ne (by omega_arith)]; omega_arith

/-- The two windows of the byte `v`: `Y ≡ x^E R` becomes `x^(256 E + v) R`. -/
theorem crtWins_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E v : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hv : v < 256)
    (h0 : CWinInv t P wx minv X Xc Q x E v 0 t) :
    WP isa (.loop (seqs (expWin M.mm)) (.nonzero .x .x3)) t (CWinInv t P wx minv X Xc Q x E v 2) :=
  count_loop (cr := .x3) (n := 2) (by decide) (CWinInv t P wx minv X Xc Q x E v)
    (fun _ hj _ hI => crtWinStep_ok M hw hw' hR hv hj hI) h0

/-! ## The bytes of the exponent -/

/-- After `i` bytes of the exponent (`L` bytes `eb` at `ep`) from `t₀`. -/
structure CByteInv (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc : Nat) (Q : Prop) (x : Nat)
    (ep : Addr) (L : Nat) (eb : List Byte) (i : Nat) (t : State) : Prop where
  ctx : CExpCtx t P wx minv X Xc
  tab : CTab t.mem P wx X Q x
  ylt : wv t.mem P (slot wx aY) wx < X
  y : Q → wv t.mem P (slot wx aY) wx % X = x ^ pre eb i * 2 ^ (64 * wx) % X
  idx : word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 i
  e : word t.mem P (8 * Crt.sExp) = ep
  len : word t.mem P (8 * Crt.sExpLen) = BitVec.ofNat 64 L
  frm : Frm P (crtExpRanges wx) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

/-- A byte, zero-extended twice, as `ldrb` loads it. -/
theorem zext_byte (m : Mem) (a : Addr) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (m.read a 1)) = BitVec.ofNat 64 (m a).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [Mem.read, BitVec.toNat_setWidth, BitVec.toNat_append, BitVec.toNat_ofNat]
  have := (m a).isLt
  simp
  omega

/-- The byte's head: the byte into `sV`, and the window count 2. -/
def byteHead : List Instr :=
  [ldh .x3 Crt.sExp, ldh .x4 Crt.sI, .add .x .x3 .x3 .x4, .ldrb .x3 .x3 0, sth .x3 Crt.sV, movi .x3 2,
    sth .x3 Crt.sBit]

/-- The byte into `sV`, and the window count 2: the start of the windows. -/
theorem crtByteHead_ok {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop} {x : Nat}
    {ep : Addr} {L : Nat} {eb : List Byte} {i : Nat} (hL : eb.length = L) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith))
    (hout : ∀ i < L, slot wx 8 + tabBytes wx ≤ ofs P (ep + BitVec.ofNat 64 i))
    (hI : CByteInv t₀ P wx minv X Xc Q x ep L eb i t) :
    WP isa (.block byteHead) t fun t₁ =>
      t₁.mem = (t.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (eb[i]'(by omega_arith)).toNat)).writeW
        (off P (8 * Crt.sBit)) (BitVec.ofNat 64 2) ∧ Keep [.x3, .x4] t t₁ ∧
      CWinInv t₁ P wx minv X Xc Q x (pre eb i) (eb[i]'(by omega_arith)).toNat 0 t₁ := by
  have hc := hI.ctx
  have hn := hc.scrT.nowrap
  have hrdi : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.rd, hI.keep.wr]; exact hrd i hi
  have hbi : t.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith) := by
    rw [hI.frm _ fun r hr => Or.inr (by have := (crtExpRanges_ok wx r hr).2; have := hout i hi; omega_arith)]
    exact hbytes i hi
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t₁ => t₁.mem = (t.mem.writeW (off P (8 * Crt.sV))
      (BitVec.ofNat 64 (eb[i]'(by omega_arith)).toNat)).writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 2)) (by
    brun [byteHead, hc.good.x0, hdr_enc (show Crt.sExp < 32 by decide), hdr_enc (show Crt.sI < 32 by decide),
      hdr_enc (show Crt.sV < 32 by decide), hdr_enc (show Crt.sBit < 32 by decide), hc.ld (i := Crt.sExp) (by decide),
      hc.ld (i := Crt.sI) (by decide), hI.e, hI.idx, hrdi, zext_byte, hbi, hc.st (i := Crt.sV) (by decide),
      hc.st (i := Crt.sBit) (by decide)]
    rfl) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨hm₁, k₁⟩ => ⟨hm₁, k₁, ?_⟩
  have o1 := writeW_outside t.mem P (d := 8 * Crt.sV) (BitVec.ofNat 64 (eb[i]'(by omega_arith)).toNat) (by decide)
  have o2 := writeW_outside (t.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (eb[i]'(by omega_arith)).toNat)) P
    (d := 8 * Crt.sBit) (BitVec.ofNat 64 2) (by decide)
  rw [← hm₁] at o2
  have f₁ : Frm P (crtWinRanges wx) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [crtWinRanges])).trans (Frm.of_outside o2 (by simp [crtWinRanges]))
  have hc₁ := hc.of_win f₁ k₁.wr (k₁.gpr .x0 (by decide))
  have hv : (eb[i]'(by omega_arith)).toNat < 256 := (eb[i]'(by omega_arith)).isLt
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hYe : wv t₁.mem P (slot wx aY) wx = wv t.mem P (slot wx aY) wx := by
    rw [o2.wv (by have := hdr_lt_slot wx aY (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith),
      o1.wv (by have := hdr_lt_slot wx aY (show Crt.sV < 32 by decide); omega_arith) (by omega_arith)]
  refine ⟨hc₁, hI.tab.of_win f₁ hn, hYe ▸ hI.ylt, fun hq => ?_, ?_, ?_, Frm.refl _ _ _, Keep.refl _ _⟩
  · rw [hYe, hI.y hq, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, Nat.div_eq_of_lt (show _ < 16 ^ 2 from hv),
      Nat.add_zero]
  · rw [o2.word (by decide) (by decide), word_writeW_self, Nat.pow_zero, Nat.mul_one]
  · rw [hm₁, word_writeW_self]

/-- The next byte: `sI` up, and `x3 := L - (i + 1)`. -/
def byteNext : List Instr :=
  [ldh .x3 Crt.sI, .addImm .x .x3 .x3 1, sth .x3 Crt.sI, ldh .x4 Crt.sExpLen, .sub .x .x3 .x4 .x3]

/-- One byte of the exponent: its two windows, then the next byte. -/
theorem crtByte_ok (M : Mont) {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x : Nat} {ep : Addr} {L : Nat} {eb : List Byte} {i : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hL : eb.length = L) (hL' : L < 2 ^ 31) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith))
    (hout : ∀ i < L, slot wx 8 + tabBytes wx ≤ ofs P (ep + BitVec.ofNat 64 i))
    (hI : CByteInv t₀ P wx minv X Xc Q x ep L eb i t) :
    WP isa (seqs [.block byteHead, .loop (seqs (expWin M.mm)) (.nonzero .x .x3), .block byteNext]) t fun t' =>
      CByteInv t₀ P wx minv X Xc Q x ep L eb (i + 1) t' ∧ ((t'.gpr .x3).toNat ≠ 0 ↔ i + 1 ≠ L) := by
  have hn := hI.ctx.scrT.nowrap
  simp only [seqs]
  refine WP.seq (WP.mono (crtByteHead_ok hL hi hrd hbytes hout hI) fun t₁ ⟨hm₁, k₁, hB0⟩ => ?_)
  have hv : (eb[i]'(by omega_arith)).toNat < 256 := (eb[i]'(by omega_arith)).isLt
  refine WP.seq (WP.mono (crtWins_ok M hw hw' hR hv hB0) fun t₂ h₂ => ?_)
  -- The next byte.
  have hc₂ := h₂.ctx
  have hh₂ : ∀ k < 32, k ≠ Crt.sV → k ≠ Crt.sBit → k ≠ Crt.sNib → k ≠ Crt.sEnt → k ≠ Crt.sJ →
      word t₂.mem P (8 * k) = word t.mem P (8 * k) := fun k hk h1 h2 h3 h4 h5 => by
    rw [h₂.frm.word_eq (crtWinRanges_hdr wx hk h1 h2 h3 h4 h5) (by omega_arith), hm₁,
      hdrStore_hdr (i := Crt.sBit) _ _ _ (by decide) hk (Ne.symm h2),
      hdrStore_hdr (i := Crt.sV) _ _ _ (by decide) hk (Ne.symm h1)]
  have hidx₂ := (hh₂ Crt.sI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI.idx
  have hlen₂ := (hh₂ Crt.sExpLen (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    hI.len
  have he₂ := (hh₂ Crt.sExp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI.e
  have hlen₂' : (t₂.mem.writeW (off P (8 * Crt.sI)) (BitVec.ofNat 64 (i + 1))).readW (off P (8 * Crt.sExpLen)) 64 =
      BitVec.ofNat 64 L := by
    rw [← hlen₂]; exact hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t' => t'.mem = t₂.mem.writeW (off P (8 * Crt.sI))
      (BitVec.ofNat 64 (i + 1)) ∧ t'.gpr .x3 = BitVec.ofNat 64 L - BitVec.ofNat 64 (i + 1)) (by
    brun [byteNext, hc₂.good.x0, hdr_enc (show Crt.sI < 32 by decide), hdr_enc (show Crt.sExpLen < 32 by decide),
      hc₂.ld (i := Crt.sI) (by decide), hc₂.st (i := Crt.sI) (by decide), hidx₂, ofNat_add_ofNat,
      hc₂.ld (i := Crt.sExpLen) (by decide), hlen₂']) (by decide) (by decide) (by decide +kernel))
    fun t' ⟨⟨hm', h3'⟩, k'⟩ => ⟨?_, ?_⟩
  · have o' := writeW_outside t₂.mem P (d := 8 * Crt.sI) (BitVec.ofNat 64 (i + 1)) (by decide)
    rw [← hm'] at o'
    have f' : Frm P (crtExpRanges wx) t₂.mem t'.mem := Frm.of_outside o' (by simp [crtExpRanges])
    have hY0 := slot_le (w := wx) (show aY < 8 by decide)
    have hYe : wv t'.mem P (slot wx aY) wx = wv t₂.mem P (slot wx aY) wx :=
      o'.wv (by have := hdr_lt_slot wx aY (show Crt.sI < 32 by decide); omega_arith) (by omega_arith)
    refine ⟨hc₂.of_frm f' k'.wr (k'.gpr .x0 (by decide)), ?_, hYe ▸ h₂.ylt, fun hq => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨by rw [o'.word (by decide) (by decide)]; exact h₂.tab.tab,
        fun j hj => by rw [o'.wv (by have := hdr_lt_slot wx (8 + j) (show Crt.sI < 32 by decide); omega_arith)
          (by have := ent_le wx hj; omega_arith)]; exact h₂.tab.lt j hj,
        fun hq j hj => by rw [o'.wv (by have := hdr_lt_slot wx (8 + j) (show Crt.sI < 32 by decide); omega_arith)
          (by have := ent_le wx hj; omega_arith)]; exact h₂.tab.val hq j hj⟩
    · rw [hYe, h₂.y hq, pre_succ eb (by omega_arith)]
      congr 3
      simp only [Nat.reducePow, Nat.reduceSub, Nat.pow_zero, Nat.div_one]
      omega_arith
    · rw [hm', word_writeW_self]
    · rw [hm', hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)]; exact he₂
    · rw [hm', hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)]; exact hlen₂
    · have f₁ : Frm P (crtExpRanges wx) t.mem t₁.mem := by
        rw [hm₁]
        exact (Frm.of_outside (writeW_outside t.mem P _ (d := 8 * Crt.sV) (by decide))
          (by simp [crtExpRanges, crtWinRanges])).trans
          (Frm.of_outside (writeW_outside _ P _ (d := 8 * Crt.sBit) (by decide))
            (by simp [crtExpRanges, crtWinRanges]))
      exact ((hI.frm.trans f₁).trans (h₂.frm.mono (crtWinRanges_sub wx))).trans f'
    · exact (((hI.keep.trans k₁).trans h₂.keep).trans k').mono (by decide)
  · rw [h3', VG.Offset.ofNat_sub_ofNat (show i + 1 ≤ L by omega_arith), cnt_ne (by omega_arith)]
    omega_arith

/-! ## The exponentiation -/

/-- `expLoop`'s start: the exponent's pointer and length, and byte index 0. -/
def expInit (sp sl : Nat) : Prog isa :=
  .block [ldh .x5 Crt.sLink, ldw .x3 .x5 sp, sth .x3 Crt.sExp, ldw .x3 .x5 sl, sth .x3 Crt.sExpLen, movi .x3 0,
    sth .x3 Crt.sI]

/-- `expLoop`'s start: the exponent's pointer and length from the modulus'
header slots `sp` and `sl`, and byte index 0. -/
theorem crtExpInit_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {L : Nat}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 L) :
    WP isa (expInit sp sl) s fun t =>
      t.mem = ((s.mem.writeW (off (off B o) (8 * Crt.sExp)) ep).writeW (off (off B o) (8 * Crt.sExpLen))
        (BitVec.ofNat 64 L)).writeW (off (off B o) (8 * Crt.sI)) (BitVec.ofNat 64 0) ∧
      Keep [.x3, .x5] s t := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have o1 := writeW_outside s.mem (off B o) (d := 8 * Crt.sExp) ep (by decide)
  have hW : (s.mem.writeW (off B (o + 8 * Crt.sExp)) ep).readW (off B (8 * sl)) 64 = BitVec.ofNat 64 L := by
    rw [store_off]
    exact ((Frm.of_outside (rs := [(8 * Crt.sExp, 8)]) o1 (by simp)).word_below (L := slot wx 8)
      (fun r hr => by rw [List.mem_singleton.mp hr]; unfold Crt.sExp sFn slot hdrBytes; omega_arith) (by omega_arith)
      (by unfold slot hdrBytes at hi; omega_arith) (by have := hdr_lt_slot w 8 hsl; omega_arith)).trans hel
  refine WP.keep _ ?_ rfl rfl rfl
  brun [expInit, ldw, hc.x0, hdr_enc (show Crt.sLink < 32 by decide), hdr_enc hsp, hdr_enc hsl,
    hdr_enc (show Crt.sExp < 32 by decide), hdr_enc (show Crt.sExpLen < 32 by decide),
    hdr_enc (show Crt.sI < 32 by decide), hc.ld' (show Crt.sLink < 32 by decide), hc.link', hc.ldn hsp, hep,
    hc.st' (show Crt.sExp < 32 by decide), hc.ldn hsl, hW, hc.st' (show Crt.sExpLen < 32 by decide),
    hc.st' (show Crt.sI < 32 by decide), off_off]
  rfl

/-- `expLoop`'s bytes. -/
def expBytes (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .loop (seqs [.block byteHead, .loop (seqs (expWin mul)) (.nonzero .x .x3), .block byteNext]) (.nonzero .x .x3)

theorem expLoop_eq (mul : Nat → Nat → Nat → Prog isa) (sp sl : Nat) :
    expLoop mul sp sl = expInit sp sl :: (tabBuild mul ++ [expBytes mul]) := by
  simp [expLoop, expInit, expBytes, byteHead, byteNext]

/-- `expLoop`'s start and table: the bytes' invariant. -/
theorem crtExpHead_ok (M : Mont) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x : Nat}
    {Q : Prop} (hc : SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (off B o) (slot wx aN) wx = X)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < X)
    (hxc : Q → wv s.mem (off B o) (slot wx Crt.aXc) wx % X = x * 2 ^ (64 * wx) % X)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < X)
    (hyc : Q → wv s.mem (off B o) (slot wx aY) wx % X = 2 ^ (64 * wx) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length) :
    WP isa (seqs (expInit sp sl :: tabBuild M.mm)) s
      (CByteInv s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) Q x ep eb.length eb 0) := by
  have hPn := hc.scrT.nowrap
  have hBn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  have hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc₀ : CExpCtx s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) :=
    ⟨hc.good, hc.scrT, hn, hinv, rfl⟩
  rw [← List.singleton_append]
  refine wp_seqs_append (by simp) (by simp [tabBuild_eq, tabPre]) ?_
  simp only [seqs]
  refine WP.mono (crtExpInit_ok hc hsp hsl hep hel) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have o1 := writeW_outside s.mem (off B o) (d := 8 * Crt.sExp) ep (by decide)
  have o2 := writeW_outside (s.mem.writeW (off (off B o) (8 * Crt.sExp)) ep) (off B o) (d := 8 * Crt.sExpLen)
    (BitVec.ofNat 64 eb.length) (by decide)
  have o3 := writeW_outside ((s.mem.writeW (off (off B o) (8 * Crt.sExp)) ep).writeW
    (off (off B o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 eb.length)) (off B o) (d := 8 * Crt.sI)
    (BitVec.ofNat 64 0) (by decide)
  rw [← hm₁] at o3
  have f₁ : Frm (off B o) (crtExpRanges wx) s.mem t₁.mem :=
    ((Frm.of_outside o1 (by simp [crtExpRanges])).trans (Frm.of_outside o2 (by simp [crtExpRanges]))).trans
      (Frm.of_outside o3 (by simp [crtExpRanges]))
  have hc₁ := hc₀.of_frm f₁ k₁.wr (k₁.gpr .x0 (by decide))
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hY1 := hdr_lt_slot wx aY (show 31 < 32 by decide)
  have hYe₁ : wv t₁.mem (off B o) (slot wx aY) wx = wv s.mem (off B o) (slot wx aY) wx := by
    rw [o3.wv (by unfold Crt.sI sFn at *; omega_arith) (by omega_arith),
      o2.wv (by unfold Crt.sExpLen sFn at *; omega_arith) (by omega_arith),
      o1.wv (by unfold Crt.sExp sFn at *; omega_arith) (by omega_arith)]
  -- The table.
  refine WP.mono (tabBuild_ok M (Q := Q) (x := x) hc₁ hw2 (by omega_arith) hR hxl hxc (by rw [hYe₁]; exact hyl)
    (fun hq => by rw [hYe₁]; exact hyc hq)) fun t₂ ⟨hc₂, htab₂, hYe₂, hh₂, f₂, k₂⟩ => ?_
  refine ⟨hc₂, htab₂, by rw [hYe₂, hYe₁]; exact hyl, fun hq => ?_, ?_, ?_, ?_, f₁.trans f₂,
    (k₁.trans k₂).mono (by decide)⟩
  · rw [hYe₂, hYe₁, hyc hq, pre_zero, Nat.pow_zero, Nat.one_mul]
  · rw [hh₂ _ (by decide) (by decide) (by decide) (by decide), hm₁, word_writeW_self]
  · rw [hh₂ _ (by decide) (by decide) (by decide) (by decide), hm₁,
      hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr (i := Crt.sExpLen) _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hh₂ _ (by decide) (by decide) (by decide) (by decide), hm₁,
      hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide), word_writeW_self]

/-- The exponentiation in a prime's workspace: `Y < X` and `[aXc] < X`
stay so, and if `Q` gives `Y ≡ R` and `[aXc] ≡ x R` modulo `X`, then
`Y ≡ x^d R`, for the exponent `d` whose `L` bytes `eb` (most significant
first) are at `ep`, outside the working space, the pointer and length in
the modulus' header slots `sp` and `sl`. -/
theorem crtExpLoop_ok (M : Mont) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x : Nat}
    {Q : Prop} (hc : SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (off B o) (slot wx aN) wx = X)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < X)
    (hxc : Q → wv s.mem (off B o) (slot wx Crt.aXc) wx % X = x * 2 ^ (64 * wx) % X)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < X)
    (hyc : Q → wv s.mem (off B o) (slot wx aY) wx % X = 2 ^ (64 * wx) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (seqs (expLoop M.mm sp sl)) s fun t => SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx < X ∧
      (Q → wv t.mem (off B o) (slot wx aY) wx % X = x ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X) ∧
      Frm (off B o) (crtExpRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hi := hc.hi
  have hlo := hc.lo
  have hBn := hc.scr.nowrap
  have hPn := hc.scrT.nowrap
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  have hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hodd _
  have hout : ∀ i < eb.length, slot wx 8 + tabBytes wx ≤ ofs (off B o) (ep + BitVec.ofNat 64 i) := fun i hi' => by
    have := he.out i hi'
    rcases ofs_rebase B (ep + BitVec.ofNat 64 i) (o := o) (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩
    · omega_arith
    · omega_arith
  rw [expLoop_eq, ← List.cons_append]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (crtExpHead_ok M hc hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc
    hsp hsl hep hel) fun t₂ h₂ => ?_)
  simp only [seqs, expBytes]
  refine WP.mono (count_loop (cr := .x3) (n := eb.length) (by omega_arith)
    (CByteInv s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) Q x ep eb.length eb)
    (fun i hi' t hI => crtByte_ok M hw2 (by omega_arith) hR rfl (by omega_arith) hi' he.rd he.val hout hI) h₂)
    fun t hI => ?_
  exact ⟨hc.of_frmT hI.frm (crtExpRanges_ok wx) hI.keep.wr (hI.keep.gpr .x0 (by decide)), hI.ylt,
    fun hq => by rw [hI.y hq, pre_len], hI.frm, hI.keep⟩

end VG.Proof.Bignum.AArch64
