import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.DBase
import VerifiedGarbage.Proof.RsaKeyGen.KeyMath

/-!
# An RSA key from its primes on AArch64: `d` for an odd `e`

`L = e Q + R`, `x = R⁻¹ mod e`, `t = e − x` (in `x1`) and `d = Q t + c` with
`c = (1 + R t) e⁻¹ mod 2⁶⁴` (in `x10`) (`dOdd_k`, `inverse_odd`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- A number below `2⁶⁴` is its low word. -/
theorem word0_of_lt {I : KIn} {m : Mem} {j v : Nat} (hw : 1 ≤ I.W) (h : av I m j = v) (hv : v < 2 ^ 64) :
    word m I.B (slot I.W j) = BitVec.ofNat 64 v :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, ← wv_mod64 _ _ _ hw,
      show wv m I.B (slot I.W j) I.W = av I m j from rfl, h, Nat.mod_eq_of_lt hv])

/-- The words of `c`: `x1 = e − x`, `x10 = ((R (e − x) + 1) e⁻¹) mod 2⁶⁴`. -/
theorem dOddC_ok {I : KIn} {s₀ s : State} (h : KS I s₀ s) {e x R : Nat} (he64 : e < 2 ^ 64) (hxe : x < e)
    (hR : R < 2 ^ 64) (heo : e % 2 = 1) (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e)
    (hX : word s.mem I.B (slot I.W aX₂) = BitVec.ofNat 64 x) (hRw : word s.mem I.B (slot I.W aR) = BitVec.ofNat 64 R) :
    WP isa (.block ([ldh .x3 kEv] ++ minv ++ ws ++ base aX₂ .x16 ++ base aR .x17 ++
      ([ldh .x1 kEv, ld .x3 .x16, .sub .x .x1 .x1 .x3, ld .x3 .x17, .mul .x .x3 .x3 .x1, .addImm .x .x3 .x3 1,
        .mul .x .x10 .x3 .x4] : List Instr))) s fun t =>
      (t.gpr .x1 = BitVec.ofNat 64 (e - x) ∧ ∃ einv : Nat, e * einv % 2 ^ 64 = 1 ∧
        (t.gpr .x10).toNat = ((R * (e - x) % 2 ^ 64 + 1) % 2 ^ 64 * einv) % 2 ^ 64 ∧ t.mem = s.mem) ∧
      Keep [.x1, .x3, .x4, .x5, .x6, .x10, .x11, .x12, .x15, .x16, .x17] s t := by
  have hn := h.ws.scr.nowrap
  have sX := h.ws.sl (j := aX₂) (by decide)
  have sR := h.ws.sl (j := aR) (by decide)
  have hlE := h.ws.scr.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega_using [this])
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 e ∧ t.mem = s.mem) (by
    brun [h.ws.x0, hdr_enc (show kEv < 32 by decide), hlE, hev]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h3₁, m₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (minvX4_ok s₁ (by rw [h3₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64]; exact heo))
    fun s₂ ⟨⟨hinv, _, m₂⟩, k₂⟩ => ?_
  rw [h3₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64] at hinv
  generalize hei : (s₂.gpr .x4).toNat = einv at hinv
  have k12 := k₁.trans k₂
  have hs₂ := h.ws.scr.congr k12.wr
  have hm₂ : s₂.mem = s.mem := by rw [m₂, m₁]
  rw [WP.block_append_iff]
  have h₂ : KS I s₀ s₂ := h.regs hm₂ k12
  refine WP.mono h₂.ws.ws_ok fun s₃ ⟨⟨_, h11, m₃, _⟩, k₃⟩ => ?_
  have hx0₃ : s₃.gpr .x0 = I.B := ((k12.trans k₃).gpr .x0 (by decide)).trans h.ws.x0
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aX₂ .x16 hx0₃ h11) fun s₄ ⟨⟨h16, m₄, _⟩, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aR .x17 ((k₄.gpr .x0 (by decide)).trans hx0₃) ((k₄.gpr .x11 (by decide)).trans h11))
    fun s₅ ⟨⟨h17, m₅, _⟩, k₅⟩ => ?_
  have k25 := (k₃.trans k₄).trans k₅
  have hs₅ := h.ws.scr.congr ((k12.trans k25).wr)
  have hm₅ : s₅.mem = s.mem := by rw [m₅, m₄, m₃, hm₂]
  have h16₅ : s₅.gpr .x16 = off I.B (slot I.W aX₂) := (k₅.gpr .x16 (by decide)).trans h16
  have hx0₅ : s₅.gpr .x0 = I.B := ((k₄.trans k₅).gpr .x0 (by decide)).trans hx0₃
  have h4₅ : (s₅.gpr .x4).toNat = einv := by rw [k25.gpr .x4 (by decide), hei]
  have hX₅ : s₅.mem.readW (off I.B (slot I.W aX₂)) 64 = BitVec.ofNat 64 x := by rw [hm₅]; exact hX
  have hR₅ : s₅.mem.readW (off I.B (slot I.W aR)) 64 = BitVec.ofNat 64 R := by rw [hm₅]; exact hRw
  have hE₅ : s₅.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := by rw [hm₅]; exact hev
  refine WP.mono (WP.keep [.x1, .x3, .x10] (Q := fun t => t.gpr .x1 = BitVec.ofNat 64 (e - x) ∧
      (t.gpr .x10).toNat = ((R * (e - x) % 2 ^ 64 + 1) % 2 ^ 64 * einv) % 2 ^ 64 ∧ t.mem = s₅.mem) (by
    brun [hx0₅, hdr_enc (show kEv < 32 by decide), h16₅, h17,
        hs₅.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega_using [this]),
      hs₅.ld (d := slot I.W aX₂) (by omega_using [sX]), hs₅.ld (d := slot I.W aR) (by omega_using [sR]), hX₅, hR₅, hE₅,
      VG.Offset.ofNat_sub_ofNat (Nat.le_of_lt hxe)]
    rw [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_mul, h4₅, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hR, Nat.mod_eq_of_lt (show e - x < 2 ^ 64 by omega_using [he64])]
    rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h1, h10, mt⟩, kt⟩ => ?_
  exact ⟨⟨h1, einv, hinv, h10, mt.trans hm₅⟩, ((k12.trans k25).trans kt).mono (by decide)⟩

/-- `c` into `[aDd]`'s low word, and the bases for `mulAddRow`. -/
theorem dOddD_ok {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (.block (ws ++ base aDd .x8 ++ ([st .x10 .x8] : List Instr) ++ base aQt .x9 ++
      ([movi .x7 0] : List Instr))) s fun t =>
      (t.mem = s.mem.writeW (off I.B (slot I.W aDd)) (s.gpr .x10) ∧ t.gpr .x8 = off I.B (slot I.W aDd) ∧
        t.gpr .x9 = off I.B (slot I.W aQt) ∧ t.gpr .x12 = BitVec.ofNat 64 I.W ∧ t.gpr .x7 = 0) ∧
      Keep [.x7, .x8, .x9, .x11, .x12] s t := by
  have hn := h.ws.scr.nowrap
  have sD := h.ws.sl (j := aDd) (by decide)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  have hx0₁ : s₁.gpr .x0 = I.B := (k₁.gpr .x0 (by decide)).trans h.ws.x0
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aDd .x8 hx0₁ h11) fun s₂ ⟨⟨h8, m₂, _⟩, k₂⟩ => ?_
  rw [WP.block_append_iff]
  have hs₂ := h.ws.scr.congr (k₁.trans k₂).wr
  have h10₂ : s₂.gpr .x10 = s.gpr .x10 := (k₁.trans k₂).gpr .x10 (by decide)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off I.B (slot I.W aDd)) (s.gpr .x10)) (by
    brun [h8, hs₂.st (d := slot I.W aDd) (by omega_using [sD]), h10₂, m₂, m₁]) rfl rfl rfl) fun s₃ ⟨m₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  have k13 := (k₁.trans k₂).trans k₃
  refine WP.mono (base_ok aQt .x9 ((k13.gpr .x0 (by decide)).trans h.ws.x0) (((k₂.trans k₃).gpr .x11 (by decide)).trans h11)) fun s₄ ⟨⟨h9, m₄, _⟩, k₄⟩ => ?_
  refine WP.mono (WP.keep [.x7] (Q := fun t => t.gpr .x7 = 0 ∧ t.mem = s₄.mem) (by brun) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨⟨h7, m₅⟩, k₅⟩ => ?_
  have k35 := (k₃.trans k₄).trans k₅
  exact ⟨⟨by rw [m₅, m₄, m₃], (k35.gpr .x8 (by decide)).trans h8, (k₅.gpr .x9 (by decide)).trans h9,
    (((k₂.trans k35).gpr .x12 (by decide))).trans h12, h7⟩, (k13.trans (k₄.trans k₅)).mono (by decide)⟩

theorem dOdd_eq : dOdd = loadEv ++ (([zeroA aQt, copyA aQt aL, divmod aQt aR aE aT, zeroA aU, copyA aU aR] :
    List (Prog isa)) ++ (invFrom aE ++ (([inverse aU aV aX₁ aX₂ aE aT] : List (Prog isa)) ++ (lGe2 ++ (gcdIsOne ++
    ([.block ([ldh .x3 kEv] ++ minv ++ ws ++ base aX₂ .x16 ++ base aR .x17 ++
        ([ldh .x1 kEv, ld .x3 .x16, .sub .x .x1 .x1 .x3, ld .x3 .x17, .mul .x .x3 .x3 .x1, .addImm .x .x3 .x3 1,
          .mul .x .x10 .x3 .x4] : List Instr)),
      zeroA aDd,
      .block (ws ++ base aDd .x8 ++ ([st .x10 .x8] : List Instr) ++ base aQt .x9 ++ ([movi .x7 0] : List Instr)),
      mulAddRow] : List (Prog isa))))))) := by
  simp only [dOdd, List.append_assoc]

/-- `dOdd`, for an odd `e ≥ 3`. -/
theorem dOdd_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {e L : Nat} (he3 : 3 ≤ e) (he64 : e < 2 ^ 64)
    (heo : e % 2 = 1) (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hL : av I s.mem aL = L)
    (hLW : L < 2 ^ (64 * I.W)) :
    WP isa (seqs dOdd) s fun t => KS I s₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem := by
  have hn := h.ws.scr.nowrap
  have hZ := h.hZ
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_using [this]
  have hw2 := h.ws.w2
  rw [dOdd_eq]
  -- `[aE] := e`.
  refine wp_seqs_append (by simp [loadEv]) (by simp) (WP.mono (loadEv_k h he64 hev) fun s₁ ⟨h₁, f₁, e₁⟩ => ?_)
  have vE₁ : av I s₁.mem aE = e := av_of_full e₁ (lt_pow_W h he64)
  have vL₁ : av I s₁.mem aL = L := by rw [f₁.av (by decide) (by decide) (by decide) hZ, hL]
  -- `L = e Q + R`.
  refine wp_seqs_append (by simp) (by simp [invFrom]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₁ (j := aQt) (by decide)) fun s₂ ⟨h₂, f₂, _, _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₂ (o := aQt) (a := aL) (by decide) (by decide) (by decide)) fun s₃ ⟨h₃, f₃, v₃, _, _⟩ =>
      WP.seq (WP.mono (divmod_k h₃ (iQ := aQt) (iR := aR) (iD := aE) (iT := aT) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨h₄, f₄, d₄⟩ =>
        WP.seq (WP.mono (zeroA_k h₄ (j := aU) (by decide)) fun s₅ ⟨h₅, f₅, z₅, _, _⟩ =>
          WP.mono (copyA_k h₅ (o := aU) (a := aR) (by decide) (by decide) (by decide))
            fun s₆ ⟨h₆, f₆, v₆, t₆, _⟩ => ?_))))
  have vE₃ : av I s₃.mem aE = e := by
    rw [f₃.av (by decide) (by decide) (by decide) hZ, f₂.av (by decide) (by decide) (by decide) hZ, vE₁]
  have vQ₃ : av I s₃.mem aQt = L := by rw [v₃, f₂.av (by decide) (by decide) (by decide) hZ, vL₁]
  rw [vE₃, vQ₃] at d₄
  obtain ⟨dR, dQ⟩ := d₄ (by omega_using [heo])
  have hR : L % e < e := Nat.mod_lt _ (by omega_using [heo])
  have vR₄ : av I s₄.mem aR = L % e := divmod_rem hLW dR
  have hok4 : [Rc.arr aQt, Rc.arr aR, Rc.arr aT].all Rc.ok = true := by decide
  have vU₆ : av I s₆.mem aU = L % e := by rw [v₆, f₅.av (by decide) (by decide) (by decide) hZ, vR₄]
  have tU₆ : atop I s₆.mem aU = 0 := by rw [t₆]; exact (wv_zero2 z₅).2
  have pres6 : ∀ j, j < 16 → j ≠ aQt → j ≠ aR → j ≠ aT → j ≠ aU → av I s₆.mem j = av I s₃.mem j :=
    fun j hj h1 h2 h3 h4 => by
      rw [f₆.av (by decide) hj (by simp [h4]) hZ, f₅.av (by decide) hj (by simp [h4]) hZ,
        f₄.av hok4 hj (by simp [h1, h2, h3]) hZ]
  have vE₆ : av I s₆.mem aE = e := by rw [pres6 aE (by decide) (by decide) (by decide) (by decide) (by decide), vE₃]
  have vQ₆ : av I s₆.mem aQt = L / e := by
    rw [f₆.av (by decide) (by decide) (by decide) hZ, f₅.av (by decide) (by decide) (by decide) hZ, dQ]
  have vR₆ : av I s₆.mem aR = L % e := by
    rw [f₆.av (by decide) (by decide) (by decide) hZ, f₅.av (by decide) (by decide) (by decide) hZ, vR₄]
  have vL₆ : av I s₆.mem aL = L := by
    rw [pres6 aL (by decide) (by decide) (by decide) (by decide) (by decide), f₃.av (by decide) (by decide)
      (by decide) hZ, f₂.av (by decide) (by decide) (by decide) hZ, vL₁]
  -- `x = R⁻¹ mod e`.
  refine wp_seqs_append (by simp [invFrom]) (by simp) (WP.mono (invFrom_k h₆ (j := aE) (by decide) (by decide))
    fun s₇ ⟨h₇, f₇, vV₇, vX₁₇, vX₂₇⟩ => ?_)
  have hok7 : [Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂].all Rc.ok = true := by decide
  have vU₇ : av I s₇.mem aU = L % e := by rw [f₇.av hok7 (by decide) (by decide) hZ, vU₆]
  have tU₇ : atop I s₇.mem aU = 0 := by rw [f₇.at hok7 (by decide) (by decide) hZ, tU₆]
  have vE₇ : av I s₇.mem aE = e := by rw [f₇.av hok7 (by decide) (by decide) hZ, vE₆]
  refine wp_seqs_append (by simp) (by simp [lGe2]) ?_
  simp only [seqs]
  refine WP.mono (inverse_k h₇ (iU := aU) (iV := aV) (iX₁ := aX₁) (iX₂ := aX₂) (iM := aE) (iT := aT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) tU₇ (by rw [vV₇, vE₆, vE₇]) vX₁₇ vX₂₇) fun s₈ ⟨h₈, f₈, hinv⟩ => ?_
  rw [vE₇, vU₇] at hinv
  obtain ⟨hg₈, hdv₈, hx₈⟩ := hinv heo (by omega_using [he3])
  generalize hx : av I s₈.mem aX₂ = x at hdv₈ hx₈
  have hokI : [Rc.arr aU, Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT].all Rc.ok = true := by decide
  have vL₈ : av I s₈.mem aL = L := by
    rw [f₈.av hokI (by decide) (by decide) hZ, f₇.av hok7 (by decide) (by decide) hZ, vL₆]
  -- `kOk := ` the masks of `L ≥ 2` and `gcd(R, e) = 1`.
  refine wp_seqs_append (by simp [lGe2, constA]) (by simp [gcdIsOne, constA]) (WP.mono (lGe2_k h₈)
    fun s₉ ⟨h₉, f₉, ok₉⟩ => ?_)
  rw [vL₈] at ok₉
  have vV₉ : av I s₉.mem aV = Nat.gcd (L % e) e := by rw [f₉.av (by decide) (by decide) (by decide) hZ, hg₈]
  refine wp_seqs_append (by simp [gcdIsOne, constA]) (by simp) (WP.mono (gcdIsOne_k h₉ ok₉)
    fun s₁₀ ⟨h₁₀, f₁₀, ok₁₀⟩ => ?_)
  rw [vV₉] at ok₁₀
  have hokC : [Rc.arr aC, Rc.hdr kOk].all Rc.ok = true := by decide
  have pres10 : ∀ j, j < 16 → j ≠ aC → av I s₁₀.mem j = av I s₈.mem j := fun j hj h1 => by
    rw [f₁₀.av hokC hj (by simp [h1]) hZ, f₉.av hokC hj (by simp [h1]) hZ]
  have hxe : x < e := hx₈
  have vX₁₀ : av I s₁₀.mem aX₂ = x := by rw [pres10 aX₂ (by decide) (by decide), hx]
  have vR₁₀ : av I s₁₀.mem aR = L % e := by
    rw [pres10 aR (by decide) (by decide), f₈.av hokI (by decide) (by decide) hZ,
      f₇.av hok7 (by decide) (by decide) hZ, vR₆]
  have vQ₁₀ : av I s₁₀.mem aQt = L / e := by
    rw [pres10 aQt (by decide) (by decide), f₈.av hokI (by decide) (by decide) hZ,
      f₇.av hok7 (by decide) (by decide) hZ, vQ₆]
  have hev₁₀ : word s₁₀.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by
    have hk : ∀ {cs : List Rc} {m m' : Mem}, KF I.B I.W cs m m' → cs.all Rc.ok = true → .hdr kEv ∉ cs →
        word m' I.B (8 * kEv) = word m I.B (8 * kEv) := fun f ok hn => f.word ok (by decide) hn
    rw [hk f₁₀ hokC (by decide), hk f₉ hokC (by decide), hk f₈ hokI (by decide), hk f₇ hok7 (by decide),
      hk f₆ (by decide) (by decide), hk f₅ (by decide) (by decide), hk f₄ hok4 (by decide),
      hk f₃ (by decide) (by decide), hk f₂ (by decide) (by decide), hk f₁ (by decide) (by decide), hev]
  -- `x1 := e − x`, `x10 := c`.
  simp only [seqs]
  refine WP.seq (WP.mono (dOddC_ok h₁₀ he64 hxe (Nat.lt_trans hR he64) heo hev₁₀
    (word0_of_lt hw1 vX₁₀ (Nat.lt_trans hxe he64)) (word0_of_lt hw1 vR₁₀ (Nat.lt_trans hR he64)))
    fun s₁₁ ⟨⟨h1₁₁, einv, hinv₁₁, c₁₁, m₁₁⟩, k₁₁⟩ => ?_)
  have h₁₁ := h₁₀.regs m₁₁ k₁₁
  generalize hcv : ((L % e * (e - x) % 2 ^ 64 + 1) % 2 ^ 64 * einv) % 2 ^ 64 = c at c₁₁
  -- `[aDd] := c`.
  refine WP.seq (WP.mono (zeroA_k h₁₁ (j := aDd) (by decide)) fun s₁₂ ⟨h₁₂, f₁₂, z₁₂, _, k₁₂⟩ => ?_)
  refine WP.seq (WP.mono (dOddD_ok h₁₂) fun s₁₃ ⟨⟨m₁₃, h8, h9, h12, h7⟩, k₁₃⟩ => ?_)
  have sD := h.ws.sl (j := aDd) (by decide)
  have sQ := h.ws.sl (j := aQt) (by decide)
  have spDQ := slot_sep (w := I.W) (j := aDd) (k := aQt) (by decide)
  have o₁₃ := writeW_outside s₁₂.mem I.B (s₁₂.gpr .x10) (d := slot I.W aDd) (by omega_using [hn, sD])
  rw [← m₁₃] at o₁₃
  have f₁₃ := KF.arr1 (B := I.B) (W := I.W) (j := aDd) o₁₃ (Nat.le_refl _) (by omega_using [])
  have h₁₃ := h₁₂.step f₁₃ (all_mut_arr (by decide)) k₁₃
  have c₁₂ : (s₁₂.gpr .x10).toNat = c := by rw [k₁₂.gpr .x10 (by decide)]; exact c₁₁
  have vD₁₃ : wv s₁₃.mem I.B (slot I.W aDd) (I.W + 2) = c := by
    rw [m₁₃, wv_put0 _ z₁₂ (by omega_using [hn, sD]), c₁₂]
  have hokD : [Rc.arr aDd].all Rc.ok = true := by decide
  have vQ₁₃ : av I s₁₃.mem aQt = L / e := by
    rw [f₁₃.av hokD (by decide) (by decide) hZ, f₁₂.av hokD (by decide) (by decide) hZ,
      show av I s₁₁.mem aQt = av I s₁₀.mem aQt by rw [m₁₁], vQ₁₀]
  have h1₁₃ : s₁₃.gpr .x1 = BitVec.ofNat 64 (e - x) := by
    rw [k₁₃.gpr .x1 (by decide), k₁₂.gpr .x1 (by decide), h1₁₁]
  -- `[aDd] += t Q`.
  have hcl : c < 2 ^ 64 := by rw [← hcv]; exact Nat.mod_lt _ (by decide)
  have hQ : L / e < 2 ^ (64 * I.W) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hLW
  have hbound : c + (e - x) * (L / e) < 2 ^ (64 * (I.W + 2)) := by
    have h1 : (e - x) * (L / e) < 2 ^ 64 * 2 ^ (64 * I.W) :=
      Nat.mul_lt_mul_of_lt_of_le (by omega_using [he64]) (Nat.le_of_lt hQ) (by omega_using [dQ, hQ])
    have h2 : 2 ^ 64 + 2 ^ 64 * 2 ^ (64 * I.W) ≤ 2 ^ (64 * (I.W + 2)) := by
      rw [show 64 * (I.W + 2) = 64 + 64 + 64 * I.W by omega_using [], Nat.pow_add, Nat.pow_add]
      have : 1 ≤ 2 ^ (64 * I.W) := Nat.one_le_two_pow
      have : 2 ^ 64 ≤ 2 ^ 64 * 2 ^ (64 * I.W) := Nat.le_mul_of_pos_right _ (by omega_using [this])
      have : 2 * (2 ^ 64 * 2 ^ (64 * I.W)) ≤ 2 ^ 64 * 2 ^ 64 * 2 ^ (64 * I.W) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by decide)
      omega_arith
    omega_using [hcl, h1, h2]
  have vQ' : wv s₁₃.mem I.B (slot I.W aQt) I.W = L / e := vQ₁₃
  have hex : (s₁₃.gpr .x1).toNat = e - x := by
    rw [h1₁₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [he64])]
  refine WP.mono (mulAddRow_ok h₁₃.ws.scr h8 h9 h12 h7 hw1 (by omega_using [hw2]) (by omega_using [sD])
      (by omega_using [sQ]) (by omega_using [spDQ])
    (by rw [vD₁₃, hex, vQ']; exact hbound)) fun t ⟨hv, o, kt⟩ => ?_
  rw [vD₁₃, hex, vQ'] at hv
  have ft := KF.arr1 (B := I.B) (W := I.W) (j := aDd) o (Nat.le_refl _) (Nat.le_refl _)
  have ht := h₁₃.step ft (all_mut_arr (by decide)) kt
  have okt : word t.mem I.B (8 * kOk) = mask (decide (Nat.gcd (L % e) e = 1) && decide (2 ≤ L)) := by
    rw [ft.word hokD (by decide) (by decide), f₁₃.word hokD (by decide) (by decide),
      f₁₂.word hokD (by decide) (by decide), m₁₁, ok₁₀]
  refine ⟨ht, ?_, ⟨_, okt, ?_, ?_⟩⟩
  · have f₁₁ : KF I.B I.W [] s₁₀.mem s₁₁.mem := KF.of_eq m₁₁
    exact (((((((((((((f₁.trans f₂).trans f₃).trans f₄).trans f₅).trans f₆).trans f₇).trans f₈).trans f₉).trans
      f₁₀).trans f₁₁).trans f₁₂).trans f₁₃).trans ft).mono (by simp)
  · -- The inverse exists iff both hold.
    have hQR : L = e * (L / e) + L % e := (Nat.div_add_mod L e).symm
    constructor
    · rintro ⟨d, hd⟩
      by_contra hc
      have : ¬ (2 ≤ L ∧ Nat.gcd (L % e) e = 1) := fun ⟨h1, h2⟩ => hc (by simp [h1, h2])
      rw [VG.Proof.RsaKeyGen.inverse_odd_none he3 hQR this] at hd
      cases hd
    · intro hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have hx1 : (e : Int) ∣ (x : Int) * (L % e : Nat) - 1 := by
        have := hdv₈; rw [hg₈, hc.1] at this; exact_mod_cast this
      exact ⟨_, VG.Proof.RsaKeyGen.inverse_odd he3 he64 hc.2 hQR hR hx1 hxe hinv₁₁⟩
  · intro d hd
    by_cases hc : 2 ≤ L ∧ Nat.gcd (L % e) e = 1
    · have hQR : L = e * (L / e) + L % e := (Nat.div_add_mod L e).symm
      have hx1 : (e : Int) ∣ (x : Int) * (L % e : Nat) - 1 := by
        have := hdv₈; rw [hg₈, hc.2] at this; exact_mod_cast this
      have hio := VG.Proof.RsaKeyGen.inverse_odd he3 he64 hc.1 hQR hR hx1 hxe hinv₁₁
      rw [hcv] at hio
      have hdL := (VG.Proof.RsaKeyGen.inverse_some hio).2 (by omega_using [hc])
      rw [hio] at hd
      cases hd
      exact av_of_full (by rw [hv, Nat.add_comm, Nat.mul_comm]) (by omega_using [hLW, hdL])
    · rw [VG.Proof.RsaKeyGen.inverse_odd_none he3 (Nat.div_add_mod L e).symm hc] at hd
      cases hd

end VG.Proof.RsaKeyGen.AArch64.Key
