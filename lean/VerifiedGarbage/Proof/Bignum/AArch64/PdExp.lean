import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad

/-!
# `vg_rsa_public_precomputed` on AArch64: the exponentiation

The exponentiation starts at the first set bit of `e`: until then `Y` is not
used (`YSt`); at that bit `Y := X`, and after it each bit squares `Y` and
multiplies it by `X` if set (`pExpBit_ok`, over the bits and bytes of `e` in
`pExpLoop_ok`). `finish` leaves `x^e mod N` (`pFinish_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Precomputed
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff count_loop read_one)

variable {M : Mont}

/-- What the exponentiation keeps: the working space, the modulus `N` (and
its low word, for `-m⁻¹`), and `X ≡ x R`. -/
structure ExpCtx (t : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N X : Nat) : Prop where
  good : Good t B Z w minv
  n : wv t.mem B (slot w aN) w = N
  inv : ((word t.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  x : wv t.mem B (slot w aXm) w = X

theorem ExpCtx.of_arrays {t t' : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X : Nat}
    (hc : ExpCtx t B Z w minv N X) (hg : Good t' B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w)
    (ha : Arrays B w [aAcc, aTmp, aY] t.mem t'.mem) : ExpCtx t' B Z w minv N X := by
  have hn : B.toNat + slot w 8 ≤ 2 ^ 64 := by have := hc.good.scr.nowrap; omega_using [hZ, this]
  exact ⟨hg, by rw [ha.wv_of_not_mem (by decide) (by decide) hn]; exact hc.n,
    by rw [ha.word0_of_not_mem (by decide) (by decide) hn hw]; exact hc.inv,
    by rw [ha.wv_of_not_mem (by decide) (by decide) hn]; exact hc.x⟩

theorem ExpCtx.store {t t' : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X : Nat}
    (hc : ExpCtx t B Z w minv N X) (hZ : slot w 8 ≤ Z) {i : Nat} (hi : 16 ≤ i) (hi' : i < 32)
    {v : BitVec 64} (hm : t'.mem = t.mem.writeW (off B (8 * i)) v) (hwr : t'.wr = t.wr)
    (h0 : t'.gpr .x0 = B) : ExpCtx t' B Z w minv N X := by
  have hn : B.toNat + slot w 8 ≤ 2 ^ 64 := by have := hc.good.scr.nowrap; omega_using [hZ, this]
  exact ⟨⟨hc.good.scr.congr hwr, h0, hm ▸ Hdr.store hc.good.hdr hi hi' v⟩,
    by rw [hm, hdrStore_wv _ _ _ hi' (by decide) hn]; exact hc.n,
    by rw [hm, hdrStore_word _ _ _ hi' (by decide) hn]; exact hc.inv,
    by rw [hm, hdrStore_wv _ _ _ hi' (by decide) hn]; exact hc.x⟩

theorem ExpCtx.mem {t t' : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X : Nat}
    (hc : ExpCtx t B Z w minv N X) (hm : t'.mem = t.mem) {regs : List Reg} (k : Keep regs t t')
    (hr : .x0 ∉ regs) : ExpCtx t' B Z w minv N X :=
  ⟨⟨hc.good.scr.congr k.wr, (k.gpr .x0 hr).trans hc.good.x0, hm ▸ hc.good.hdr⟩, hm ▸ hc.n, hm ▸ hc.inv, hm ▸ hc.x⟩

/-- Whether the exponentiation started, into `x3`. -/
theorem startedTest_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N x E : Nat}
    (hg : Good t B Z w minv) (hZ : slot w 8 ≤ Z) (hy : YSt t.mem B w N x E) :
    WP isa (.block startedTest) t fun t' => isa.eval (.nonzero .x .x3) t' = some (!decide (E = 0)) ∧
      t'.mem = t.mem ∧ Keep [.x3] t t' := by
  have hn := hg.scr.nowrap
  have hl : InRegions (t.rd ++ t.wr) (off B (8 * sStarted)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show sStarted < 32 by decide); omega_using [hZ, this])
  refine WP.mono (WP.keep [.x3] (Q := fun t' => t'.gpr .x3 = (if E = 0 then 0 else 1) ∧ t'.mem = t.mem) (by
    unfold startedTest
    brun [hg.x0, hdr_enc (show sStarted < 32 by decide), hl, hy.started]) (by decide) (by decide)
      (by decide +kernel)) fun t' ⟨⟨h3, hm⟩, k⟩ => ⟨?_, hm, k⟩
  rw [eval_nonzero, h3]
  by_cases h : E = 0 <;> simp [h]

theorem eval_nz_ofNat {t : State} {r : Reg} {n : Nat} (h : t.gpr r = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    isa.eval (.nonzero .x r) t = some (decide (n ≠ 0)) := by
  rw [eval_nonzero, ne_zero_iff, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-- `start`: `Y := X`, and the exponentiation started. -/
theorem start_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X : Nat}
    (hc : ExpCtx t B Z w minv N X) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa start t fun t' => ExpCtx t' B Z w minv N X ∧ wv t'.mem B (slot w aY) w = X ∧
      word t'.mem B (8 * sStarted) = 1 ∧ Frm B (startRanges w) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hs := hc.good.scr
  have hn := hs.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hZ, hn]
  have hX := slot_le (w := w) (show aXm < 8 by decide)
  have hY := slot_le (w := w) (show aY < 8 by decide)
  have hXY : slot w aXm + 8 * (w + 2) ≤ slot w aY := by unfold slot aXm aY; omega_using []
  have hYs := hdr_lt_slot w aY (show sStarted < 32 by decide)
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  unfold start
  refine WP.seq (WP.mono (WP.keep [.x12, .x16, .x17] (Q := fun t₁ => t₁.gpr .x12 = BitVec.ofNat 64 w ∧
      t₁.gpr .x16 = off B (slot w aXm) ∧ t₁.gpr .x17 = off B (slot w aY) ∧ t₁.mem = t.mem) (by
    brun [hc.good.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aXm < 32 by decide),
      hdr_enc (show sArr aY < 32 by decide), hl sW (by decide), hl (sArr aXm) (by decide),
      hl (sArr aY) (by decide), hc.good.hdr.hw, hc.good.hdr.harr aXm (by decide),
      hc.good.hdr.harr aY (by decide)]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h12, h16, h17, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (copyWords_ok h16 h17 h12 hw hw' (by omega_using [hn', hY])
    (fun j hj => by rw [k₁.rd, k₁.wr]; exact hs.ld (by omega_using [hZ, hY, hXY, hj]))
    (fun j hj => by rw [k₁.wr]; exact hs.st (by omega_using [hZ, hY, hj]))
    (fun j hj b hb => Or.inl
        (by rw [ofs_off B (d := slot w aXm + 8 * j) (i := b) (by omega_using [hn', hY, hXY, hj, hb])]; omega_using [hXY, hj, hb])))
    fun t₂ ⟨hv₂, _, ho₂, _, _, k₂⟩ => ?_)
  rw [hm₁, hc.x] at hv₂
  rw [hm₁] at ho₂
  have k12 := k₁.trans k₂
  have ha₂ : Arrays B w [aAcc, aTmp, aY] t.mem t₂.mem :=
    Arrays.of_outside (j := aY) (by simp) ho₂ (Nat.le_refl _) (by omega_using [])
  have hc₂ : ExpCtx t₂ B Z w minv N X := hc.of_arrays ⟨hs.congr k12.wr,
    (k12.gpr .x0 (by decide)).trans hc.good.x0, ha₂.hdr hc.good.hdr⟩ hZ hw ha₂
  refine WP.mono (WP.keep [.x3] (Q := fun t' => t'.mem = t₂.mem.writeW (off B (8 * sStarted)) (1 : BitVec 64)) (by
    brun [hc₂.good.x0, hdr_enc (show sStarted < 32 by decide),
      hc₂.good.scr.st (d := 8 * sStarted) (by have := hdr_lt_slot w 8 (show sStarted < 32 by decide); omega_using [hZ, this])]
    rfl) (by decide) (by decide) (by decide +kernel)) fun t' ⟨hm', k'⟩ => ?_
  refine ⟨ExpCtx.store hc₂ hZ (i := sStarted) (by decide) (by decide) hm' k'.wr
    ((k'.gpr .x0 (by decide)).trans hc₂.good.x0), ?_, by rw [hm', word_writeW_self], ?_,
    (k12.trans k').mono (by decide)⟩
  · rw [hm', hdrStore_wv (i := sStarted) (j := aY) _ _ _ (by decide) (by decide) hn']; exact hv₂
  · rw [hm']
    exact (Frm.of_outside (ho₂.mono (o' := slot w aY) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using []))
      (by simp [startRanges])).trans
      (Frm.of_outside (writeW_outside _ B _ (d := 8 * sStarted) (by omega_using [hn', hY, hYs])) (by simp [startRanges]))

/-- `Y := Y²` once started. -/
theorem pSq_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E : Nat}
    (hc : ExpCtx t B Z w minv N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hy : YSt t.mem B w N x E)
    (hz : isa.eval (.nonzero .x .x3) t = some (!decide (E = 0))) :
    WP isa (.ite (.nonzero .x .x3) (M.mm aY aY aY) (.block [])) t fun t' => ExpCtx t' B Z w minv N X ∧
      YSt t'.mem B w N x (2 * E) ∧ Arrays B w [aAcc, aTmp, aY] t.mem t'.mem ∧ Keep mmRegs t t' := by
  rcases hy with ⟨h0, hs0⟩ | ⟨h0, hs1, Y, hY, hYN, hYc⟩
  · refine WP.ite false (by rw [hz, h0]; rfl) (by simp) (fun _ => WP.block_nil ⟨hc, ?_,
      fun _ _ => rfl, Keep.refl _ _⟩)
    exact .inl ⟨by omega_using [h0], hs0⟩
  · refine WP.ite true (by rw [hz]; simp [h0]) (fun _ => ?_) (by simp)
    refine WP.mono (M.mm_ok (o := aY) (a := aY) (b := aY) hc.good hZ hw hw' (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
      (by rw [hc.n, hY]; exact hYN)) fun t₂ ⟨hg₂, hlt₂, hmm₂, ha₂, k₂⟩ => ?_
    rw [hc.n] at hlt₂
    rw [hc.n, hY] at hmm₂
    exact ⟨hc.of_arrays hg₂ hZ (by omega_using [hw]) ha₂, .inr ⟨by omega_using [h0], by rw [ha₂.hslot (by decide)]; exact hs1,
      _, rfl, hlt₂, VG.Proof.Bignum.mont_sq hR hYc hmm₂⟩, ha₂, k₂⟩

/-- If the bit is set, `Y := Y X` once started, or `Y := X` and started. -/
theorem pMul_ok {t₃ : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E V : Nat}
    (hc₃ : ExpCtx t₃ B Z w minv N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hy₃ : YSt t₃.mem B w N x (2 * E)) (hz₃ : isa.eval (.nonzero .x .x3) t₃ = some (decide (V / 128 % 2 ≠ 0))) :
    WP isa (.ite (.nonzero .x .x3) (.seq (.block startedTest) (.ite (.nonzero .x .x3) (M.mm aY aY aXm) start))
      (.block [])) t₃
      fun t₄ => ExpCtx t₄ B Z w minv N X ∧ YSt t₄.mem B w N x (2 * E + V / 128 % 2) ∧
        Frm B (pBitRanges w) t₃.mem t₄.mem ∧ (∀ k < 32, k ≠ sStarted → word t₄.mem B (8 * k) = word t₃.mem B (8 * k)) ∧
        Keep mmRegs t₃ t₄ := by
  have hn := hc₃.good.scr.nowrap
  have h8 : 256 ≤ slot w 0 := by unfold slot hdrBytes; omega_using []
  by_cases hbit : V / 128 % 2 = 0
  · refine WP.ite false (by rw [hz₃]; simp [hbit]) (by simp) (fun _ => WP.block_nil ⟨hc₃, ?_,
      Frm.refl _ _ _, fun _ _ _ => rfl, Keep.refl _ _⟩)
    rw [hbit, Nat.add_zero]; exact hy₃
  · refine WP.ite true (by rw [hz₃]; simp [hbit]) (fun _ => ?_) (by simp)
    rw [show V / 128 % 2 = 1 by omega_using [hbit]]
    refine WP.seq (WP.mono (startedTest_ok hc₃.good hZ hy₃) fun t₄ ⟨hz₄, hm₄, k₄⟩ => ?_)
    have hc₄ := hc₃.mem hm₄ k₄ (by decide)
    rcases hy₃ with ⟨h0, hs0⟩ | ⟨h0, hs1, Y, hY, hYN, hYc⟩
    · refine WP.ite false (by rw [hz₄, h0]; rfl) (by simp) (fun _ => ?_)
      refine WP.mono (start_ok hc₄ hZ (by omega_arith) hw') fun t₅ ⟨hc₅, hv₅, hs₅, hf₅, k₅⟩ => ?_
      refine ⟨hc₅, .inr ⟨by omega_using [], hs₅, X, hv₅, hXN, by rw [show 2 * E + 1 = 1 by omega_using [h0], Nat.pow_one]; exact hXc⟩,
        by rw [← hm₄]; exact hf₅.mono (startRanges_sub w), fun k hk hk' => ?_, (k₄.trans k₅).mono (by decide)⟩
      rw [hf₅.word_eq (fun r hr => by
        simp only [startRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        have := hdr_lt_slot w aY hk
        rcases hr with rfl | rfl
        · omega_using [this]
        · simp only [sStarted, sFn] at hk' ⊢; omega_using [hk']) (by omega_using [hk]), hm₄]
    · refine WP.ite true (by rw [hz₄]; simp [h0]) (fun _ => ?_) (by simp)
      refine WP.mono (M.mm_ok (o := aY) (a := aY) (b := aXm) hc₄.good hZ hw hw' (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hc₄.inv
        (by rw [hc₄.x, hc₄.n]; exact hXN)) fun t₅ ⟨hg₅, hlt₅, hmm₅, ha₅, k₅⟩ => ?_
      rw [hc₄.n] at hlt₅
      rw [hc₄.n, hc₄.x, hm₄, hY] at hmm₅
      refine ⟨hc₄.of_arrays hg₅ hZ (by omega_using [hw]) ha₅, .inr ⟨by omega_using [], by rw [ha₅.hslot (by decide), hm₄]; exact hs1,
        _, rfl, hlt₅, VG.Proof.Bignum.mont_mulx hR hYc hXc hmm₅⟩,
        by rw [← hm₄]; exact Frm.of_arrays ha₅ (by simp [pBitRanges, bitRanges]),
        fun k hk _ => by rw [ha₅.hslot hk, hm₄], (k₄.trans k₅).mono (by decide)⟩

theorem bit7 (V : Nat) (hV : V < 2 ^ 64) :
    (BitVec.ofNat 64 V >>> 7) &&& 1 = BitVec.ofNat 64 (V / 128 % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hV,
    Nat.shiftRight_eq_div_pow, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat]
  omega_using []

/-- One bit of `e`: `YSt` for the prefix `E` becomes `YSt` for `2 E + bit`,
for the bit at the top of the byte `V / 128 mod 2`; `V` doubles and the bit
count `b` drops, into `x3`. -/
theorem pExpBit_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E V b : Nat}
    (hc : ExpCtx t B Z w minv N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hy : YSt t.mem B w N x E)
    (hV : word t.mem B (8 * sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 62)
    (hb : word t.mem B (8 * sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b) (hb' : b < 2 ^ 31) :
    WP isa (Precomputed.expBit M.mm) t fun t' => ExpCtx t' B Z w minv N X ∧ YSt t'.mem B w N x (2 * E + V / 128 % 2) ∧
      word t'.mem B (8 * sV) = BitVec.ofNat 64 (V + V) ∧ word t'.mem B (8 * sBit) = BitVec.ofNat 64 (b - 1) ∧
      t'.gpr .x3 = BitVec.ofNat 64 (b - 1) ∧ Frm B (pBitRanges w) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.good.scr.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hZ, hn]
  have eV : sV = 25 := rfl
  have eB : sBit = 24 := rfl
  have eS : sStarted = 27 := rfl
  have h8 : 256 ≤ slot w 0 := by unfold slot hdrBytes; omega_using []
  unfold Precomputed.expBit
  -- Whether started.
  refine WP.seq (WP.mono (startedTest_ok hc.good hZ hy) fun t₁ ⟨hz₁, hm₁, k₁⟩ => ?_)
  have hc₁ := hc.mem hm₁ k₁ (by decide)
  -- `Y := Y²` if started.
  refine WP.seq (WP.mono (pSq_ok (x := x) hc₁ hZ hw hw' hR (by rw [hm₁]; exact hy) hz₁) fun t₂ ⟨hc₂, hy₂, ha₂, k₂⟩ => ?_)
  have hV₂ : word t₂.mem B (8 * sV) = BitVec.ofNat 64 V := by rw [ha₂.hslot (by decide), hm₁]; exact hV
  have hb₂ : word t₂.mem B (8 * sBit) = BitVec.ofNat 64 b := by rw [ha₂.hslot (by decide), hm₁]; exact hb
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi =>
    hc₂.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  -- The bit, into `x3`.
  refine WP.seq (WP.mono (WP.keep [.x3, .x4] (Q := fun t₃ => t₃.gpr .x3 = BitVec.ofNat 64 (V / 128 % 2) ∧
      t₃.mem = t₂.mem) (by
    unfold bitTest
    brun [hc₂.good.x0, hdr_enc (show sV < 32 by decide), hl₂ sV (by decide), hV₂,
      show BitVec.setWidth 64 (1#16) = (1 : BitVec 64) from rfl, bit7 V (by omega_using [hV'])])
      (by decide) (by decide) (by decide +kernel))
    fun t₃ ⟨⟨hz₃, hm₃⟩, k₃⟩ => ?_)
  have hc₃ := hc₂.mem hm₃ k₃ (by decide)
  have hy₃ : YSt t₃.mem B w N x (2 * E) := by rw [hm₃]; exact hy₂
  -- If the bit is set: `Y := Y X` if started, `Y := X` and started if not.
  refine WP.seq (WP.mono (pMul_ok hc₃ hZ hw hw' hR hXN hXc hy₃ (eval_nz_ofNat hz₃ (by omega_using [])))
    fun t₄ ⟨hc₄, hy₄, hf₄, hh₄, k₄⟩ => ?_)
  -- The next bit.
  have hV₄ : word t₄.mem B (8 * sV) = BitVec.ofNat 64 V := by
    rw [hh₄ sV (by decide) (by decide), hm₃]; exact hV₂
  have hb₄ : word t₄.mem B (8 * sBit) = BitVec.ofNat 64 b := by
    rw [hh₄ sBit (by decide) (by decide), hm₃]; exact hb₂
  have hl₄ : ∀ i < 32, InRegions (t₄.rd ++ t₄.wr) (off B (8 * i)) 8 := fun i hi =>
    hc₄.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  have hs₄ : ∀ i < 32, InRegions t₄.wr (off B (8 * i)) 8 := fun i hi =>
    hc₄.good.scr.st (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  have hV₄' : (t₄.mem.writeW (off B (8 * sV)) (BitVec.ofNat 64 (V + V))).readW (off B (8 * sBit)) 64 =
      BitVec.ofNat 64 b := by
    rw [← hb₄]; exact (writeW_outside _ B _ (by omega_using [eV])).word (by unfold sV sBit sFn; omega_using []) (by omega_using [eB])
  refine WP.mono (WP.keep [.x3] (Q := fun t' => t'.mem = (t₄.mem.writeW (off B (8 * sV))
      (BitVec.ofNat 64 (V + V))).writeW (off B (8 * sBit)) (BitVec.ofNat 64 (b - 1)) ∧
      t'.gpr .x3 = BitVec.ofNat 64 (b - 1)) (by
    unfold bitNext
    brun [hc₄.good.x0, hdr_enc (show sV < 32 by decide), hdr_enc (show sBit < 32 by decide),
      hl₄ sV (by decide), hs₄ sV (by decide), hV₄, hV₄', hs₄ sBit (by decide), hl₄ sBit (by decide),
      BitVec.ofNat_add_ofNat, ofNat_sub_one' hb1 (by omega_using [hb'])]) (by decide) (by decide) (by decide +kernel))
    fun t' ⟨⟨hm', h3'⟩, k'⟩ => ?_
  have o1 := writeW_outside t₄.mem B (BitVec.ofNat 64 (V + V)) (d := 8 * sV) (by unfold sV sFn; omega_using [])
  have o2 := writeW_outside (t₄.mem.writeW (off B (8 * sV)) (BitVec.ofNat 64 (V + V))) B
    (BitVec.ofNat 64 (b - 1)) (d := 8 * sBit) (by omega_using [eB])
  have hkeep : ∀ j < 8, wv t'.mem B (slot w j) w = wv t₄.mem B (slot w j) w := fun j hj => by
    rw [hm', o2.wv (by have := hdr_lt_slot w j (show sBit < 32 by decide); omega_using [this])
      (by have := slot_le (w := w) hj; omega_using [hn', this]),
      o1.wv (by have := hdr_lt_slot w j (show sV < 32 by decide); omega_using [this])
      (by have := slot_le (w := w) hj; omega_using [hn', this])]
  have hw0 : word t'.mem B (slot w aN) = word t₄.mem B (slot w aN) := by
    have := slot_le (w := w) (show aN < 8 by decide)
    rw [hm', o2.word (by have := hdr_lt_slot w aN (show sBit < 32 by decide); omega_using [this]) (by omega_using [hn', this]),
      o1.word (by have := hdr_lt_slot w aN (show sV < 32 by decide); omega_using [this]) (by omega_using [hn', this])]
  have hst' : word t'.mem B (8 * sStarted) = word t₄.mem B (8 * sStarted) := by
    rw [hm', hdrStore_hdr (i := sBit) _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr (i := sV) _ _ _ (by decide) (by decide) (by decide)]
  have hgood : Good t' B Z w minv := ⟨hc₄.good.scr.congr k'.wr, (k'.gpr .x0 (by decide)).trans hc₄.good.x0,
    by rw [hm']; exact Hdr.store (Hdr.store hc₄.good.hdr (by decide) (by decide) _) (by decide) (by decide) _⟩
  refine ⟨⟨hgood, by rw [hkeep aN (by decide)]; exact hc₄.n, by rw [hw0]; exact hc₄.inv,
    by rw [hkeep aXm (by decide)]; exact hc₄.x⟩, YSt.congr hy₄ hst' (hkeep aY (by decide)), ?_, ?_, h3', ?_,
    ((((k₁.trans k₂).trans k₃).trans k₄).trans k').mono (by decide)⟩
  · rw [hm', o2.word (by unfold sV sBit sFn; omega_using []) (by omega_using [eV]), word_writeW_self]
  · rw [hm', word_writeW_self]
  · rw [hm']
    exact ((((by rw [hm₁]; exact Frm.refl _ _ _ : Frm B (pBitRanges w) t.mem t₁.mem).trans
      (Frm.of_arrays ha₂ (by simp [pBitRanges, bitRanges]))).trans (by rw [hm₃]; exact Frm.refl _ _ _)).trans hf₄).trans
      ((Frm.of_outside o1 (by simp [pBitRanges, bitRanges])).trans (Frm.of_outside o2 (by simp [pBitRanges, bitRanges])))

/-! ## The bits of a byte -/

/-- After `j` bits of the byte `v` from `t₀`, after the prefix `E`. -/
structure PBitInv (t₀ : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N X x E v : Nat) (j : Nat)
    (t : State) : Prop where
  ctx : ExpCtx t B Z w minv N X
  y : YSt t.mem B w N x (E * 2 ^ j + v / 2 ^ (8 - j))
  v : word t.mem B (8 * sV) = BitVec.ofNat 64 (v * 2 ^ j)
  b : word t.mem B (8 * sBit) = BitVec.ofNat 64 (8 - j)
  frm : Frm B (pBitRanges w) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

/-- Bit `j` of the byte `v`. -/
theorem pBitStep_ok {t s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E v : Nat}
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hv : v < 256) {j : Nat} (hj : j < 8) (hI : PBitInv t B Z w minv N X x E v j s) :
    WP isa (Precomputed.expBit M.mm) s fun s' => PBitInv t B Z w minv N X x E v (j + 1) s' ∧
      ((s'.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ 8) := by
  have hp : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega_using [hj])
  refine WP.mono (pExpBit_ok hI.ctx hZ hw hw' hR hXN hXc hI.y hI.v
    (by have := Nat.mul_le_mul_left v hp; omega_using [hv, this]) hI.b (by omega_using [hj]) (by omega_using []))
    fun s' ⟨hc', hy', hV', hb', h3', hfr', k'⟩ => ⟨⟨hc', ?_, ?_, ?_,
      hI.frm.trans hfr', (hI.keep.trans k').mono (by decide)⟩, ?_⟩
  · rwa [show 2 * (E * 2 ^ j + v / 2 ^ (8 - j)) + v * 2 ^ j / 128 % 2 =
      E * 2 ^ (j + 1) + v / 2 ^ (8 - (j + 1)) by
        rw [Nat.mul_add, Nat.add_assoc, bit_step (by omega_using [hj]), show 7 - j = 8 - (j + 1) by omega_using [],
          Nat.pow_succ, Nat.mul_comm 2 (E * 2 ^ j), Nat.mul_assoc]] at hy'
  · rw [hV', ← Nat.two_mul, Nat.pow_succ]; congr 1; rw [Nat.mul_comm, Nat.mul_assoc]
  · rw [hb']; congr 1
  · rw [h3', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [])]; omega_using [hj]

theorem pBits_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E v : Nat}
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hv : v < 256) (h0 : PBitInv t B Z w minv N X x E v 0 t) :
    WP isa (.loop (Precomputed.expBit M.mm) (.nonzero .x .x3)) t (PBitInv t B Z w minv N X x E v 8) :=
  count_loop (by decide) (PBitInv t B Z w minv N X x E v)
    (fun _ hj _ hI => pBitStep_ok hZ hw hw' hR hXN hXc hv hj hI) h0

/-! ## The bytes -/

/-- After `i` bytes of `e` (`L` bytes `eb` at `ep`) from `t₀`. -/
structure PByteInv (t₀ : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N X x : Nat) (ep : Addr)
    (L : Nat) (eb : List Byte) (i : Nat) (t : State) : Prop where
  ctx : ExpCtx t B Z w minv N X
  y : YSt t.mem B w N x (pre eb i)
  idx : word t.mem B (8 * sI) = BitVec.ofNat 64 i
  e : word t.mem B (8 * sE) = ep
  len : word t.mem B (8 * sElen) = BitVec.ofNat 64 L
  frm : Frm B (pExpRanges w) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

theorem byte_val (b : Byte) : BitVec.setWidth 64 (BitVec.setWidth 32 b) = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [byte_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := b.isLt; omega_using [])]

theorem byteHead_eq : byteHead = ([ldh .x3 sE, ldh .x4 sI] : List Instr) ++
    ([.add .x .x3 .x3 .x4, .ldrb .x3 .x3 0, sth .x3 sV, movi .x3 8, sth .x3 sBit] : List Instr) := rfl

/-- `byteHead`'s loads: `e` and the byte index. -/
theorem pByteHead1_ok {t₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} {i : Nat} (hZ : slot w 8 ≤ Z) (hI : PByteInv t₀ B Z w minv N X x ep L eb i t) :
    WP isa (.block [ldh .x3 sE, ldh .x4 sI]) t fun t₁ =>
      t₁.gpr .x3 = ep ∧ t₁.gpr .x4 = BitVec.ofNat 64 i ∧ PByteInv t₀ B Z w minv N X x ep L eb i t₁ := by
  have hc := hI.ctx
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi =>
    hc.good.scr.ld (by have := hdr_lt_slot w 8 hi; have := hc.good.scr.nowrap; omega_arith)
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t₁ => t₁.gpr .x3 = ep ∧ t₁.gpr .x4 = BitVec.ofNat 64 i ∧
      t₁.mem = t.mem) (by
    brun [hc.good.x0, hdr_enc (show sE < 32 by decide), hdr_enc (show sI < 32 by decide), hl sE (by decide),
      hl sI (by decide), hI.e, hI.idx]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h1, h2, hm⟩, k⟩ => ⟨h1, h2, ?_⟩
  exact ⟨hc.mem hm k (by decide), hm ▸ hI.y, hm ▸ hI.idx, hm ▸ hI.e, hm ▸ hI.len, hm ▸ hI.frm,
    (hI.keep.trans k).mono (by decide)⟩

/-- `byteHead`'s byte of `e` into `sV`, and the bit count 8: the start of the
bits. -/
theorem pByteHead2_ok {t₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} {i : Nat} (hZ : slot w 8 ≤ Z) (hL : eb.length = L) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith))
    (hout : ∀ i < L, Z ≤ ofs B (ep + BitVec.ofNat 64 i))
    (hI : PByteInv t₀ B Z w minv N X x ep L eb i t) (h3 : t.gpr .x3 = ep) (h4 : t.gpr .x4 = BitVec.ofNat 64 i) :
    WP isa (.block [.add .x .x3 .x3 .x4, .ldrb .x3 .x3 0, sth .x3 sV, movi .x3 8, sth .x3 sBit]) t fun t₁ =>
      t₁.mem = (t.mem.writeW (off B (8 * sV)) (BitVec.ofNat 64 (eb[i]'(by omega_using [hL, hi])).toNat)).writeW
        (off B (8 * sBit)) (BitVec.ofNat 64 8) ∧ Keep [.x3] t t₁ ∧
      PBitInv t₁ B Z w minv N X x (pre eb i) (eb[i]'(by omega_using [hL, hi])).toNat 0 t₁ := by
  have eV : sV = 25 := rfl
  have eB : sBit = 24 := rfl
  have hc := hI.ctx
  have hn := hc.good.scr.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hZ, hn]
  have hs : ∀ i < 32, InRegions t.wr (off B (8 * i)) 8 := fun i hi =>
    hc.good.scr.st (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  have hrdi : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.rd, hI.keep.wr]; exact hrd i hi
  have hbi : t.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_using [hL, hi]) := by
    rw [hI.frm _ fun r hr => Or.inr (by have := pExpRanges_le w r hr; have := hout i hi; omega_arith)]
    exact hbytes i hi
  refine WP.mono (WP.keep [.x3] (Q := fun t₁ => t₁.mem = (t.mem.writeW (off B (8 * sV))
      (BitVec.ofNat 64 (eb[i]'(by omega_using [hL, hi])).toNat)).writeW (off B (8 * sBit)) (BitVec.ofNat 64 8)) (by
    brun [hc.good.x0, h3, h4, hdr_enc (show sV < 32 by decide), hdr_enc (show sBit < 32 by decide),
      hrdi, read_one, hbi, byte_val, hs sV (by decide), hs sBit (by decide)]
    rfl) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨hm₁, k₁⟩ => ⟨hm₁, k₁, ?_⟩
  have hc₁ : ExpCtx t₁ B Z w minv N X := ⟨⟨hc.good.scr.congr k₁.wr, (k₁.gpr .x0 (by decide)).trans hc.good.x0,
    by rw [hm₁]; exact Hdr.store (Hdr.store hc.good.hdr (by decide) (by decide) _) (by decide) (by decide) _⟩,
    by rw [hm₁, hdrStore_wv (i := sBit) (j := aN) _ _ _ (by decide) (by decide) hn',
      hdrStore_wv (i := sV) (j := aN) _ _ _ (by decide) (by decide) hn']; exact hc.n,
    by rw [hm₁, hdrStore_word (i := sBit) (j := aN) _ _ _ (by decide) (by decide) hn',
      hdrStore_word (i := sV) (j := aN) _ _ _ (by decide) (by decide) hn']; exact hc.inv,
    by rw [hm₁, hdrStore_wv (i := sBit) (j := aXm) _ _ _ (by decide) (by decide) hn',
      hdrStore_wv (i := sV) (j := aXm) _ _ _ (by decide) (by decide) hn']; exact hc.x⟩
  have hv : (eb[i]'(by omega_arith)).toNat < 256 := (eb[i]'(by omega_using [hL, hi])).isLt
  refine ⟨hc₁, ?_, ?_, ?_, Frm.refl _ _ _, Keep.refl _ _⟩
  · rw [Nat.pow_zero, Nat.mul_one, Nat.sub_zero, Nat.div_eq_of_lt (show _ < 2 ^ 8 from hv), Nat.add_zero]
    exact YSt.congr hI.y (by rw [hm₁, hdrStore_hdr (i := sBit) _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr (i := sV) _ _ _ (by decide) (by decide) (by decide)])
      (by rw [hm₁, hdrStore_wv (i := sBit) (j := aY) _ _ _ (by decide) (by decide) hn',
        hdrStore_wv (i := sV) (j := aY) _ _ _ (by decide) (by decide) hn'])
  · rw [hm₁, hdrStore_hdr (i := sBit) (k := sV) _ _ _ (by decide) (by decide) (by decide),
      word_writeW_self, Nat.pow_zero, Nat.mul_one]
  · rw [hm₁, word_writeW_self]

theorem ofNat_sub_ne {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b).toNat ≠ 0 ↔ b ≠ a := by
  have hb' : b < 2 ^ 64 := by omega_using [hb, ha]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb']
  omega_using [ha, hb']

/-- One byte of `e`: its eight bits, then the next byte. -/
theorem pByte_ok {t₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr} {L : Nat}
    {eb : List Byte} {i : Nat} (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hL : eb.length = L) (hL' : L < 2 ^ 31) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_using [hL, h]))
    (hout : ∀ i < L, Z ≤ ofs B (ep + BitVec.ofNat 64 i))
    (hI : PByteInv t₀ B Z w minv N X x ep L eb i t) :
    WP isa (.seq (.block byteHead) (.seq (.loop (Precomputed.expBit M.mm) (.nonzero .x .x3)) (.block byteNext))) t
      fun t' => PByteInv t₀ B Z w minv N X x ep L eb (i + 1) t' ∧ ((t'.gpr .x3).toNat ≠ 0 ↔ i + 1 ≠ L) := by
  have hn := hI.ctx.good.scr.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  rw [byteHead_eq]
  refine WP.seq ((WP.block_append_iff).mpr (WP.mono (pByteHead1_ok hZ hI) fun tₐ ⟨h3ₐ, h4ₐ, hIₐ⟩ =>
    WP.mono (pByteHead2_ok hZ hL hi hrd hbytes hout hIₐ h3ₐ h4ₐ) fun t₁ ⟨hm₁, k₁, hB0⟩ => ?_))
  have hv : (eb[i]'(by omega_using [hL, hi])).toNat < 256 := (eb[i]'(by omega_using [hL, hi])).isLt
  refine WP.seq (WP.mono (pBits_ok hZ hw hw' hR hXN hXc hv hB0) fun t₂ h₂ => ?_)
  -- The next byte.
  have hc₂ := h₂.ctx
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi =>
    hc₂.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  have hs₂ : ∀ i < 32, InRegions t₂.wr (off B (8 * i)) 8 := fun i hi =>
    hc₂.good.scr.st (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  have hh₂ : ∀ k < 32, k ≠ sV → k ≠ sBit → k ≠ sStarted → word t₂.mem B (8 * k) = word tₐ.mem B (8 * k) :=
    fun k hk h1 h2 h3 => by
      rw [h₂.frm.word_eq (pBitRanges_hdr w hk h1 h2 h3) (by omega_using [hk]), hm₁,
        hdrStore_hdr (i := sBit) _ _ _ (by decide) hk (Ne.symm h2),
        hdrStore_hdr (i := sV) _ _ _ (by decide) hk (Ne.symm h1)]
  have hidx₂ := (hh₂ sI (by decide) (by decide) (by decide) (by decide)).trans hIₐ.idx
  have he₂ := (hh₂ sE (by decide) (by decide) (by decide) (by decide)).trans hIₐ.e
  have hlen₂ := (hh₂ sElen (by decide) (by decide) (by decide) (by decide)).trans hIₐ.len
  have hlen₂' : (t₂.mem.writeW (off B (8 * sI)) (BitVec.ofNat 64 (i + 1))).readW (off B (8 * sElen)) 64 =
      BitVec.ofNat 64 L := by
    rw [← hlen₂]; exact hdrStore_hdr (i := sI) _ _ _ (by decide) (by decide) (by decide)
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t' => t'.mem = t₂.mem.writeW (off B (8 * sI))
      (BitVec.ofNat 64 (i + 1)) ∧ t'.gpr .x3 = BitVec.ofNat 64 L - BitVec.ofNat 64 (i + 1)) (by
    unfold byteNext
    brun [hc₂.good.x0, hdr_enc (show sI < 32 by decide), hdr_enc (show sElen < 32 by decide),
      hl₂ sI (by decide), hs₂ sI (by decide), hidx₂, BitVec.ofNat_add_ofNat, hl₂ sElen (by decide), hlen₂'])
      (by decide) (by decide) (by decide +kernel))
    fun t' ⟨⟨hm', h3'⟩, k'⟩ => ⟨?_, by rw [h3']; exact ofNat_sub_ne (by omega_using [hi]) (by omega_using [hL'])⟩
  refine ⟨ExpCtx.store hc₂ hZ (i := sI) (by decide) (by decide) hm' k'.wr ((k'.gpr .x0 (by decide)).trans
    hc₂.good.x0), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hy := h₂.y
    rw [show pre eb i * 2 ^ 8 + (eb[i]'(by omega_using [hL, hi])).toNat / 2 ^ (8 - 8) = pre eb (i + 1) by
      rw [pre_succ eb (by omega_using [hL, hi])]; omega_using []] at hy
    exact YSt.congr hy (by rw [hm', hdrStore_hdr (i := sI) _ _ _ (by decide) (by decide) (by decide)])
      (by rw [hm', hdrStore_wv (i := sI) (j := aY) _ _ _ (by decide) (by decide) hn'])
  · rw [hm', word_writeW_self]
  · rw [hm', hdrStore_hdr (i := sI) _ _ _ (by decide) (by decide) (by decide)]; exact he₂
  · rw [hm', hdrStore_hdr (i := sI) _ _ _ (by decide) (by decide) (by decide)]; exact hlen₂
  · have f₁ : Frm B (pExpRanges w) tₐ.mem t₁.mem := by
      rw [hm₁]
      exact (Frm.of_outside (writeW_outside tₐ.mem B _ (d := 8 * sV) (by unfold sV sFn; omega_using []))
        (by simp [pExpRanges, pBitRanges, bitRanges])).trans
        (Frm.of_outside (writeW_outside _ B _ (d := 8 * sBit) (by unfold sBit sFn; omega_using []))
          (by simp [pExpRanges, pBitRanges, bitRanges]))
    have f₃ : Frm B (pExpRanges w) t₂.mem t'.mem := by
      rw [hm']; exact Frm.of_outside (writeW_outside _ B _ (d := 8 * sI) (by unfold sI sFn; omega_using []))
        (by simp [pExpRanges])
    exact ((hIₐ.frm.trans f₁).trans (h₂.frm.mono (pBitRanges_sub w))).trans f₃
  · exact (((hIₐ.keep.trans k₁).trans h₂.keep).trans k').mono (by decide)

/-- The loop's start: byte index 0, not started. -/
theorem pExpInit_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} (hc : ExpCtx t B Z w minv N X) (hZ : slot w 8 ≤ Z)
    (he : word t.mem B (8 * sE) = ep) (hlen : word t.mem B (8 * sElen) = BitVec.ofNat 64 L) :
    WP isa (.block [movi .x3 0, sth .x3 sI, sth .x3 sStarted]) t (PByteInv t B Z w minv N X x ep L eb 0) := by
  have hn := hc.good.scr.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hZ, hn]
  have hst : ∀ i < 32, InRegions t.wr (off B (8 * i)) 8 := fun i hi =>
    hc.good.scr.st (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  refine WP.mono (WP.keep [.x3] (Q := fun t₁ => t₁.mem = (t.mem.writeW (off B (8 * sI))
      (0 : BitVec 64)).writeW (off B (8 * sStarted)) (0 : BitVec 64)) (by
    brun [hc.good.x0, hdr_enc (show sI < 32 by decide), hdr_enc (show sStarted < 32 by decide),
      hst sI (by decide), hst sStarted (by decide)]
    rfl) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨hm₁, k₁⟩ => ?_
  have hc₁ : ExpCtx t₁ B Z w minv N X := ⟨⟨hc.good.scr.congr k₁.wr, (k₁.gpr .x0 (by decide)).trans hc.good.x0,
    by rw [hm₁]; exact Hdr.store (Hdr.store hc.good.hdr (by decide) (by decide) _) (by decide) (by decide) _⟩,
    by rw [hm₁, hdrStore_wv (i := sStarted) (j := aN) _ _ _ (by decide) (by decide) hn',
      hdrStore_wv (i := sI) (j := aN) _ _ _ (by decide) (by decide) hn']; exact hc.n,
    by rw [hm₁, hdrStore_word (i := sStarted) (j := aN) _ _ _ (by decide) (by decide) hn',
      hdrStore_word (i := sI) (j := aN) _ _ _ (by decide) (by decide) hn']; exact hc.inv,
    by rw [hm₁, hdrStore_wv (i := sStarted) (j := aXm) _ _ _ (by decide) (by decide) hn',
      hdrStore_wv (i := sI) (j := aXm) _ _ _ (by decide) (by decide) hn']; exact hc.x⟩
  refine ⟨hc₁, .inl ⟨pre_zero eb, by rw [hm₁, word_writeW_self]⟩, ?_, ?_, ?_, ?_, k₁.mono (by decide)⟩
  · rw [hm₁, hdrStore_hdr (i := sStarted) _ _ _ (by decide) (by decide) (by decide), word_writeW_self]; rfl
  · rw [hm₁, hdrStore_hdr (i := sStarted) _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr (i := sI) _ _ _ (by decide) (by decide) (by decide)]; exact he
  · rw [hm₁, hdrStore_hdr (i := sStarted) _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr (i := sI) _ _ _ (by decide) (by decide) (by decide)]; exact hlen
  · rw [hm₁]
    exact (Frm.of_outside (writeW_outside _ B _ (d := 8 * sI) (by unfold sI sFn; omega_using [])) (by simp [pExpRanges])).trans
      (Frm.of_outside (writeW_outside _ B _ (d := 8 * sStarted) (by unfold sStarted sFn; omega_using []))
        (by simp [pExpRanges, pBitRanges]))

/-- The exponentiation: `YSt` for `e`, the `L` bytes `eb` at `ep`, outside the
working space. -/
theorem pExpLoop_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} (hc : ExpCtx t B Z w minv N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w)
    (hw' : w < 2 ^ 31) (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N)
    (hXc : X % N = x * 2 ^ (64 * w) % N)
    (he : word t.mem B (8 * sE) = ep) (hlen : word t.mem B (8 * sElen) = BitVec.ofNat 64 L)
    (hL : eb.length = L) (hL1 : 1 ≤ L) (hL' : L < 2 ^ 31)
    (hrd : ∀ i < L, InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_using [hL, h]))
    (hout : ∀ i < L, Z ≤ ofs B (ep + BitVec.ofNat 64 i)) :
    WP isa (Precomputed.expLoop M.mm) t fun t' => ExpCtx t' B Z w minv N X ∧
      YSt t'.mem B w N x (Spec.Rsa.os2ip eb) ∧ Frm B (pExpRanges w) t.mem t'.mem ∧ Keep mmRegs t t' := by
  unfold Precomputed.expLoop
  refine WP.seq (WP.mono (pExpInit_ok (x := x) (eb := eb) hc hZ he hlen) fun t₁ h₁ => ?_)
  refine WP.mono (count_loop (cr := .x3) (n := L) (by omega_using [hL1]) (PByteInv t B Z w minv N X x ep L eb)
    (fun i hi s hI => pByte_ok hZ hw hw' hR hXN hXc hL hL' hi hrd hbytes hout hI) h₁) fun s hI => ?_
  exact ⟨hI.ctx, by rw [← pre_len, hL]; exact hI.y, hI.frm, hI.keep⟩

/-! ## The result -/

/-- `finish`: `Y R⁻¹`, which is `x^E mod N`, or 1 if `E = 0`. -/
theorem pFinish_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E : Nat}
    (hc : ExpCtx t B Z w minv N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hN1 : 1 < N) (hone : wv t.mem B (slot w aOne) w = 1)
    (hy : YSt t.mem B w N x E) :
    WP isa (finish M.mm) t fun t' => Good t' B Z w minv ∧ wv t'.mem B (slot w aY) w = x ^ E % N ∧
      Frm B (finRanges w) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.good.scr.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hZ, hn]
  unfold finish
  refine WP.seq (WP.mono (startedTest_ok hc.good hZ hy) fun t₁ ⟨hz₁, hm₁, k₁⟩ => ?_)
  have hc₁ := hc.mem hm₁ k₁ (by decide)
  rcases hy with ⟨h0, -⟩ | ⟨h0, -, Y, hY, hYN, hYc⟩
  · refine WP.ite false (by rw [hz₁, h0]; rfl) (by simp) (fun _ => ?_)
    have hl : ∀ i < 32, InRegions (t₁.rd ++ t₁.wr) (off B (8 * i)) 8 := fun i hi =>
      hc₁.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
    refine WP.seq (WP.mono (WP.keep [.x12, .x9, .x13] (Q := fun t₂ => t₂.gpr .x12 = BitVec.ofNat 64 w ∧
        t₂.gpr .x9 = 1 ∧ t₂.gpr .x13 = BitVec.ofNat 64 0 ∧ t₂.mem = t₁.mem) (by
      brun [hc₁.good.x0, hdr_enc (show sW < 32 by decide), hl sW (by decide), hc₁.good.hdr.hw]) (by decide) (by decide) (by decide +kernel))
      fun t₂ ⟨⟨h12, h9, h13, hm₂⟩, k₂⟩ => ?_)
    have hc₂ := hc₁.mem hm₂ k₂ (by decide)
    refine WP.mono (setWord_ok hc₂.good.scr hc₂.good.x0 hc₂.good.hdr hZ h12 hw' (o := aY) (by decide)
      (i := 0) (by omega_using [hw]) h13) fun t' ⟨hv, ho, k₃⟩ => ?_
    have ha : Arrays B w [aY] t₂.mem t'.mem := Arrays.of_outside (j := aY) (by simp) ho (Nat.le_refl _) (Nat.le_refl _)
    refine ⟨⟨hc₂.good.scr.congr k₃.wr, (k₃.gpr .x0 (by decide)).trans hc₂.good.x0, ha.hdr hc₂.good.hdr⟩, ?_, ?_,
      ((k₁.trans k₂).trans k₃).mono (by decide)⟩
    · rw [hv, h9, h0]
      simp only [Nat.pow_zero, Nat.mul_zero, Nat.mod_eq_of_lt hN1]; rfl
    · rw [hm₂, hm₁] at ha
      exact Frm.of_arrays ha (by simp [finRanges])
  · refine WP.ite true (by rw [hz₁]; simp [h0]) (fun _ => ?_) (by simp)
    refine WP.mono (M.mm_ok (o := aY) (a := aY) (b := aOne) hc₁.good hZ hw hw' (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hc₁.inv
      (by rw [hc₁.n, hm₁, hone]; exact hN1)) fun t' ⟨hg', hlt, hmm, ha, k₂⟩ => ?_
    rw [hc₁.n] at hlt
    rw [hc₁.n, hm₁, hY, hone, Nat.mul_one] at hmm
    refine ⟨hg', ?_, by rw [hm₁] at ha; exact Frm.of_arrays ha (by simp [finRanges]), (k₁.trans k₂).mono (by decide)⟩
    rw [← Nat.mod_eq_of_lt hlt]
    exact VG.Proof.Bignum.mont_cancel hR (by rw [hmm, hYc])

end VG.Proof.Bignum.AArch64
