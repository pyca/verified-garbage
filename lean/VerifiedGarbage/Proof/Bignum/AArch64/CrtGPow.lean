import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.R2
import VerifiedGarbage.Proof.Bignum.CrtGPow

/-!
# `vg_rsa_private_crt` on AArch64: `G = 2^E mod n`

`gPow`: `K = ⌈w / w_X⌉` (`kLoop_ok`), `D = 64 ((K + 1) w_X - w)` into
slot `sD` (`gHead_ok`), its top bit into `sCnt`, `Y := R mod n`, then a
squaring and a doubling under each bit of `D` from the top (`gBit_ok`,
`gBits_ok`): `Y ≡ 2^D R = 2^(64 w_X (K + 1))` (`gPow_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop eval_nonzero ne_zero_iff)

/-- `M.mm o a b` in the modulus' workspace, keeping `m = N` and `-m⁻¹`. -/
theorem crtMmN_ok (M : Mont) {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (hg : Good t B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) {o a b : Nat} (ho : o < 8)
    (ha : a < 8) (hb : b < 8) (d1 : o ≠ aAcc) (d2 : o ≠ aTmp) (d3 : a ≠ aAcc) (d4 : b ≠ aAcc) (d5 : o ≠ aN)
    (hn : wv t.mem B (slot w aN) w = N) (hinv : ((word t.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv t.mem B (slot w b) w < N) (d6 : a ≠ aTmp := by decide) (d7 : b ≠ aTmp := by decide) :
    WP isa (M.mm o a b) t fun t' => Good t' B Z w minv ∧ wv t'.mem B (slot w aN) w = N ∧
      ((word t'.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧
      wv t'.mem B (slot w o) w < N ∧
      wv t'.mem B (slot w o) w * 2 ^ (64 * w) % N = wv t.mem B (slot w a) w * wv t.mem B (slot w b) w % N ∧
      Arrays B w [aAcc, aTmp, o] t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; omega_arith
  have hnm : aN ∉ [aAcc, aTmp, o] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by decide, by decide, Ne.symm d5⟩
  refine WP.mono (M.mm_ok hg hZ hw hw' ho ha hb d1 d2 d3 d4 hinv (by rw [hn]; exact hB) d6 d7)
    fun t' ⟨hg', hlt', hm, hA, k⟩ => ?_
  rw [hn] at hlt' hm
  exact ⟨hg', by rw [hA.wv_of_not_mem (by decide) hnm hn']; exact hn,
    by rw [hA.word0_of_not_mem (by decide) hnm hn' (by omega_arith)]; exact hinv, hlt', hm, hA, k⟩

/-- `subs` of two numbers: the carry is set iff there is no borrow. -/
theorem subs_ge {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    decide (2 ^ 64 ≤ (BitVec.ofNat 64 a).toNat + (~~~BitVec.ofNat 64 b).toNat + (true).toNat) = decide (b ≤ a) := by
  rw [BitVec.toNat_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Bool.toNat_true]
  exact decide_eq_decide.mpr (by omega_arith)

/-- A step of the loop `x3 += w_X` while `x3 < w`, `K = ⌈w / w_X⌉` steps. -/
theorem kStep_ok {t : State} {w wx K k : Nat} (hwx : 1 ≤ wx) (hw' : w + wx < 2 ^ 32)
    (hK : (w + wx - 1) / wx = K) (hk : k < K)
    (h3 : t.gpr .x3 = BitVec.ofNat 64 (k * wx)) (h5 : t.gpr .x5 = BitVec.ofNat 64 wx)
    (h12 : t.gpr .x12 = BitVec.ofNat 64 w) (h7 : t.gpr .x7 = 0) (h8 : t.gpr .x8 = 1) :
    WP isa (.block [.add .x .x3 .x3 .x5, .subs .x .x4 .x3 .x12, .csel .x .x4 .x7 .x8]) t fun t' =>
      (t'.gpr .x3 = BitVec.ofNat 64 ((k + 1) * wx) ∧ ((t'.gpr .x4).toNat ≠ 0 ↔ k + 1 ≠ K) ∧ t'.mem = t.mem) ∧
      Keep [.x3, .x4] t t' := by
  obtain ⟨hK1, hK2⟩ := kBounds (w := w) hwx
  rw [hK] at hK1 hK2
  have hle : (k + 1) * wx ≤ K * wx := Nat.mul_le_mul_right _ hk
  have hle' : k * wx + wx ≤ K * wx := by rw [← Nat.succ_mul]; exact hle
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t' => t'.gpr .x3 = BitVec.ofNat 64 ((k + 1) * wx) ∧
      t'.gpr .x4 = (if w ≤ (k + 1) * wx then 0 else 1) ∧ t'.mem = t.mem)
    (by brun [h3, h5, h12, h7, h8, ofNat_add_ofNat,
      subs_ge (show k * wx + wx < 2 ^ 64 by omega_arith) (show w < 2 ^ 64 by omega_arith), Nat.succ_mul, decide_eq_true_eq])
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h3', h4', hm'⟩, k'⟩ => ⟨⟨h3', ?_, hm'⟩, k'⟩
  rw [h4']
  have hK' : k + 1 = K ↔ w ≤ (k + 1) * wx := by
    constructor
    · rintro rfl; exact hK1
    · intro h
      rcases Nat.lt_or_ge (k + 1) K with h' | h'
      · have := Nat.mul_le_mul_right wx (show k + 2 ≤ K by omega_arith)
        rw [Nat.succ_mul (k + 1)] at this; omega_arith
      · omega_arith
  split <;> rename_i h
  · rw [show (0 : BitVec 64).toNat = 0 from rfl]
    exact ⟨fun h' => absurd rfl h', fun h' => absurd (hK'.mpr h) h'⟩
  · rw [show (1 : BitVec 64).toNat = 1 from rfl]
    exact ⟨fun _ h' => h (hK'.mp h'), fun _ => by decide⟩

/-- The loop `x3 += w_X` while `x3 < w`, from `x3 = 0`: `x3 = K w_X`. -/
theorem kLoop_ok {s : State} {w wx : Nat} (hwx : 1 ≤ wx) (hw : 1 ≤ w) (hw' : w + wx < 2 ^ 32)
    (h5 : s.gpr .x5 = BitVec.ofNat 64 wx) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 0) (h7 : s.gpr .x7 = 0) (h8 : s.gpr .x8 = 1) :
    WP isa (.loop (.block [.add .x .x3 .x3 .x5, .subs .x .x4 .x3 .x12, .csel .x .x4 .x7 .x8]) (.nonzero .x .x4))
      s fun t => t.gpr .x3 = BitVec.ofNat 64 ((w + wx - 1) / wx * wx) ∧ t.mem = s.mem ∧ Keep [.x3, .x4] s t := by
  generalize hK : (w + wx - 1) / wx = K
  obtain ⟨hK1, hK2⟩ := kBounds (w := w) hwx
  rw [hK] at hK1 hK2
  have hK0 : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h, Nat.zero_mul] at hK1; omega_arith
    · exact h
  refine WP.mono (count_loop (cr := .x4) hK0 (fun k t => t.gpr .x3 = BitVec.ofNat 64 (k * wx) ∧
      t.mem = s.mem ∧ Keep [.x3, .x4] s t) (fun k hk t ⟨h3', hm, k₀⟩ => ?_)
    ⟨by rw [h3, Nat.zero_mul], rfl, Keep.refl _ _⟩) fun t h => h
  exact WP.mono (kStep_ok hwx hw' hK hk h3' ((k₀.gpr .x5 (by decide)).trans h5)
    ((k₀.gpr .x12 (by decide)).trans h12) ((k₀.gpr .x7 (by decide)).trans h7) ((k₀.gpr .x8 (by decide)).trans h8))
    fun t' ⟨⟨h3'', h4'', hm'⟩, k'⟩ => ⟨⟨h3'', hm'.trans hm, (k₀.trans k').mono (by decide)⟩, h4''⟩

/-- `gPow`'s first steps: `D` into slot `sD` and `x3`. -/
def gHead (slotWs : Nat) : List (Prog isa) := [
  .block [ldh .x5 slotWs, ldw .x5 .x5 sW, ldh .x12 sW, movi .x3 0, movi .x7 0, movi .x8 1],
  .loop (.block [.add .x .x3 .x3 .x5, .subs .x .x4 .x3 .x12, .csel .x .x4 .x7 .x8]) (.nonzero .x .x4),
  .block [.add .x .x3 .x3 .x5, .sub .x .x3 .x3 .x12, .lsl .x .x3 .x3 6, sth .x3 Crt.sD]]

/-- The steps of `D`. -/
theorem gHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw30 : w < 2 ^ 30) {sl : Nat} (hsl' : sl < 32) {Bx : Addr} {wx : Nat}
    (hX : word s.mem B (8 * sl) = Bx) (hXw : word s.mem Bx (8 * sW) = BitVec.ofNat 64 wx)
    (hXr : InRegions (s.rd ++ s.wr) (off Bx (8 * sW)) 8) (hwx : 1 ≤ wx) (hwx' : wx ≤ w) :
    WP isa (seqs (gHead sl)) s fun t => t.gpr .x3 = BitVec.ofNat 64 (gD w wx) ∧
      t.mem = s.mem.writeW (off B (8 * Crt.sD)) (BitVec.ofNat 64 (gD w wx)) ∧
      Keep [.x3, .x4, .x5, .x7, .x8, .x12] s t := by
  have hs := hg.scr
  refine WP.seq (WP.mono (WP.keep [.x3, .x5, .x7, .x8, .x12] (Q := fun t => t.gpr .x5 = BitVec.ofNat 64 wx ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x3 = BitVec.ofNat 64 0 ∧ t.gpr .x7 = 0 ∧ t.gpr .x8 = 1 ∧
      t.mem = s.mem) (by
    brun [ldw, hg.x0, hdr_enc hsl', hdr_enc (show sW < 32 by decide), hg.ld hZ hsl', hX, hXr, hXw,
      hg.ld hZ (show sW < 32 by decide), hg.hdr.hw]) rfl rfl rfl)
    fun t₁ ⟨⟨h5₁, h12₁, h3₁, h7₁, h8₁, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (kLoop_ok hwx (by omega_arith) (by omega_arith) h5₁ h12₁ h3₁ h7₁ h8₁) fun t₂ ⟨h3₂, hm₂, k₂⟩ => ?_)
  obtain ⟨hK1, hK2⟩ := kBounds (w := w) hwx
  have hD : gD w wx = 64 * ((w + wx - 1) / wx * wx + wx - w) := rfl
  generalize (w + wx - 1) / wx * wx = a at h3₂ hK1 hK2 hD
  have hsub : BitVec.ofNat 64 (a + wx) - BitVec.ofNat 64 w = BitVec.ofNat 64 (a + wx - w) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega_arith),
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  have h0₂ : t₂.gpr .x0 = B := ((k₁.trans k₂).gpr .x0 (by decide)).trans hg.x0
  have hs₂ := hs.congr (k₁.trans k₂).wr
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (gD w wx) ∧
      t.mem = s.mem.writeW (off B (8 * Crt.sD)) (BitVec.ofNat 64 (gD w wx))) (by
    brun [h0₂, hdr_enc (show Crt.sD < 32 by decide), hs₂.st (show 8 * Crt.sD + 8 ≤ Z by
      have := hdr_lt_slot w 8 (show Crt.sD < 32 by decide); omega_arith), h3₂, (k₂.gpr .x5 (by decide)).trans h5₁,
      (k₂.gpr .x12 (by decide)).trans h12₁, hm₂, hm₁, ofNat_add_ofNat, hsub,
      shl_ofNat (show (a + wx - w) * 2 ^ 6 < 2 ^ 64 by omega_arith)]
    rw [hD, Nat.mul_comm]; exact ⟨rfl, rfl⟩) (by decide) (by decide) (by decide +kernel))
    fun t ⟨h, k⟩ => ⟨h.1, h.2, ((k₁.trans k₂).trans k).mono (by decide)⟩

/-! ## The bits of `D` -/

/-- The loop's body: `Y := Y² R⁻¹`, doubled if the bit is set, and the
next bit. -/
def gBody (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  mul aY aY aY,
  .block [ldh .x3 Crt.sD, ldh .x4 sCnt, .logic .and .x .x3 .x3 .x4],
  .ite (.nonzero .x .x3) (double aN aAcc aTmp aY) (.block []),
  .block [ldh .x3 sCnt, .lsr .x .x3 .x3 1, sth .x3 sCnt]]

theorem gPow_eq (mul : Nat → Nat → Nat → Prog isa) (slotWs : Nat) : gPow mul slotWs =
    gHead slotWs ++ [topBit, .block [sth .x9 sCnt], mul aY aR2 aOne, .loop (seqs (gBody mul)) (.nonzero .x .x3)] :=
  rfl

/-- After the top `j` of the `L + 1` bits of `D`, from `s₀`: `Y ≡ 2^⌊D / 2^(L + 1 - j)⌋ R`. -/
structure GInv (s₀ : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N D L : Nat) (j : Nat) (t : State) :
    Prop where
  good : Good t B Z w minv
  n : wv t.mem B (slot w aN) w = N
  inv : ((word t.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  ylt : wv t.mem B (slot w aY) w < N
  y : wv t.mem B (slot w aY) w % N = 2 ^ (D / 2 ^ (L + 1 - j)) * 2 ^ (64 * w) % N
  d : word t.mem B (8 * Crt.sD) = BitVec.ofNat 64 D
  c : word t.mem B (8 * sCnt) = BitVec.ofNat 64 (2 ^ (L + 1 - j) / 2)
  frm : Frm B (gRanges w) s₀.mem t.mem
  keep : Keep mmRegs s₀ t

theorem bne_and_pow (D k : Nat) (hk : k < 64) :
    (BitVec.ofNat 64 D &&& BitVec.ofNat 64 (2 ^ k) != 0) = !decide (D / 2 ^ k % 2 = 0) := by
  rw [bne, and_pow_beq D k hk]

/-- Bit `L - j` of `D`. -/
theorem gBit_ok (M : Mont) {s₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N D L : Nat}
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hR : Nat.Coprime (2 ^ (64 * w)) N) (hN0 : 0 < N)
    (hL : L < 63) {j : Nat} (hj : j < L + 1) (hI : GInv s₀ B Z w minv N D L j t) :
    WP isa (seqs (gBody M.mm)) t fun t' =>
      GInv s₀ B Z w minv N D L (j + 1) t' ∧ ((t'.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ L + 1) := by
  have hn := hI.good.scr.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  have hc2 : 2 ^ (L + 1 - j) / 2 = 2 ^ (L - j) := by
    rw [show L + 1 - j = (L - j) + 1 by omega_arith, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
  have hpL : 2 ^ (L - j) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega_arith)
  -- `Y := Y²`.
  refine WP.seq (WP.mono (crtMmN_ok M (o := aY) (a := aY) (b := aY) hI.good hZ hw hw' (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hI.n hI.inv hI.ylt)
    fun t₁ ⟨hg₁, hn₁, hinv₁, hlt₁, hm₁, ha₁, k₁⟩ => ?_)
  have hY₁ : wv t₁.mem B (slot w aY) w % N = 2 ^ (2 * (D / 2 ^ (L + 1 - j))) * 2 ^ (64 * w) % N :=
    VG.Proof.Bignum.mont_sq hR hI.y hm₁
  have hd₁ : word t₁.mem B (8 * Crt.sD) = BitVec.ofNat 64 D := by rw [ha₁.hslot (by decide)]; exact hI.d
  have hc₁ : word t₁.mem B (8 * sCnt) = BitVec.ofNat 64 (2 ^ (L - j)) := by
    rw [ha₁.hslot (by decide), hI.c, hc2]
  -- The bit.
  refine WP.seq (WP.mono (WP.keep [.x3, .x4] (Q := fun t₂ =>
      t₂.gpr .x3 = BitVec.ofNat 64 D &&& BitVec.ofNat 64 (2 ^ (L - j)) ∧ t₂.mem = t₁.mem) (by
    brun [hg₁.x0, hdr_enc (show Crt.sD < 32 by decide), hdr_enc (show sCnt < 32 by decide),
      hg₁.ld hZ (show Crt.sD < 32 by decide), hg₁.ld hZ (show sCnt < 32 by decide), hd₁, hc₁])
    (by decide) (by decide) (by decide +kernel)) fun t₂ ⟨⟨h3₂, hm₂⟩, k₂⟩ => ?_)
  have hg₂ : Good t₂ B Z w minv := ⟨hg₁.scr.congr k₂.wr, (k₂.gpr .x0 (by decide)).trans hg₁.x0, hm₂ ▸ hg₁.hdr⟩
  -- Doubled if it is set.
  have hdbl : WP isa (.ite (.nonzero .x .x3) (double aN aAcc aTmp aY) (.block [])) t₂ fun t₃ =>
      Good t₃ B Z w minv ∧ wv t₃.mem B (slot w aY) w < N ∧
      wv t₃.mem B (slot w aY) w % N =
        2 ^ (2 * (D / 2 ^ (L + 1 - j)) + D / 2 ^ (L - j) % 2) * 2 ^ (64 * w) % N ∧
      Arrays B w [aAcc, aTmp, aY] t₂.mem t₃.mem ∧ Keep mmRegs t₂ t₃ := by
    have hev : isa.eval (.nonzero .x .x3) t₂ = some (!decide (D / 2 ^ (L - j) % 2 = 0)) := by
      rw [eval_nonzero, h3₂, bne_and_pow D (L - j) (by omega_arith)]
    by_cases hbit : D / 2 ^ (L - j) % 2 = 0
    · refine WP.ite false (by rw [hev]; simp [hbit]) (by simp) (fun _ => WP.block_nil ⟨hg₂, ?_, ?_,
        fun _ _ => rfl, Keep.refl _ _⟩)
      · rw [hm₂]; exact hlt₁
      · rw [hm₂, hY₁, hbit]; rfl
    · refine WP.ite true (by rw [hev]; simp [hbit]) (fun _ => ?_) (by simp)
      refine WP.mono (double_ok hg₂.scr hg₂.x0 hg₂.hdr hZ hw hw' (mo := aN) (acc := aAcc) (tmp := aTmp)
        (o := aY) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by rw [hm₂, hn₁]; exact hlt₁)) fun t₃ ⟨hv₃, ha₃, k₃⟩ => ?_
      rw [hm₂, hn₁] at hv₃
      refine ⟨⟨hg₂.scr.congr k₃.wr, (k₃.gpr .x0 (by decide)).trans hg₂.x0, ha₃.hdr hg₂.hdr⟩,
        by rw [hv₃]; exact Nat.mod_lt _ hN0, ?_, ha₃, k₃⟩
      rw [hv₃, Nat.mod_mod, Nat.mul_mod 2 (wv t₁.mem B (slot w aY) w) N, hY₁, ← Nat.mul_mod,
        show D / 2 ^ (L - j) % 2 = 1 by omega_arith, Nat.pow_succ, Nat.mul_comm _ 2, Nat.mul_assoc]
  refine WP.seq (WP.mono hdbl fun t₃ ⟨hg₃, hlt₃, hY₃, ha₃, k₃⟩ => ?_)
  -- The next bit.
  have hc₃ : word t₃.mem B (8 * sCnt) = BitVec.ofNat 64 (2 ^ (L - j)) := by
    rw [ha₃.hslot (by decide), hm₂]; exact hc₁
  refine WP.mono (WP.keep [.x3] (Q := fun t' => t'.mem = t₃.mem.writeW (off B (8 * sCnt))
      (BitVec.ofNat 64 (2 ^ (L - j) / 2)) ∧ t'.gpr .x3 = BitVec.ofNat 64 (2 ^ (L - j) / 2)) (by
    brun [hg₃.x0, hdr_enc (show sCnt < 32 by decide), hg₃.ld hZ (show sCnt < 32 by decide),
      hg₃.scr.st (show 8 * sCnt + 8 ≤ Z by have := hdr_lt_slot w 8 (show sCnt < 32 by decide); omega_arith), hc₃,
      shr_ofNat hpL, Nat.pow_one]) (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨hm', h3'⟩, k'⟩ => ?_
  have o' : Outside B (8 * sCnt) 8 t₃.mem t'.mem := by
    rw [hm']; exact writeW_outside _ _ _ (by unfold sCnt sFn; omega_arith)
  have hkeep : ∀ i < 8, i ≠ aAcc → i ≠ aTmp → i ≠ aY → wv t'.mem B (slot w i) w = wv t₁.mem B (slot w i) w :=
    fun i hi h1 h2 h3 => by
      rw [hm', hdrStore_wv _ _ _ (by decide) hi hn', ha₃.wv_of_not_mem hi (by simp [h1, h2, h3]) hn', hm₂]
  have hY' : wv t'.mem B (slot w aY) w = wv t₃.mem B (slot w aY) w := by
    rw [hm', hdrStore_wv _ _ _ (by decide) (by decide) hn']
  have hle : L + 1 - (j + 1) = L - j := by omega_arith
  refine ⟨⟨⟨hg₃.scr.congr k'.wr, (k'.gpr .x0 (by decide)).trans hg₃.x0, by
      rw [hm']; exact Hdr.store hg₃.hdr (by decide) (by decide) _⟩,
    by rw [hkeep aN (by decide) (by decide) (by decide) (by decide)]; exact hn₁,
    by rw [hm', hdrStore_word _ _ _ (by decide) (by decide) hn',
      ha₃.word0_of_not_mem (by decide) (by decide) hn' (by omega_arith), hm₂]; exact hinv₁,
    by rw [hY']; exact hlt₃,
    by rw [hY', hY₃, hle, show 2 * (D / 2 ^ (L + 1 - j)) + D / 2 ^ (L - j) % 2 = D / 2 ^ (L - j) by
      rw [show L + 1 - j = L - j + 1 by omega_arith]; exact div_bit D (L - j)],
    by rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), ha₃.hslot (by decide), hm₂]; exact hd₁,
    by rw [hm', word_writeW_self, hle], ?_, (((hI.keep.trans k₁).trans k₂).trans (k₃.trans k')).mono (by decide)⟩,
    ?_⟩
  · exact (((hI.frm.trans (Frm.of_arrays ha₁ (by simp [gRanges]))).trans
      (by rw [hm₂]; exact Frm.refl _ _ _)).trans (Frm.of_arrays ha₃ (by simp [gRanges]))).trans
      (Frm.of_outside o' (by simp [gRanges]))
  · rw [h3', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    constructor
    · intro h h'
      rw [show L - j = 0 by omega_arith] at h
      exact h rfl
    · intro h
      rcases Nat.eq_zero_or_pos (L - j) with h0 | h0
      · omega_arith
      · rw [show L - j = (L - j - 1) + 1 by omega_arith, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
        exact Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)

/-- The `L + 1` bits of `D`: `Y ≡ 2^D R`. -/
theorem gBits_ok (M : Mont) {s₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N D L : Nat}
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hR : Nat.Coprime (2 ^ (64 * w)) N) (hN0 : 0 < N)
    (hL : L < 63) (h0 : GInv s₀ B Z w minv N D L 0 t) :
    WP isa (.loop (seqs (gBody M.mm)) (.nonzero .x .x3)) t (GInv s₀ B Z w minv N D L (L + 1)) :=
  count_loop (cr := .x3) (by omega_arith) (GInv s₀ B Z w minv N D L)
    (fun _ hj _ hI => gBit_ok M hZ hw hw' hR hN0 hL hj hI) h0

/-! ## `G` -/

/-- `gPow`: `[aY] ≡ 2^(64 w_X (K + 1)) (mod N)` for `K = ⌈w / w_X⌉`, with `w_X` in
the header of the workspace whose base is in slot `sl`. -/
theorem gPow_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem B (slot w aN) w = N)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : N % 2 = 1) (hN1 : 1 < N)
    (hr2' : wv s.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N)
    (hone : wv s.mem B (slot w aOne) w = 1)
    {sl : Nat} (hsl' : sl < 32)
    {Bx : Addr} {wx : Nat} (hX : word s.mem B (8 * sl) = Bx)
    (hXw : word s.mem Bx (8 * sW) = BitVec.ofNat 64 wx)
    (hXr : InRegions (s.rd ++ s.wr) (off Bx (8 * sW)) 8) (hwx : 1 ≤ wx) (hwx' : wx ≤ w) :
    WP isa (seqs (gPow M.mm sl)) s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w aY) w < N ∧
      wv t.mem B (slot w aY) w % N = 2 ^ (64 * wx * ((w + wx - 1) / wx + 1)) % N ∧
      Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)),
        (8 * Crt.sD, 8), (8 * sCnt, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hw' : w < 2 ^ 31 := by omega_arith
  have hs := hg.scr
  have hnw := hs.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hN0 : 0 < N := by omega_arith
  obtain ⟨hD0, hD1, hDE⟩ := gD_bounds hwx hwx' hw30
  rw [gPow_eq]
  refine wp_seqs_append (by simp [gHead]) (by simp) (WP.mono (gHead_ok hg hZ hw hw30 hsl' hX hXw hXr hwx hwx')
    fun t₁ ⟨hax₁, hm₁, k₁⟩ => ?_)
  generalize gD w wx = D at hD0 hD1 hDE hax₁ hm₁
  have hs₁ := hs.congr k₁.wr
  have h0₁ : t₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans hg.x0
  -- The top bit `L` of `D`.
  refine WP.seq (WP.mono (topBit_ok hax₁ hD0 (by omega_arith)) fun t₂ ⟨⟨h9₂, _, hm₂⟩, k₂⟩ => ?_)
  have hL : D.log2 < 62 := (Nat.log2_lt (by omega_arith)).mpr hD1
  have hs₂ := hs₁.congr k₂.wr
  have h0₂ : t₂.gpr .x0 = B := (k₂.gpr .x0 (by decide)).trans h0₁
  refine WP.seq (WP.mono (WP.keep [] (Q := fun t => t.mem = t₂.mem.writeW (off B (8 * sCnt))
      (BitVec.ofNat 64 (2 ^ D.log2))) (by
    brun [h0₂, hdr_enc (show sCnt < 32 by decide), hs₂.st (show 8 * sCnt + 8 ≤ Z by
      have := hdr_lt_slot w 8 (show sCnt < 32 by decide); omega_arith), h9₂]) (by decide) (by decide)
    (by decide +kernel)) fun t₃ ⟨hm₃, k₃⟩ => ?_)
  have hm₃' : t₃.mem = (s.mem.writeW (off B (8 * Crt.sD)) (BitVec.ofNat 64 D)).writeW (off B (8 * sCnt))
      (BitVec.ofNat 64 (2 ^ D.log2)) := by rw [hm₃, hm₂, hm₁]
  have hwv₃ : ∀ j < 8, wv t₃.mem B (slot w j) w = wv s.mem B (slot w j) w := fun j hj => by
    rw [hm₃', hdrStore_wv _ _ _ (by decide) hj hn', hdrStore_wv _ _ _ (by decide) hj hn']
  have hg₃ : Good t₃ B Z w minv := ⟨hs₂.congr k₃.wr, (k₃.gpr .x0 (by decide)).trans h0₂, by
    rw [hm₃']; exact Hdr.store (Hdr.store hg.hdr (by decide) (by decide) _) (by decide) (by decide) _⟩
  -- `Y := R`.
  refine WP.seq (WP.mono (crtMmN_ok M (N := N) (o := aY) (a := aR2) (b := aOne) hg₃ hZ hw hw' (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((hwv₃ aN (by decide)).trans hn)
    (by rw [hm₃', hdrStore_word _ _ _ (by decide) (by decide) hn', hdrStore_word _ _ _ (by decide) (by decide) hn'];
        exact hinv)
    (by rw [hwv₃ aOne (by decide), hone]; exact hN1))
    fun t₄ ⟨hg₄, hn₄, hinv₄, hlt₄, hm₄, ha₄, k₄⟩ => ?_)
  rw [hwv₃ aR2 (by decide), hwv₃ aOne (by decide), hone, Nat.mul_one] at hm₄
  have hY₄ : wv t₄.mem B (slot w aY) w % N = 2 ^ (D / 2 ^ (D.log2 + 1 - 0)) * 2 ^ (64 * w) % N := by
    rw [Nat.sub_zero, Nat.div_eq_of_lt Nat.lt_log2_self, Nat.pow_zero, Nat.one_mul]
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₄, hr2']
  have hfr₄ : Frm B (gRanges w) s.mem t₄.mem := by
    have o1 := writeW_outside s.mem B (BitVec.ofNat 64 D) (d := 8 * Crt.sD) (by unfold Crt.sD sFn; omega_arith)
    have o2 := writeW_outside (s.mem.writeW (off B (8 * Crt.sD)) (BitVec.ofNat 64 D)) B
      (BitVec.ofNat 64 (2 ^ D.log2)) (d := 8 * sCnt) (by unfold sCnt sFn; omega_arith)
    rw [← hm₃'] at o2
    exact ((Frm.of_outside o1 (by simp [gRanges])).trans (Frm.of_outside o2 (by simp [gRanges]))).trans
      (Frm.of_arrays ha₄ (by simp [gRanges]))
  have h0 : GInv s B Z w minv N D D.log2 0 t₄ := ⟨hg₄, hn₄, hinv₄, hlt₄, hY₄,
    by rw [ha₄.hslot (by decide), hm₃', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self],
    by rw [ha₄.hslot (by decide), hm₃', word_writeW_self, Nat.sub_zero, Nat.pow_succ,
      Nat.mul_div_cancel _ (by decide)],
    hfr₄, (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  -- The bits.
  refine WP.mono (gBits_ok M hZ hw hw' hR hN0 (by omega_arith) h0) fun t hI => ⟨hI.good, hI.ylt, ?_, hI.frm, hI.keep⟩
  rw [hI.y, Nat.sub_self, Nat.pow_zero, Nat.div_one, ← Nat.pow_add, hDE]

end VG.Proof.Bignum.AArch64
