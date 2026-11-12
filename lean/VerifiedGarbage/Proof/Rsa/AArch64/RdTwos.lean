module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
import VerifiedGarbage.Proof.Rsa.AArch64.RdPieces
public import VerifiedGarbage.Proof.Rsa.AArch64.RdStages
public import VerifiedGarbage.Proof.Bignum.ShiftStages
import VerifiedGarbage.Proof.Rsa.RecoverDetWords
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `vg_rsa_recover_primes_det` on AArch64: the halvings

`twos_ok`: `64 v` steps of `RecoverDet.twoStep` from `(n - 1, X mod 2^(64 v), X)`,
`u` and `x` narrow (arrays 2 and 3) and `X` wide (array 6).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Rsa.RecoverDet

/-- After `j` halvings. -/
structure TwI (I : RpIn) (m₀ : Mem) (c : Bool) (N : Nat) (st : Nat × Nat × Nat) (j : Nat) (t : State) : Prop where
  g : G I m₀ (vk I.k) c t
  val : (wv t.mem I.B (slot (vk I.k) nU) (vk I.k), wv t.mem I.B (slot (vk I.k) nXn) (vk I.k),
    wv t.mem I.B (slot (Wk I.k) wX) (Wk I.k)) = (twoStep (64 * Wk I.k))^[j] st
  zU : word t.mem I.B (slot (vk I.k) nU + 8 * vk I.k) = 0
  zX : word t.mem I.B (slot (vk I.k) nXn + 8 * vk I.k) = 0
  n : wv t.mem I.B (slot (vk I.k) 0) (vk I.k) = N
  one : wv t.mem I.B (slot (vk I.k) nOne) (vk I.k + 2) = 1

/-- The halvings' start: `u = n - 1`, `x = X mod 2^(64 v)`, one, and `x6 := 64 v`. -/
theorem twosInit_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I)
    {N X : Nat} (hN : wv s.mem I.B (slot (vk I.k) 0) (vk I.k) = N) (hN1 : 1 ≤ N)
    (hX : wv s.mem I.B (slot (Wk I.k) wX) (Wk I.k) = X) :
    WP isa (seqs (([.block setNar] : List (Prog isa)) ++ oneA nOne ++ ([zeroA nU, subA nU Public.aN nOne, zeroA nXn,
      copyA nXn (2 * wX)] : List (Prog isa)))) s fun t => TwI I m₀ c N (N - 1, X % 2 ^ (64 * vk I.k), X) 0 t := by
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv1 : 1 ≤ vk I.k := by have := L.k1; simp only [vk]; omega
  have hb32 : slot (vk I.k) 32 ≤ 2 ^ 64 := by
    have := h.bndv L (j := 31) (k := vk I.k + 2) (by decide) (Nat.le_refl _)
    have : slot (vk I.k) 32 = _ := slot_succ (vk I.k) 31; omega
  have s0 := slot_lt (w := vk I.k) (show 0 < 32 by decide)
  have s1 := slot_lt (w := vk I.k) (show nOne < 32 by decide)
  have s2 := slot_lt (w := vk I.k) (show nU < 32 by decide)
  have s3 := slot_lt (w := vk I.k) (show nXn < 32 by decide)
  have s12 := slot_lt (w := vk I.k) (show 2 * wX + 1 < 32 by decide)
  have e12 : slot (Wk I.k) wX = slot (vk I.k) (2 * wX) := slot_wide _ _
  have sW6 : slot (vk I.k) (2 * wX) + 8 * Wk I.k ≤ 2 ^ 64 := by
    have := h.bndW L (j := wX) (k := Wk I.k) (by decide) (by omega); rw [e12] at this; exact this
  rw [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [oneA]) (WP.mono (h.setNar_ok L) fun s₁ ⟨g₁, f₁, k₁⟩ => ?_)
  have hN₁ : wv s₁.mem I.B (slot (vk I.k) 0) (vk I.k) = N := by rw [Frm.hdrW_wv f₁ (slot_ge _ _) (by omega), hN]
  have hX₁ : wv s₁.mem I.B (slot (vk I.k) (2 * wX)) (Wk I.k) = X := by
    rw [Frm.hdrW_wv f₁ (slot_ge _ _) sW6, ← e12, hX]
  refine wp_seqs_append (by simp [oneA]) (by simp) (WP.mono (oneA_ok g₁ (j := nOne) (by decide))
    fun s₂ ⟨g₂, v₂, o₂, k₂⟩ => ?_)
  have hN₂ : wv s₂.mem I.B (slot (vk I.k) 0) (vk I.k) = N := by
    rw [o₂.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), hN₁]
  have hX₂ : wv s₂.mem I.B (slot (vk I.k) (2 * wX)) (Wk I.k) = X := by
    rw [o₂.wv (.inr (by have := slot_lt (w := vk I.k) (show nOne < 2 * wX by decide); omega))
      sW6, hX₁]
  have one₂ : wv s₂.mem I.B (slot (vk I.k) nOne) (vk I.k) = 1 := by
    rw [wv_low_of_lt (w := vk I.k + 2) (by omega) (by rw [v₂]; exact Nat.one_lt_two_pow (by omega)), v₂]
  simp only [seqs]
  -- `u = n - 1`.
  refine WP.seq (WP.mono (zeroA_ok g₂.ws (j := nU) (by decide)) fun s₃ ⟨z₃, o₃, _, _, _, k₃⟩ => ?_)
  have g₃ := g₂.out (by decide) (Nat.le_refl _) o₃ k₃ (by decide)
  refine WP.seq (WP.mono (subA_ok g₃.ws (o := nU) (a := Public.aN) (b := nOne) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₄ ⟨v₄, _, _, o₄, k₄⟩ => ?_)
  have g₄ := g₃.out (by decide) (by omega) o₄ k₄ (by decide)
  rw [show slot (vk I.k) Public.aN = slot (vk I.k) 0 from rfl] at v₄
  rw [show wv s₃.mem I.B (slot (vk I.k) 0) (vk I.k) = N by
      rw [o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega)]; exact hN₂,
    show wv s₃.mem I.B (slot (vk I.k) nOne) (vk I.k) = 1 by
      rw [o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega)]; exact one₂] at v₄
  have hu : wv s₄.mem I.B (slot (vk I.k) nU) (vk I.k) = N - 1 := by
    simp only [decide_eq_true hN1, Bool.not_true, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at v₄; omega
  -- `x`.
  refine WP.seq (WP.mono (zeroA_ok g₄.ws (j := nXn) (by decide)) fun s₅ ⟨z₅, o₅, _, _, _, k₅⟩ => ?_)
  have g₅ := g₄.out (by decide) (Nat.le_refl _) o₅ k₅ (by decide)
  refine WP.mono (copyA_ok g₅.ws (o := nXn) (a := 2 * wX) (by decide) (by decide) (by decide))
    fun s₆ ⟨v₆, o₆, _, _, k₆⟩ => ?_
  have g₆ := g₅.out (by decide) (by omega) o₆ k₆ (by decide)
  have hb12 : slot (vk I.k) (2 * wX) + 8 * (vk I.k + 2) ≤ 2 ^ 64 := by omega
  have x₅ : wv s₅.mem I.B (slot (vk I.k) (2 * wX)) (Wk I.k) = X := by
    rw [o₅.wv (.inr (by have := slot_lt (w := vk I.k) (show nXn < 2 * wX by decide); omega)) sW6,
      o₄.wv (.inr (by have := slot_lt (w := vk I.k) (show nU < 2 * wX by decide); omega)) sW6,
      o₃.wv (.inr (by have := slot_lt (w := vk I.k) (show nU < 2 * wX by decide); omega)) sW6, hX₂]
  refine ⟨g₆, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.iterate_zero_apply, Prod.mk.injEq, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · rw [o₆.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
        o₅.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), hu]
    · rw [v₆, ← wv_mod _ _ _ (show vk I.k ≤ Wk I.k by omega), x₅]
    · rw [e12, o₆.wv (.inr (by have := slot_lt (w := vk I.k) (show nXn < 2 * wX by decide); omega)) sW6, x₅]
  · rw [o₆.word (wd_sep (by decide) (by omega) (by omega)) (by omega),
      o₅.word (wd_sep (by decide) (by omega) (by omega)) (by omega), o₄.word (.inr (by omega)) (by omega)]
    exact (wv_eq_zero_iff _ _ _ _).mp z₃ (vk I.k) (by omega)
  · rw [o₆.word (.inr (by omega)) (by omega)]
    exact (wv_eq_zero_iff _ _ _ _).mp z₅ (vk I.k) (by omega)
  · rw [o₆.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₅.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₄.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), hN₂]
  · rw [o₆.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₅.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₄.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), v₂]

/-! ## The trailing zeros of `[A] ∨ [B]` -/

open VG.Proof.Bignum.ShiftStages (tz dvd_iff tz_spec dvd_gcd_iff)

/-- `rbit` then `clz`: the trailing zeros of a word `x ≠ 0`. -/
theorem ctz_tz (x : BitVec 64) (hx : x ≠ 0) : x.reverse.clz.toNat = tz x.toNat := by
  have hn : x.toNat ≠ 0 := fun e => hx (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
  have hc : x.reverse.clz = x.ctz := rfl
  rw [hc]
  have hlt : x.ctz.toNat < 64 := by have := BitVec.ctz_lt_iff_ne_zero.mpr hx; rw [BitVec.lt_def] at this; simpa using this
  have hlow : 2 ^ x.ctz.toNat ∣ x.toNat := by
    rw [Nat.dvd_iff_mod_eq_zero]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hi : i < x.ctz.toNat
    · simp only [hi, decide_true, Bool.true_and]
      have := BitVec.getLsbD_false_of_lt_ctz hi
      rwa [BitVec.getLsbD] at this
    · simp [hi]
  have hbit : x.toNat / 2 ^ x.ctz.toNat % 2 = 1 := by
    have := BitVec.getLsbD_true_ctz_of_ne_zero hx
    rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq] at this
    simpa using this
  apply Nat.le_antisymm
  · exact (dvd_iff hn _).mp hlow
  · obtain ⟨hd, _⟩ := tz_spec x.toNat hn
    by_contra hcon
    have : 2 ^ (x.ctz.toNat + 1) ∣ x.toNat := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hd
    obtain ⟨q, hq⟩ := this
    rw [hq, Nat.pow_succ, Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _), Nat.mul_mod_right] at hbit
    omega

theorem exec_rbit (s : State) (d n : Reg) :
    exec (Instr.rbit .x d n) s = some (s.write .x d (s.gpr n).reverse) := by
  simp [exec, State.read]

theorem exec_clz (s : State) (d n : Reg) :
    exec (Instr.clz .x d n) s = some (s.write .x d (s.gpr n).clz) := by
  simp [exec, State.read]

/-- What `ctzOr`'s scan knows after `i` words of `f`: if a nonzero word was found, the first, `j₀`;
else that none is. -/
def ScanI (f : Nat → BitVec 64) (i : Nat) (found : Bool) (j₀ : Nat) : Prop :=
  if found then j₀ < i ∧ f j₀ ≠ 0 ∧ ∀ j < j₀, f j = 0 else ∀ j < i, f j = 0

/-- The registers the scan writes. -/
abbrev czRegs : List Reg := [.x3, .x4, .x5, .x6, .x8, .x9, .x10, .x14, .x16, .x17]

/-- After `i` words of the scan. -/
structure CzI (s₀ : State) (B : Addr) (dA dB : Nat) (f : Nat → BitVec 64) (i : Nat) (t : State) : Prop where
  keep : Keep czRegs s₀ t
  mem : t.mem = s₀.mem
  x16 : t.gpr .x16 = off B (dA + 8 * i)
  x17 : t.gpr .x17 = off B (dB + 8 * i)
  x8 : t.gpr .x8 = BitVec.ofNat 64 (64 * i)
  found : ∃ fd j₀, t.gpr .x6 = mask fd ∧
    t.gpr .x5 = (if fd then BitVec.ofNat 64 (64 * j₀ + tz (f j₀).toNat) else 0) ∧ ScanI f i fd j₀

theorem czStep_ok {s₀ : State} {B : Addr} {Z dA dB n : Nat} (hs : Scr s₀ B Z) (h7 : s₀.gpr .x7 = 0)
    (h15 : s₀.gpr .x15 = mask true) (hA : dA + 8 * n ≤ Z) (hB : dB + 8 * n ≤ Z)
    {i : Nat} (hi : i < n) {t : State} (hI : CzI s₀ B dA dB (fun j => word s₀.mem B (dA + 8 * j) ||| word s₀.mem B (dB + 8 * j)) i t) :
    WP isa (.block (ctzScan ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      CzI s₀ B dA dB (fun j => word s₀.mem B (dA + 8 * j) ||| word s₀.mem B (dB + 8 * j)) (i + 1) t' ∧
        t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hnw := hs.nowrap
  have hst := hs.congr hI.keep.wr
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  have t15 : t.gpr .x15 = mask true := (hI.keep.gpr .x15 (by decide)).trans h15
  obtain ⟨fd, j₀, h6, h5, hS⟩ := hI.found
  generalize hy : word s₀.mem B (dA + 8 * i) ||| word s₀.mem B (dB + 8 * i) = y
  have wa : word t.mem B (dA + 8 * i) = word s₀.mem B (dA + 8 * i) := by rw [hI.mem]
  have wb : word t.mem B (dB + 8 * i) = word s₀.mem B (dB + 8 * i) := by rw [hI.mem]
  refine WP.mono (WP.keep czRegs (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .x16 = off B (dA + 8 * (i + 1)) ∧
      t'.gpr .x17 = off B (dB + 8 * (i + 1)) ∧ t'.gpr .x8 = BitVec.ofNat 64 (64 * (i + 1)) ∧
      t'.gpr .x6 = mask (fd || decide (y ≠ 0)) ∧
      t'.gpr .x5 = (if (!fd && decide (y ≠ 0)) then BitVec.ofNat 64 (64 * i + tz y.toNat) else t.gpr .x5) ∧
      t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1) (by
    unfold ctzScan
    brun [exec_rbit, exec_clz, hI.x16, hI.x17, hI.x8, t7, t15, h5, h6, wa, wb, hy,
      hst.ld (show dA + 8 * i + 8 ≤ Z by omega), hst.ld (show dB + 8 * i + 8 ≤ Z by omega), nz_mask,
      show mask fd ^^^ mask true = mask (!fd) by cases fd <;> rfl, mask_and', sel_mask, mask_or']
    refine ⟨by rw [show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega], by rw [show dB + 8 * i + 8 = dB + 8 * (i + 1) by omega],
      by rw [show (64#64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, BitVec.ofNat_add_ofNat,
        show 64 * (i + 1) = 64 * i + 64 by omega], ?_⟩
    by_cases hc : (!fd && decide (y ≠ 0)) = true
    · have hy0 : y ≠ 0 := by simpa using (Bool.and_eq_true _ _).mp hc |>.2
      simp only [hc, ↓reduceIte]
      rw [BitVec.add_comm, ← ctz_tz y hy0, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]) (by decide) (by decide) (by decide +kernel))
    fun t' ⟨⟨hm, x16, x17, x8, x6, x5, x14⟩, k⟩ => ⟨⟨(hI.keep.trans k).mono (by decide), hm.trans hI.mem, x16, x17, x8, ?_⟩, x14⟩
  unfold ScanI at hS ⊢
  cases fd
  · simp only [Bool.false_eq_true, ↓reduceIte] at hS h5
    by_cases hy0 : y = 0
    · refine ⟨false, j₀, by rw [x6, hy0]; rfl, by rw [x5, hy0, h5]; rfl, ?_⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hS j hj
      · rw [hy]; exact hy0
    · have hd : decide (y ≠ 0) = true := decide_eq_true hy0
      refine ⟨true, i, by rw [x6, hd]; rfl, by rw [x5, hy, hd]; rfl, ?_⟩
      simp only [↓reduceIte]
      exact ⟨by omega, by rw [hy]; exact hy0, hS⟩
  · simp only [↓reduceIte] at hS h5
    refine ⟨true, j₀, by rw [x6]; rfl, by rw [x5, h5]; rfl, ?_⟩
    simp only [↓reduceIte]
    exact ⟨by omega, hS.2.1, hS.2.2⟩

/-- A number whose words below `k` are zero is a multiple of `2^(64 k)`. -/
theorem low_zero {V : Nat} : ∀ k, (∀ j < k, V / 2 ^ (64 * j) % 2 ^ 64 = 0) → V % 2 ^ (64 * k) = 0
  | 0, _ => by rw [Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | k + 1, h => by
    rw [show 64 * (k + 1) = 64 * k + 64 by omega, Nat.pow_add, Nat.mod_mul, low_zero k fun j hj => h j (by omega),
      h k (by omega), Nat.mul_zero]

/-- The trailing zeros of `V`, from its lowest nonzero word, word `i₀`. -/
theorem tz_words {V i₀ : Nat} (hlow : V % 2 ^ (64 * i₀) = 0) (hy : V / 2 ^ (64 * i₀) % 2 ^ 64 ≠ 0) :
    tz V = 64 * i₀ + tz (V / 2 ^ (64 * i₀) % 2 ^ 64) := by
  generalize hQ : V / 2 ^ (64 * i₀) = Q at hy
  have hV : V = 2 ^ (64 * i₀) * Q := by rw [← hQ]; exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hlow)).symm
  have hV0 : V ≠ 0 := by intro e; rw [e] at hQ; rw [← hQ] at hy; simp at hy
  have hy0 := hy
  have tz_eq_of : ∀ {n T : Nat}, n ≠ 0 → (∀ s, 2 ^ s ∣ n ↔ s ≤ T) → tz n = T := fun h0 h =>
    Nat.le_antisymm ((h _).mp ((dvd_iff h0 _).mpr (Nat.le_refl _))) ((dvd_iff h0 _).mp ((h _).mpr (Nat.le_refl _)))
  refine tz_eq_of hV0 fun s => ?_
  by_cases hs : s ≤ 64 * i₀
  · constructor
    · intro _; omega
    · intro _; rw [hV]; exact Nat.dvd_trans (Nat.pow_dvd_pow 2 hs) (Nat.dvd_mul_right _ _)
  · obtain ⟨t, rfl⟩ : ∃ t, s = 64 * i₀ + t := ⟨s - 64 * i₀, by omega⟩
    rw [Nat.add_le_add_iff_left, ← dvd_iff hy0, hV, Nat.pow_add, Nat.mul_dvd_mul_iff_left (Nat.two_pow_pos _)]
    by_cases ht : t ≤ 64
    · rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero,
        Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 ht)]
    · constructor
      · intro d; exfalso
        have : 2 ^ 64 ∣ Q := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) d
        exact hy (Nat.mod_eq_zero_of_dvd this)
      · intro d; exfalso
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hy) d
        have : 2 ^ 64 < 2 ^ t := Nat.pow_lt_pow_right (by decide) (by omega)
        have := Nat.mod_lt Q (Nat.two_pow_pos 64)
        omega

/-- The trailing zeros of `a ∨ b`, for `a ≠ 0`, are those of `gcd(a, b)`. -/
theorem tz_or_gcd {a b : Nat} (ha : a ≠ 0) : tz (a ||| b) = tz (Nat.gcd a b) := by
  have hab : a ||| b ≠ 0 := fun e => ha (Nat.or_eq_zero_iff.mp e).1
  have hg : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha
  apply Nat.le_antisymm
  · rw [← dvd_iff hg, ← dvd_gcd_iff, Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
    have := (dvd_iff hab (tz (a ||| b))).mpr (Nat.le_refl _)
    rw [Nat.dvd_iff_mod_eq_zero, Nat.or_mod_two_pow, Nat.or_eq_zero_iff] at this
    exact this
  · rw [← dvd_iff hab, Nat.dvd_iff_mod_eq_zero, Nat.or_mod_two_pow, Nat.or_eq_zero_iff,
      ← Nat.dvd_iff_mod_eq_zero, ← Nat.dvd_iff_mod_eq_zero, dvd_gcd_iff, dvd_iff hg]

/-- `ctzOr A B sl`: the trailing zeros of `[A] ∨ [B]` (narrow, not zero) into slot `sl`. -/
theorem ctzOr_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I)
    {A Bj : Nat} (hA : A < 16) (hB : Bj < 16) {sl : Nat} (hsl : Own sl) :
    WP isa (ctzOr A Bj sl) s fun t => G I m₀ (vk I.k) c t ∧ Frm I.B (hdrW ++ [(8 * sl, 8)]) s.mem t.mem ∧
      word t.mem I.B (8 * sl) =
        BitVec.ofNat 64 (tz (wv s.mem I.B (slot (vk I.k) A) (vk I.k) ||| wv s.mem I.B (slot (vk I.k) Bj) (vk I.k))) ∧
      Keep (czRegs ++ ([.x7, .x11, .x12, .x15] : List Reg)) s t := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hv2 : 2 ≤ vk I.k := by simp only [vk]; omega
  have hvl : vk I.k < 200 := by simp only [vk]; omega
  have sA := hdr_lt_slot (vk I.k) A (i := 31) (by decide)
  have sB := hdr_lt_slot (vk I.k) Bj (i := 31) (by decide)
  unfold ctzOr
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (h.setNar_ok L) fun t₀ ⟨g₀, f₀, k₀⟩ => ?_
  have hn := g₀.ws.scr.nowrap
  have zA := g₀.ws.sl hA
  have zB := g₀.ws.sl hB
  refine WP.mono (ws_ok g₀.ws.scr g₀.ws.x0 g₀.ws.h256 g₀.ws.hw g₀.ws.hS) fun t₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  have x0₁ : t₁.gpr .x0 = I.B := (k₁.gpr .x0 (by decide)).trans g₀.ws.x0
  refine WP.mono (base_ok A .x16 x0₁ h11) fun t₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  refine WP.mono (base_ok Bj .x17 ((k₂.gpr .x0 (by decide)).trans x0₁) ((k₂.gpr .x11 (by decide)).trans h11))
    fun t₃ ⟨⟨h17, m₃, _⟩, k₃⟩ => ?_
  have h12₃ : t₃.gpr .x12 = BitVec.ofNat 64 (vk I.k) := by rw [k₃.gpr .x12 (by decide), k₂.gpr .x12 (by decide), h12]
  refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x14, .x15] (Q := fun t => t.gpr .x7 = 0 ∧ t.gpr .x15 = mask true ∧
      t.gpr .x5 = 0 ∧ t.gpr .x6 = mask false ∧ t.gpr .x8 = BitVec.ofNat 64 (64 * 0) ∧
      t.gpr .x14 = BitVec.ofNat 64 (vk I.k) ∧ t.mem = t₃.mem) (by brun [h12₃, mov, movi])
    (by decide) (by decide) (by decide +kernel)) fun t₄ ⟨⟨h7, h15, h5, h6, h8, h14, m₄⟩, k₄⟩ => ?_
  have h16₄ : t₄.gpr .x16 = off I.B (slot (vk I.k) A + 8 * 0) := by rw [k₄.gpr .x16 (by decide), k₃.gpr .x16 (by decide), h16]; rfl
  have h17₄ : t₄.gpr .x17 = off I.B (slot (vk I.k) Bj + 8 * 0) := by rw [k₄.gpr .x17 (by decide), h17]; rfl
  have g₄ : G I m₀ (vk I.k) c t₄ := g₀.same (by rw [m₄, m₃, m₂, m₁]) ((((k₁.trans k₂).trans k₃).trans k₄)) (by decide)
  refine WP.seq (WP.mono (wp_countdown (N := vk I.k) (by omega) (by omega)
    (CzI t₄ I.B (slot (vk I.k) A) (slot (vk I.k) Bj) (fun j => word t₄.mem I.B (slot (vk I.k) A + 8 * j) |||
      word t₄.mem I.B (slot (vk I.k) Bj + 8 * j)))
    (fun i hi t hI _ => czStep_ok g₄.ws.scr h7 h15 (by omega) (by omega) hi hI)
    ⟨Keep.refl _ _, rfl, h16₄, h17₄, h8, ⟨false, 0, h6, h5, fun j hj => absurd hj (Nat.not_lt_zero j)⟩⟩ h14)
    fun t₅ hI => ?_)
  obtain ⟨fd, j₀, _, h5₅, hS⟩ := hI.found
  have g₅ : G I m₀ (vk I.k) c t₅ := g₄.same hI.mem hI.keep (by decide)
  refine WP.mono (sthOwn_ok g₅ hsl .x5) fun t ⟨g, f, hw, k⟩ => ⟨g, ?_, ?_, ?_⟩
  · exact (((f₀.mono fun r hr => List.mem_append_left _ hr).trans (by
      rw [show t₅.mem = t₀.mem by rw [hI.mem, m₄, m₃, m₂, m₁]]; exact Frm.refl _ _ _)).trans
      (f.mono fun r hr => List.mem_append_right _ hr))
  · -- The value.
    have e₄ : ∀ d n, 256 ≤ d → d + 8 * n ≤ 2 ^ 64 → wv t₄.mem I.B d n = wv s.mem I.B d n := fun d n hd hd' => by
      rw [m₄, m₃, m₂, m₁, hdrW_wv f₀ hd hd']
    rw [← e₄ _ _ sA (by omega), ← e₄ _ _ sB (by omega)]
    generalize hVd : wv t₄.mem I.B (slot (vk I.k) A) (vk I.k) ||| wv t₄.mem I.B (slot (vk I.k) Bj) (vk I.k) = V
    have wf : ∀ j < vk I.k, (word t₄.mem I.B (slot (vk I.k) A + 8 * j) ||| word t₄.mem I.B (slot (vk I.k) Bj + 8 * j)).toNat =
        V / 2 ^ (64 * j) % 2 ^ 64 := fun j hj => by
      rw [← hVd, BitVec.toNat_or, Nat.or_div_two_pow, Nat.or_mod_two_pow, wv_word_at _ _ _ hj, wv_word_at _ _ _ hj]
    have hVl : V < 2 ^ (64 * vk I.k) := by
      rw [← hVd]; exact Nat.or_lt_two_pow (wv_lt _ _ _ _) (wv_lt _ _ _ _)
    rw [hw, h5₅]
    unfold ScanI at hS
    cases fd
    · simp only [Bool.false_eq_true, ↓reduceIte] at hS ⊢
      have := low_zero (V := V) (vk I.k) fun j hj => by rw [← wf j hj, hS j hj]; rfl
      rw [Nat.mod_eq_of_lt hVl] at this
      rw [this, tz]; simp
    simp only [↓reduceIte] at hS ⊢
    obtain ⟨hj₀, hy0, hlow⟩ := hS
    have hlowV : V % 2 ^ (64 * j₀) = 0 := low_zero j₀ fun j hj => by rw [← wf j (by omega), hlow j hj]; rfl
    have hyV := wf j₀ hj₀
    rw [tz_words hlowV (by rw [← hyV]; exact fun e => hy0 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))), ← hyV]
  · exact ((((((k₀.trans k₁).trans k₂).trans k₃).trans k₄).trans hI.keep).trans k).mono (by decide)

/-! ## The halvings -/

/-- A slot of the stages' own, kept by a store to another. -/
theorem own_word {B : Addr} {m m' : Mem} {sl' : Nat} (hf : Frm B (hdrW ++ [(8 * sl', 8)]) m m') {sl : Nat}
    (hsl : Own sl) (hne : sl ≠ sl') : word m' B (8 * sl) = word m B (8 * sl) := by
  obtain ⟨h1, h2, h3⟩ := hsl
  exact hf.word_eq (fun r hr => by
    simp only [hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl <;> simp only [sW, sArr, sStride, sFn] at h3 ⊢ <;> omega) (by omega)

/-- The probes the halvings keep: the words above `u` and `x`, `n` and one. -/
structure TwK (B : Addr) (v : Nat) (m m' : Mem) : Prop where
  zU : word m' B (slot v nU + 8 * v) = word m B (slot v nU + 8 * v)
  zX : word m' B (slot v nXn + 8 * v) = word m B (slot v nXn + 8 * v)
  n : wv m' B (slot v 0) v = wv m B (slot v 0) v
  one : wv m' B (slot v nOne) (v + 2) = wv m B (slot v nOne) (v + 2)

theorem TwK.trans {B : Addr} {v : Nat} {m₁ m₂ m₃ : Mem} (a : TwK B v m₁ m₂) (b : TwK B v m₂ m₃) : TwK B v m₁ m₃ :=
  ⟨b.zU.trans a.zU, b.zX.trans a.zX, b.n.trans a.n, b.one.trans a.one⟩

theorem TwK.of {B : Addr} {v : Nat} {m m' : Mem} {rs : List (Nat × Nat)} (F : Frm B (hdrW ++ rs) m m')
    (hb : slot v 32 ≤ 2 ^ 64)
    (hrs : ∀ r ∈ rs, ((slot v nU + 8 * v + 8 ≤ r.1 ∨ r.1 + r.2 ≤ slot v nU + 8 * v) ∧
      (slot v nXn + 8 * v + 8 ≤ r.1 ∨ r.1 + r.2 ≤ slot v nXn + 8 * v)) ∧
      (slot v 0 + 8 * v ≤ r.1 ∨ r.1 + r.2 ≤ slot v 0) ∧
      (slot v nOne + 8 * (v + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot v nOne)) : TwK B v m m' := by
  have s32 := slot_lt (w := v) (show nOne < 32 by decide)
  have s3 := slot_lt (w := v) (show nXn < 32 by decide)
  have s2 := slot_lt (w := v) (show nU < 32 by decide)
  have s0 := slot_lt (w := v) (show 0 < 32 by decide)
  exact ⟨Frm.hdr_word F (by have := slot_ge v nU; omega) (by omega) fun r hr => (hrs r hr).1.1,
    Frm.hdr_word F (by have := slot_ge v nXn; omega) (by omega) fun r hr => (hrs r hr).1.2,
    Frm.hdr_wv F (slot_ge _ _) (by omega) fun r hr => (hrs r hr).2.1,
    Frm.hdr_wv F (slot_ge _ _) (by omega) fun r hr => (hrs r hr).2.2⟩

/-- `twos`: the halvings in closed form, which are `64 v` of `twoStep`. -/
theorem twos_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I)
    {N X : Nat} (hN : wv s.mem I.B (slot (vk I.k) 0) (vk I.k) = N) (hN2 : 2 ≤ N)
    (hX : wv s.mem I.B (slot (Wk I.k) wX) (Wk I.k) = X) :
    WP isa twos s (TwI I m₀ c N (N - 1, X % 2 ^ (64 * vk I.k), X) (64 * vk I.k)) := by
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hk1 := L.k1
  have hk2 := L.k2
  have hv1 : 2 ≤ vk I.k := by simp only [vk]; omega
  have hb32 : slot (vk I.k) 32 ≤ 2 ^ 64 := by
    have := h.bndv L (j := 31) (k := vk I.k + 2) (by decide) (Nat.le_refl _)
    have : slot (vk I.k) 32 = _ := slot_succ (vk I.k) 31; omega
  have hb32' : 256 + 32 * (8 * (vk I.k + 2)) ≤ 2 ^ 64 := hb32
  have e : twos = seqs (([.block setNar] ++ oneA nOne ++ [zeroA nU, subA nU Public.aN nOne, zeroA nXn,
      copyA nXn (2 * wX)]) ++ ([ctzOr nU nXn sT1, ctzOr nU nU sT2] ++ (shiftBy nU false false sT2 ++
      (shiftBy nXn false false sT1 ++ (shiftBy wX true true sT1 ++ [.block setNar]))))) := by
    simp only [VG.Impl.Rsa.AArch64.RecoverDet.twos, List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  have hNlt : N < 2 ^ (64 * vk I.k) := by rw [← hN]; exact wv_lt _ _ _ _
  refine wp_seqs_append (by simp [oneA]) (by simp) (WP.mono (twosInit_ok h L hN (by omega) hX) fun t₀ I₀ => ?_)
  have v₀ := I₀.val
  simp only [Function.iterate_zero_apply, Prod.mk.injEq] at v₀
  obtain ⟨u₀, x₀, X₀⟩ := v₀
  generalize hx : X % 2 ^ (64 * vk I.k) = x at x₀
  have hu0 : 0 < N - 1 := by omega
  have hul : N - 1 < 2 ^ (64 * vk I.k) := by omega
  have hXl : X < 2 ^ (64 * Wk I.k) := by rw [← hX]; exact wv_lt _ _ _ _
  -- The trailing zeros.
  refine wp_seqs_append (by simp) (by simp [shiftBy]) ?_
  refine WP.seq (WP.mono (ctzOr_ok I₀.g L (A := nU) (Bj := nXn) (by decide) (by decide) (sl := sT1)
    ⟨by decide, by decide, by decide⟩) fun t₁ ⟨g₁, f₁, w₁, k₁⟩ => ?_)
  rw [u₀, x₀] at w₁
  have K₁ : TwK I.B (vk I.k) t₀.mem t₁.mem := TwK.of f₁ hb32 (by
    simp only [List.mem_singleton]; rintro r rfl
    simp only [slot, hdrBytes, sT1, sFn, nU, nXn, nOne]; omega)
  have e₁ : ∀ d n, 256 ≤ d → d + 8 * n ≤ 2 ^ 64 → wv t₁.mem I.B d n = wv t₀.mem I.B d n := fun d n hd hd' =>
    Frm.hdr_wv f₁ hd hd' (by simp only [List.mem_singleton]; rintro r rfl; simp only [sT1, sFn]; omega)
  have u₁ : wv t₁.mem I.B (slot (vk I.k) nU) (vk I.k) = N - 1 := by
    rw [e₁ _ _ (slot_ge _ _) (by simp only [slot, hdrBytes, nU]; omega), u₀]
  refine WP.mono (ctzOr_ok g₁ L (A := nU) (Bj := nU) (by decide) (by decide) (sl := sT2)
    ⟨by decide, by decide, by decide⟩) fun t₂ ⟨g₂, f₂, w₂, k₂⟩ => ?_
  rw [u₁, Nat.or_self] at w₂
  have K₂ : TwK I.B (vk I.k) t₁.mem t₂.mem := TwK.of f₂ hb32 (by
    simp only [List.mem_singleton]; rintro r rfl
    simp only [slot, hdrBytes, sT2, sFn, nU, nXn, nOne]; omega)
  have e₂ : ∀ d n, 256 ≤ d → d + 8 * n ≤ 2 ^ 64 → wv t₂.mem I.B d n = wv t₀.mem I.B d n := fun d n hd hd' => by
    rw [Frm.hdr_wv f₂ hd hd' (by simp only [List.mem_singleton]; rintro r rfl; simp only [sT2, sFn]; omega), e₁ d n hd hd']
  have w₂₁ : word t₂.mem I.B (8 * sT1) = BitVec.ofNat 64 (tz ((N - 1) ||| x)) := by
    rw [own_word f₂ ⟨by decide, by decide, by decide⟩ (by decide), w₁]
  -- The counts.
  have ht2 : tz (N - 1) < 64 * vk I.k := ShiftStages.tz_lt hu0 hul
  have ht1 : tz ((N - 1) ||| x) ≤ tz (N - 1) := by
    rw [tz_or_gcd (by omega)]
    exact (dvd_iff (by omega) _).mp (Nat.dvd_trans ((dvd_iff (Nat.gcd_ne_zero_left (by omega)) _).mpr
      (Nat.le_refl _)) (Nat.gcd_dvd_left _ _))
  have sep : ∀ d n a b, d + 8 * n ≤ a ∨ a + b ≤ d → ∀ r ∈ [(a, b)], d + 8 * n ≤ r.1 ∨ r.1 + r.2 ≤ d := by
    intro d n a b h r hr; rw [List.mem_singleton.mp hr]; exact h
  -- `u := u / 2^t₂`.
  refine wp_seqs_append (by simp [shiftBy]) (by simp [shiftBy]) (WP.mono (shiftBy_ok g₂ L false false (j := nU)
    (by decide) (sl := sT2) (by decide) (by decide) (by decide) w₂ (N := vk I.k) rfl ht2) fun t₃ ⟨g₃, f₃, v₃, k₃⟩ => ?_)
  have K₃ : TwK I.B (vk I.k) t₂.mem t₃.mem := TwK.of f₃ hb32 (by
    simp only [List.mem_singleton]; rintro r rfl
    simp only [slot, hdrBytes, nU, nXn, nOne]; omega)
  -- `x := x / 2^t₁`.
  have w₃₁ : word t₃.mem I.B (8 * sT1) = BitVec.ofNat 64 (tz ((N - 1) ||| x)) := by
    rw [stage_word f₃ (by decide) (by decide) (by decide), w₂₁]
  refine wp_seqs_append (by simp [shiftBy]) (by simp [shiftBy]) (WP.mono (shiftBy_ok g₃ L false false (j := nXn)
    (by decide) (sl := sT1) (by decide) (by decide) (by decide) w₃₁ (N := vk I.k) rfl (by omega))
    fun t₄ ⟨g₄, f₄, v₄, k₄⟩ => ?_)
  have K₄ : TwK I.B (vk I.k) t₃.mem t₄.mem := TwK.of f₄ hb32 (by
    simp only [List.mem_singleton]; rintro r rfl
    simp only [slot, hdrBytes, nU, nXn, nOne]; omega)
  -- `X := X 2^t₁`.
  have w₄₁ : word t₄.mem I.B (8 * sT1) = BitVec.ofNat 64 (tz ((N - 1) ||| x)) := by
    rw [stage_word f₄ (by decide) (by decide) (by decide), w₃₁]
  refine wp_seqs_append (by simp [shiftBy]) (by simp) (WP.mono (shiftBy_ok g₄ L true true (j := wX)
    (by decide) (sl := sT1) (by decide) (by decide) (by decide) w₄₁ (N := Wk I.k) rfl (by omega))
    fun t₅ ⟨g₅, f₅, v₅, k₅⟩ => ?_)
  have K₅ : TwK I.B (vk I.k) t₄.mem t₅.mem := TwK.of f₅ hb32 (by
    simp only [List.mem_singleton]; rintro r rfl
    simp only [slot, hdrBytes, nU, nXn, nOne, wX, Wk]; omega)
  refine WP.mono (g₅.setNar_ok L) fun t ⟨g, f, _⟩ => ?_
  have K₆ : TwK I.B (vk I.k) t₅.mem t.mem := TwK.of (rs := []) (by simpa using f) hb32 (by simp)
  have K := ((((((K₁.trans K₂).trans K₃).trans K₄).trans K₅).trans K₆))
  -- The values.
  have bU : slot (vk I.k) nU + 8 * vk I.k ≤ 2 ^ 64 := by simp only [slot, hdrBytes, nU] at hb32' ⊢; omega
  have bX : slot (vk I.k) nXn + 8 * vk I.k ≤ 2 ^ 64 := by simp only [slot, hdrBytes, nXn] at hb32' ⊢; omega
  have bW : slot (Wk I.k) wX + 8 * Wk I.k ≤ 2 ^ 64 := by
    have := g₅.bndW L (j := wX) (k := Wk I.k) (by decide) (by omega); omega
  have vU : wv t.mem I.B (slot (vk I.k) nU) (vk I.k) = (N - 1) / 2 ^ tz (N - 1) := by
    rw [Frm.hdrW_wv f (slot_ge _ _) bU,
      Frm.hdr_wv f₅ (slot_ge _ _) bU (sep _ _ _ _ (by simp only [slot, hdrBytes, nU, wX, Wk]; omega)),
      Frm.hdr_wv f₄ (slot_ge _ _) bU (sep _ _ _ _ (by simp only [slot, hdrBytes, nU, nXn]; omega)), v₃,
      e₂ _ _ (slot_ge _ _) bU, u₀]
    rfl
  have vX : wv t.mem I.B (slot (vk I.k) nXn) (vk I.k) = x / 2 ^ tz ((N - 1) ||| x) := by
    rw [Frm.hdrW_wv f (slot_ge _ _) bX,
      Frm.hdr_wv f₅ (slot_ge _ _) bX (sep _ _ _ _ (by simp only [slot, hdrBytes, nXn, wX, Wk]; omega)), v₄,
      Frm.hdr_wv f₃ (slot_ge _ _) bX (sep _ _ _ _ (by simp only [slot, hdrBytes, nU, nXn]; omega)),
      e₂ _ _ (slot_ge _ _) bX, x₀]
    rfl
  have vW : wv t.mem I.B (slot (Wk I.k) wX) (Wk I.k) = X * 2 ^ tz ((N - 1) ||| x) % 2 ^ (64 * Wk I.k) := by
    rw [Frm.hdrW_wv f (slot_ge _ _) bW, v₅,
      Frm.hdr_wv f₄ (slot_ge _ _) bW (sep _ _ _ _ (by simp only [slot, hdrBytes, nXn, wX, Wk]; omega)),
      Frm.hdr_wv f₃ (slot_ge _ _) bW (sep _ _ _ _ (by simp only [slot, hdrBytes, nU, wX, Wk]; omega)),
      e₂ _ _ (slot_ge _ _) bW, X₀]
    rfl
  refine ⟨g, ?_, K.zU.trans I₀.zU, K.zX.trans I₀.zX, K.n.trans I₀.n, K.one.trans I₀.one⟩
  rw [vU, vX, vW, twos_closed hu0 hul hXl, tz_or_gcd (by omega)]

end VG.Proof.Rsa.AArch64.Rd
