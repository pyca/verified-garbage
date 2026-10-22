module

import VerifiedGarbage.Proof.MlKem.AArch64.NttR.ModelI
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Model
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Gs
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Rows
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.MlKem.Ntt
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sound
public import VerifiedGarbage.Proof.MlKem.NttLayer

/-!
# ML-KEM on AArch64: the scheduled inverse NTT halfword by halfword, its coefficients

The coefficients after each level of `NTT⁻¹` as mlkem-native schedules it
(`Lfi`: the multiplication by 3303 first, then its seven Gentleman–Sande
layers, some sums reduced), as `vg_mlkem16_inv_ntt`
(`Impl/MlKem/AArch64/Ntt16/FastInv.lean`) computes them from the input's `W`,
obey the operations the machine collapses (`modelFI`), represent those of
`NTT⁻¹` times 3303 (`Lfi_rep`), and their reductions (`Ofi`) are the
coefficients of `NTT⁻¹` (`Ofi_nttInv`).

Most sums are not reduced, so the coefficients grow to nearly `2¹⁵`: their
bounds are tighter than `q` where a reduction leaves them about `q / 2`
(`mmW_tight`), and depend on the coefficient (`bF`, a table of each level's
bounds checked against the levels by `decide`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Proof.MlKem.AArch64.Ntt16 (LRep gs_lane ofNat_zeta tw_lt tw_def)

/-- The zeta `q - ζ` that level `st` multiplies the difference at `p` by. -/
def zf (st p : Nat) : Nat := qN - zetaN (256 / fLen st - 1 - p / (2 * fLen st))

/-- The coefficients after `st` levels of the scheduled `NTT⁻¹`, from the input's `W`. -/
def Lfi (W : Nat → BitVec 16) : Nat → Nat → BitVec 16
  | 0, p => W p
  | 1, p => mmW (W p) 3303 (twN 3303)
  | st + 2, p =>
    if p % (2 * fLen (st + 1)) < fLen (st + 1) then
      if fRed (st + 1) p = true then n1W (Lfi W (st + 1) p + Lfi W (st + 1) (p + fLen (st + 1)))
      else Lfi W (st + 1) p + Lfi W (st + 1) (p + fLen (st + 1))
    else mmW (Lfi W (st + 1) (p - fLen (st + 1)) - Lfi W (st + 1) p) (zf (st + 1) p) (twN (zf (st + 1) p))

/-- The reduced coefficients after the eight levels. -/
def Ofi (W : Nat → BitVec 16) (p : Nat) : BitVec 16 := normW (Lfi W fastInvRules.layers p)

theorem Lfi_succ (W : Nat → BitVec 16) {st : Nat} (hs : 1 ≤ st) (p : Nat) : Lfi W (st + 1) p =
    if p % (2 * fLen st) < fLen st then
      if fRed st p = true then n1W (Lfi W st p + Lfi W st (p + fLen st)) else Lfi W st p + Lfi W st (p + fLen st)
    else mmW (Lfi W st (p - fLen st) - Lfi W st p) (zf st p) (twN (zf st p)) := by
  obtain ⟨k, rfl⟩ : ∃ k, st = k + 1 := ⟨st - 1, by omega⟩
  rfl

theorem fPair_iff {st p p' : Nat} (h : fPair st p p' = true) :
    1 ≤ st ∧ st ≤ 7 ∧ p' = p + fLen st ∧ p % (2 * fLen st) < fLen st ∧ p' < 256 := by
  unfold fPair at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem fLen_pos (st : Nat) : 0 < fLen st := by
  rw [fLen, Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.two_pow_pos st

theorem modelFI (W : Nat → BitVec 16) : Model (Lfi W) (Ofi W) fastInvRules := by
  refine ⟨by decide, fun _ h => absurd h (by decide), fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun p _ => rfl,
    fun _ => rfl, fun _ p => rfl, fun _ st p p' hg hr => ?_, fun _ st p p' hg hr => ?_,
    fun _ st p p' z t hg hz => ?_⟩
  · obtain ⟨h1, -, rfl, hm, -⟩ := fPair_iff hg
    rw [Lfi_succ W h1, ite_eq_left hm, ite_eq_right (by rw [hr]; exact Bool.false_ne_true)]
  · obtain ⟨h1, -, rfl, hm, -⟩ := fPair_iff hg
    rw [Lfi_succ W h1, ite_eq_left hm, ite_eq_left hr]
  · obtain ⟨h1, h7, rfl, hm, -⟩ := fPair_iff hg
    unfold fZeta at hz
    simp only [Bool.and_eq_true, Nat.beq_eq] at hz
    obtain ⟨rfl, rfl⟩ := hz
    have hpos := fLen_pos st
    rw [Lfi_succ W h1]
    unfold zf
    generalize fLen st = len at hpos hm ⊢
    have h1 : (p + len) % (2 * len) = p % (2 * len) + len := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show len < 2 * len by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [ite_eq_right (by omega), Nat.add_sub_cancel]

/-! ## Tight bounds of the products -/

/-- How far `tw z · 2q` is from `z · 2¹⁶`. -/
def dz (z : Nat) : Nat := ((z : Int) * 65536 - 6658 * (Impl.MlKem.AArch64.Ntt16.tw z : Int)).natAbs

/-- The bound of `a · z mod q`, as the code computes it, for `|a| < M`. -/
def mmB (M z : Nat) : Nat := (32768 * 3329 + (M - 1) * dz z) / 65536 + 1

/-- The integer core, with the bound of `A`: with `C = tw z` and
`T = ⌊(2AC + 2¹⁵) / 2¹⁶⌋`, `|A z - T q| < mmB M z`. -/
theorem core_tight {A : Int} {z M : Nat} (hA : -(M : Int) < A) (hA' : A < M) :
    -(mmB M z : Int) < A * z - (2 * A * (((z : Int) * 65536 + 3329) / 6658) + 32768) / 65536 * 3329 ∧
    A * z - (2 * A * (((z : Int) * 65536 + 3329) / 6658) + 32768) / 65536 * 3329 < mmB M z := by
  have hdz : (dz z : Int) = ((z : Int) * 65536 - 6658 * (((z : Int) * 65536 + 3329) / 6658)).natAbs := by
    rw [dz, tw_def]
  unfold mmB
  generalize hC : ((z : Int) * 65536 + 3329) / 6658 = C at hdz ⊢
  generalize hd : (z : Int) * 65536 - 6658 * C = d at hdz
  have hn : (A * d).natAbs ≤ (M - 1) * dz z := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (by omega) (by omega)
  generalize hE : (M - 1) * dz z = E at hn ⊢
  have hQ1 : A * d ≤ E := by omega
  have hQ2 : -(E : Int) ≤ A * d := by omega
  have hX : A * z * 65536 = 6658 * (A * C) + A * d := by rw [← hd]; grind
  have h2 : 2 * A * C = 2 * (A * C) := by grind
  rw [h2]
  generalize A * C = P at hX
  generalize A * d = Q at hQ1 hQ2 hX
  generalize A * (z : Int) = X at hX ⊢
  omega

/-- `mm_ok` with the bound of the factor: `r = a · z - t · q` is less than
`mmB M z` in absolute value for `|a| < M`. -/
theorem mm_tight (a : BitVec 16) {z M : Nat} (ha : -(M : Int) < a.toInt) (ha' : a.toInt < M) (hM : M ≤ 32768)
    (hz : z < 3329) :
    ∃ t, sqdmulhHLane true a (BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.tw z)) = some t ∧
      -(mmB M z : Int) < (a * BitVec.ofNat 16 z - t * BitVec.ofNat 16 3329).toInt ∧
      (a * BitVec.ofNat 16 z - t * BitVec.ofNat 16 3329).toInt < mmB M z ∧
      ((a * BitVec.ofNat 16 z - t * BitVec.ofNat 16 3329).toInt - a.toInt * z) % 3329 = 0 := by
  obtain ⟨t, ht, -, -, h3⟩ := Ntt16.mm_ok a (z := z) (by omega) hz
  refine ⟨t, ht, ?_⟩
  have htw := tw_lt hz
  have hc : (BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.tw z)).toInt = Impl.MlKem.AArch64.Ntt16.tw z := by
    rw [BitVec.toInt_ofNat']; simp only [Int.bmod_def]; omega
  have hzt : (BitVec.ofNat 16 z).toInt = z := by
    rw [BitVec.toInt_ofNat']; simp only [Int.bmod_def]; omega
  have hq : (BitVec.ofNat 16 3329).toInt = 3329 := by decide
  have hne : ¬ (a = 0x8000#16 ∧ BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.tw z) = 0x8000#16) := by
    rintro ⟨-, h⟩
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this; omega
  have et : t = _ := Option.some.inj (ht.symm.trans (by simp only [sqdmulhHLane, hne, ite_false]; rfl))
  subst et
  refine ⟨?_, ?_, h3⟩ <;>
  · have h := core_tight (A := a.toInt) (z := z) ha ha'
    have hmb : mmB M z ≤ 32768 := by
      unfold mmB
      have : dz z ≤ 3329 := by
        have := tw_def z
        unfold dz; omega
      have : (M - 1) * dz z ≤ 32767 * 3329 := Nat.mul_le_mul (by omega) this
      omega
    simp only [BitVec.toInt_sub, BitVec.toInt_mul, BitVec.toInt_ofInt, hc, hzt, hq, tw_def]
    rw [Int.shiftRight_eq_div_pow]
    simp only [ite_true, show (2 : Int) ^ 15 = 32768 from rfl]
    generalize (2 * a.toInt * (((z : Int) * 65536 + 3329) / 6658) + 32768) / 65536 = T at *
    generalize a.toInt * (z : Int) = X at *
    simp only [Int.bmod_def]
    omega

/-- A lane times `z`, modulo `q`, with the bound of the lane. -/
theorem mmW_tight {a : BitVec 16} {X : Zq} {M z : Nat} (h : LRep a X M) (hM : M ≤ 32768) (hz : z < 3329) :
    LRep (mmW a z (twN z)) (X * ofNat z) (mmB M z) := by
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨T, hT, b1, b2, b3⟩ := mm_tight a (z := z) a1 a2 hM hz
  rw [mmW_eq hT]
  refine ⟨b1, b2, ?_⟩
  have e : (X * ofNat z).val = X.val * z % 3329 := by
    rw [val_mul, val_ofNat, Nat.mod_eq_of_lt (show z < q from hz)]
  rw [e]
  generalize a * BitVec.ofNat 16 z - T * BitVec.ofNat 16 3329 = r at b1 b2 b3 ⊢
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero a3
  have : a.toInt * z = X.val * z + 3329 * (k * z) := by rw [show a.toInt = X.val + 3329 * k by omega]; grind
  rw [this] at b3
  generalize a.toInt * z = A at b3
  generalize k * (z : Int) = K at b3
  omega

/-- A lane reduced, with the bound of the lane. -/
theorem n1W_tight {a : BitVec 16} {X : Zq} {M : Nat} (h : LRep a X M) (hM : M ≤ 32768) :
    LRep (n1W a) X (mmB M 1) := by
  have e : n1W a = mmW a 1 (twN 1) := by
    unfold n1W mmW
    rw [BitVec.mul_one]
    rfl
  have h1 : X * ofNat 1 = X := by
    apply Fin.ext
    rw [val_mul, val_ofNat, Nat.mod_eq_of_lt (show 1 < q by decide), Nat.mul_one, Nat.mod_eq_of_lt X.isLt]
  rw [e, ← h1]
  exact mmW_tight h hM (by decide)

/-! ## The bounds of the coefficients -/

/-- The bounds after each level, for each class `cl` of coefficients. -/
def bT : List (List Nat) :=
  [[3329], [1691], [3382, 3329], [6764, 6658, 3329], [1880, 1877, 1771, 3329],
    [3760, 3754, 3542, 1771, 3329], [7520, 7508, 7084, 3542, 6658, 3329],
    [15040, 15016, 14168, 7084, 13316, 6658, 3329],
    [30080, 30032, 28336, 14168, 26632, 13316, 6658, 3329]]

/-- The highest bit set in `x < 256`, `0` for `0` and `1`. -/
def cl (x : Nat) : Nat :=
  if x < 2 then 0 else if x < 4 then 1 else if x < 8 then 2 else if x < 16 then 3
  else if x < 32 then 4 else if x < 64 then 5 else if x < 128 then 6 else 7

/-- The bound of coefficient `p` after level `st`: that of the class of `p mod 2^st`. -/
def bF (st p : Nat) : Nat := (bT.getD st []).getD (cl (p % 2 ^ st)) 0

theorem bF_ends : (∀ p < 256, bF 0 p = 3329 ∧ mmB 3329 3303 ≤ bF 1 p ∧ bF 8 p ≤ 32768) := by decide +kernel

/-- The sums of each level fit, and their bounds (reduced or not) are those
of the next level. -/
theorem bF_sum : ∀ st < 7, ∀ p < 256, p % (2 * fLen (st + 1)) < fLen (st + 1) →
    p + fLen (st + 1) < 256 ∧ bF (st + 1) p + bF (st + 1) (p + fLen (st + 1)) ≤ 32768 ∧
    (if fRed (st + 1) p = true then mmB (bF (st + 1) p + bF (st + 1) (p + fLen (st + 1))) 1
      else bF (st + 1) p + bF (st + 1) (p + fLen (st + 1))) ≤ bF (st + 2) p := by decide +kernel

/-- The differences of each level fit, their zetas are those of `NTT⁻¹`, and
their products are less than `q`. -/
theorem bF_dif : ∀ st < 7, ∀ p < 256, ¬ p % (2 * fLen (st + 1)) < fLen (st + 1) →
    fLen (st + 1) ≤ p ∧ bF (st + 1) p + bF (st + 1) (p - fLen (st + 1)) ≤ 32768 ∧ 3329 ≤ bF (st + 2) p ∧
    256 / fLen (st + 1) - 1 - p / (2 * fLen (st + 1)) < 128 ∧
    0 < zetaN (256 / fLen (st + 1) - 1 - p / (2 * fLen (st + 1))) ∧
    zetaN (256 / fLen (st + 1) - 1 - p / (2 * fLen (st + 1))) < 3329 := by decide +kernel

theorem fLen_eq : ∀ st < 7, fLen (st + 1) = 2 <<< st := by decide +kernel

/-! ## The coefficients represent `NTT⁻¹`'s -/

/-- Coefficient `p` of `NTT⁻¹` of `F` after level `st`, times 3303 after the first. -/
def vFi (F : Poly) (st p : Nat) : Zq := if st = 0 then F[p]! else (nttInvL (st - 1) F)[p]! * 3303

theorem vFi_succ (F : Poly) (st p : Nat) : vFi F (st + 1) p = (nttInvL st F)[p]! * 3303 := by
  rw [vFi, ite_eq_right (Nat.succ_ne_zero st)]
  rfl

theorem ofNat_q_sub {x : Nat} (h : x < 3329) : ofNat (3329 - x) = -ofNat x := by
  have e : ofNat (3329 - x) + ofNat x = 0 := by
    rw [← ofNat_add, Nat.sub_add_cancel (Nat.le_of_lt h)]
    rfl
  grind

/-- The coefficients after `st` levels represent those of `NTT⁻¹` (times 3303). -/
theorem Lfi_rep (W : Nat → BitVec 16) (F : Poly) (h : ∀ p < 256, LRep (W p) F[p]! 3329) :
    ∀ st ≤ 8, ∀ p < 256, LRep (Lfi W st p) (vFi F st p) (bF st p)
  | 0, _, p, hp => by
    rw [(bF_ends p hp).1]
    exact h p hp
  | 1, _, p, hp => by
    rw [vFi_succ]
    exact (mmW_tight (h p hp) (by decide) (by decide)).mono (bF_ends p hp).2.1
  | st + 2, hs, p, hp => by
    have ih := Lfi_rep W F h (st + 1) (by omega)
    rw [Lfi_succ W (by omega), vFi_succ, nttInvL_succ_get F (show st < 7 by omega) hp, ← fLen_eq st (by omega)]
    simp only [vFi_succ] at ih
    by_cases hm : p % (2 * fLen (st + 1)) < fLen (st + 1)
    · obtain ⟨hp', hB, hn⟩ := bF_sum st (by omega) p hp hm
      rw [ite_eq_left hm, ite_eq_left hm]
      obtain ⟨_, _, l1, -⟩ := gs_lane (z := 0) (ih p hp) (ih _ hp') (by decide) hB
      have e : ((nttInvL st F)[p]! + (nttInvL st F)[p + fLen (st + 1)]!) * 3303 =
          (nttInvL st F)[p]! * 3303 + (nttInvL st F)[p + fLen (st + 1)]! * 3303 := by grind
      rw [e]
      by_cases hr : fRed (st + 1) p = true
      · rw [ite_eq_left hr] at hn ⊢
        exact (n1W_tight l1 hB).mono hn
      · rw [ite_eq_right hr] at hn ⊢
        exact l1.mono hn
    · obtain ⟨hl, hB, hn, hk, hz0, hz⟩ := bF_dif st (by omega) p hp hm
      rw [ite_eq_right hm, ite_eq_right hm]
      obtain ⟨T, hT, -, l2⟩ := gs_lane (z := zf (st + 1) p) (ih p hp) (ih (p - fLen (st + 1)) (by omega))
        (by unfold zf qN; omega) hB
      rw [mmW_eq hT]
      have e : zeta (256 / fLen (st + 1) - 1 - p / (2 * fLen (st + 1))) *
          ((nttInvL st F)[p]! - (nttInvL st F)[p - fLen (st + 1)]!) * 3303 =
          ofNat (zf (st + 1) p) * ((nttInvL st F)[p - fLen (st + 1)]! * 3303 - (nttInvL st F)[p]! * 3303) := by
        unfold zf qN
        rw [ofNat_q_sub hz, show zetaN (256 / fLen (st + 1) - 1 - p / (2 * fLen (st + 1))) =
          Impl.MlKem.AArch64.Ntt16.zeta (256 / fLen (st + 1) - 1 - p / (2 * fLen (st + 1))) from rfl,
          ofNat_zeta hk]
        grind
      rw [e]
      exact l2.mono hn

/-- The reduced coefficients are those of `NTT⁻¹`. -/
theorem Ofi_nttInv (W : Nat → BitVec 16) (F : Poly) (h : ∀ p < 256, LRep (W p) F[p]! 3329) {p : Nat}
    (hp : p < 256) : (Ofi W p).toNat = ((nttInv F)[p]!).val := by
  rw [nttInv_eq_nttInvL, map_mul_get _ (show p < n from hp), ← vFi_succ]
  exact normL_val (n1W_rep (Lfi_rep W F h 8 (by decide) p hp) (bF_ends p hp).2.2)

end VG.Proof.MlKem.AArch64.NttR
