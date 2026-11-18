module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.MlKem.Ntt
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sound
public import VerifiedGarbage.Proof.MlKem.NttLayer
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint

/-! ### `MlKem.AArch64.NttR.ModelI`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.NttR.Model`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Ntt16.Idx`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Ntt16.Rows`, which this module and modules that import it used -/

section

/-!
# ML-KEM's 16-bit NTT on AArch64: its zetas

The zetas of the 16-bit NTT's table are those of the standard
(`ofNat_zeta`), each less than `q` (`zeta_lt`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

/-! ## Zetas -/

theorem ofNat_zeta {k : Nat} (hk : k < 128) : ofNat (Impl.MlKem.AArch64.Ntt16.zeta k) = VG.Proof.MlKem.zeta k := by
  rw [VG.Proof.MlKem.zeta_eq hk, Impl.MlKem.AArch64.Ntt16.zeta, zetaTable_eq]

theorem zeta_lt {k : Nat} (hk : k < 128) : Impl.MlKem.AArch64.Ntt16.zeta k < 3329 := by
  have := zetaTable_lt k hk
  exact this

end VG.Proof.MlKem.AArch64.Ntt16

end

end

/-!
# ML-KEM's 16-bit NTT on AArch64: lanes reduced to `[0, q)`

A lane less than `q` in absolute value made nonnegative (`nonneg_lane`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

/-! ## Reduction to `[0, q)` -/

/-- A lane less than `q` in absolute value made nonnegative: `r + (r >> 15 & q)`. -/
theorem nonneg_lane {r : BitVec 16} (h1 : -3329 < r.toInt) (h2 : r.toInt < 3329) :
    (r + (r.sshiftRight 15 &&& BitVec.ofNat 16 3329)).toInt =
      if r.toInt < 0 then r.toInt + 3329 else r.toInt := by
  rw [BitVec.sshiftRight_eq, Int.shiftRight_eq_div_pow]
  by_cases h : r.toInt < 0
  · rw [show r.toInt / ((2 ^ 15 : Nat) : Int) = -1 by omega_arith, ite_eq_left h,
      show BitVec.ofInt 16 (-1) &&& BitVec.ofNat 16 3329 = BitVec.ofNat 16 3329 by decide,
      BitVec.toInt_add]
    simp only [Int.bmod_def, show (BitVec.ofNat 16 3329).toInt = 3329 by decide]
    split <;> omega_arith
  · rw [show r.toInt / ((2 ^ 15 : Nat) : Int) = 0 by omega_arith, ite_eq_right h,
      show BitVec.ofInt 16 0 &&& BitVec.ofNat 16 3329 = 0#16 by decide, BitVec.add_zero]

end VG.Proof.MlKem.AArch64.Ntt16

end

end

/-!
# ML-KEM on AArch64: the NTT halfword by halfword, its coefficients

The coefficients after `st` layers (`Lf`), as the 16-bit NTT
(`Impl/MlKem/AArch64/Ntt16.lean`) computes them from the input's `W`, obey the
butterflies the machine collapses (`model`), represent those of `NTT`
within `(st + 1) q` (`Lf_rep`), and their reductions (`Of`) are the
coefficients of `NTT` (`Of_ntt`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Proof.MlKem.AArch64.Ntt16 (LRep bf_lane mm_ok ofNat_zeta zeta_lt nonneg_lane)

/-- The zeta of the block of `p` in the layer at distance `len`. -/
def zk (len p : Nat) : Nat := Impl.MlKem.AArch64.Ntt16.zeta (128 / len + p / (2 * len))

/-- The coefficients after `st` layers, from the input's `W`. -/
def Lf (W : Nat → BitVec 16) : Nat → Nat → BitVec 16
  | 0, p => W p
  | st + 1, p =>
    let len := 128 >>> st
    if p % (2 * len) < len then Lf W st p + mmW (Lf W st (p + len)) (zk len p) (twN (zk len p))
    else Lf W st (p - len) - mmW (Lf W st p) (zk len (p - len)) (twN (zk len (p - len)))

/-- The reduced coefficients after the seven layers. -/
def Of (W : Nat → BitVec 16) (p : Nat) : BitVec 16 := normW (Lf W 7 p)

theorem Lf_succ (W : Nat → BitVec 16) (st p : Nat) : Lf W (st + 1) p =
    if p % (2 * (128 >>> st)) < 128 >>> st then
      Lf W st p + mmW (Lf W st (p + (128 >>> st))) (zk (128 >>> st) p) (twN (zk (128 >>> st) p))
    else Lf W st (p - (128 >>> st)) - mmW (Lf W st p) (zk (128 >>> st) (p - (128 >>> st)))
      (twN (zk (128 >>> st) (p - (128 >>> st)))) := rfl

theorem div_sub_len {p len : Nat} (hpos : 0 < len) (hm : ¬ p % (2 * len) < len) :
    (p - len) / (2 * len) = p / (2 * len) := by
  have h1 := Nat.div_add_mod p (2 * len)
  have h3 := Nat.mod_lt p (show 0 < 2 * len by omega_using [hpos])
  apply Nat.div_eq_of_lt_le
  · rw [Nat.mul_comm]
    generalize 2 * len * (p / (2 * len)) = M at h1 ⊢
    omega_using [hm, h1]
  · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    generalize 2 * len * (p / (2 * len)) = M at h1 ⊢
    omega_using [h3, h1]

theorem model (W : Nat → BitVec 16) : Model (Lf W) (Of W) fwdRules := by
  refine ⟨by decide, fun _ _ st p p' z t hb => ?_, nofun, nofun, nofun, nofun, fun p _ => rfl, nofun, nofun,
    nofun, nofun, nofun⟩
  unfold bflyOk fwdRules at hb
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hb
  obtain ⟨⟨⟨⟨⟨hst, rfl⟩, hm⟩, -⟩, rfl⟩, rfl⟩ := hb
  have hpos : 0 < 128 >>> st := by
    rcases (by omega_using [hst] : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨?_, ?_⟩
  · rw [Lf_succ, ite_eq_left hm]; rfl
  · have h1 : (p + (128 >>> st)) % (2 * (128 >>> st)) = p % (2 * (128 >>> st)) + (128 >>> st) := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 128 >>> st < 2 * (128 >>> st) by omega_using [hm])]
      exact Nat.mod_eq_of_lt (by omega_using [hm])
    rw [Lf_succ, ite_eq_right (by omega_using [h1]), Nat.add_sub_cancel]
    rfl

/-! ## The coefficients represent `NTT`'s -/

theorem lens_get {st : Nat} (h : st < 7) :
    0 < 128 >>> st ∧ 2 * (128 >>> st) * (128 / (128 >>> st)) = 256 ∧ 128 / (128 >>> st) + 255 / (2 * (128 >>> st)) < 128 := by
  rcases (by omega_using [h] : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem mmW_eq {b : BitVec 16} {z : Nat} {T : BitVec 16}
    (h : sqdmulhHLane true b (BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.tw z)) = some T) :
    mmW b z (twN z) = b * BitVec.ofNat 16 z - T * BitVec.ofNat 16 3329 := by
  unfold mmW qdW; rw [h]; rfl

theorem pair_lt {p len K : Nat} (hpos : 0 < len) (hp : p < 2 * len * K) (hm : p % (2 * len) < len) :
    p + len < 2 * len * K := by
  have h1 := Nat.div_add_mod p (2 * len)
  have hq : p / (2 * len) < K := (Nat.div_lt_iff_lt_mul (by omega_using [hpos])).2 (by rw [Nat.mul_comm]; exact hp)
  have h2 : 2 * len * (p / (2 * len) + 1) ≤ 2 * len * K := Nat.mul_le_mul_left _ hq
  rw [Nat.mul_add, Nat.mul_one] at h2
  generalize 2 * len * (p / (2 * len)) = M at h1 h2
  omega_using [hm, h1, h2]

/-- The coefficients after `st` layers represent those of `NTT` after `st` layers. -/
theorem Lf_rep (W : Nat → BitVec 16) (F : Poly) (h : ∀ p < 256, LRep (W p) F[p]! 3329) :
    ∀ st ≤ 7, ∀ p < 256, LRep (Lf W st p) (nttL st F)[p]! ((st + 1) * 3329)
  | 0, _, p, hp => by simp only [Lf, nttL_zero]; exact (h p hp).mono (by omega_using [])
  | st + 1, hs, p, hp => by
    have ih := Lf_rep W F h st (by omega_using [hs])
    obtain ⟨hpos, hl, hz⟩ := lens_get (st := st) (by omega_using [hs])
    rw [nttL_succ F (by omega_using [hs]), nttLayer_get _ hpos hl hp, Lf_succ]
    generalize 128 >>> st = len at hpos hl hz
    have hdiv : p / (2 * len) ≤ 255 / (2 * len) := Nat.div_le_div_right (show p ≤ 255 by omega_using [hp])
    have hk : 128 / len + p / (2 * len) < 128 := by omega_using [hz, hdiv]
    rw [show (st + 1 + 1) * 3329 = (st + 1) * 3329 + 3329 by omega_using []]
    by_cases hm : p % (2 * len) < len
    · rw [ite_eq_left hm, ite_eq_left hm]
      obtain ⟨T, hT, l1, -⟩ := bf_lane (ih p hp) (ih (p + len) (by have := pair_lt hpos (show p < 2 * len * (128 / len) by omega_using [hp, hl]) hm; omega_using [hl, this])) (zeta_lt hk) (by omega_using [hs]) (by omega_using [hs])
      unfold zk
      rw [mmW_eq hT, ← ofNat_zeta hk]
      exact l1
    · rw [ite_eq_right hm, ite_eq_right hm]
      obtain ⟨T, hT, -, l2⟩ := bf_lane (ih (p - len) (by omega_using [hp])) (ih p hp) (zeta_lt hk) (by omega_using [hs]) (by omega_using [hs])
      unfold zk
      rw [div_sub_len hpos hm, mmW_eq hT, ← ofNat_zeta hk]
      exact l2

/-- A coefficient less than `2¹⁵` in absolute value, reduced to `[0, q)`. -/
theorem normW_val {x : BitVec 16} {X : Zq} {B : Nat} (h : LRep x X B) (hB : B ≤ 32768) :
    (normW x).toNat = X.val := by
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨T, hT, b1, b2, b3⟩ := mm_ok x (z := 1) (by omega_using [hB, a1]) (by decide)
  have e1 : n1W x = x - T * BitVec.ofNat 16 3329 := by
    unfold n1W qdW
    rw [show (BitVec.ofNat 16 10) = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.tw 1) from rfl, hT]
    rfl
  rw [show x * BitVec.ofNat 16 1 = x from BitVec.mul_one _] at b1 b2 b3
  have hn := nonneg_lane b1 b2
  unfold normW
  rw [e1, show BitVec.ofNat 16 qN = BitVec.ofNat 16 3329 from rfl]
  generalize x - T * BitVec.ofNat 16 3329 = r at b1 b2 b3 hn ⊢
  have hX : X.val < 3329 := X.isLt
  have hv : (r + (r.sshiftRight 15 &&& BitVec.ofNat 16 3329)).toInt = (X.val : Int) := by
    rw [hn]
    split <;> omega_arith
  generalize r + (r.sshiftRight 15 &&& BitVec.ofNat 16 3329) = y at hv ⊢
  rw [BitVec.toInt_eq_toNat_cond] at hv
  split at hv <;> omega_using [hv]

/-- The reduced coefficients are those of `NTT`. -/
theorem Of_ntt (W : Nat → BitVec 16) (F : Poly) (h : ∀ p < 256, LRep (W p) F[p]! 3329) {p : Nat} (hp : p < 256) :
    (Of W p).toNat = ((ntt F)[p]!).val := by
  rw [ntt_eq_nttL]
  exact normW_val (Lf_rep W F h 7 (by decide) p hp) (by decide)

end VG.Proof.MlKem.AArch64.NttR

end

end

/-! ### `MlKem.AArch64.Ntt16.Gs`, which this module and modules that import it used -/

section

/-!
# ML-KEM's 16-bit inverse NTT on AArch64: lanes

The inverse butterfly on one lane: `x ← x + y`, `y ← (y - x) · z mod q`
(`gs_lane`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

private theorem toInt_add16' {a r : BitVec 16} (h1 : -32768 ≤ a.toInt + r.toInt)
    (h2 : a.toInt + r.toInt < 32768) : (a + r).toInt = a.toInt + r.toInt := by
  rw [BitVec.toInt_add]; simp only [Int.bmod_def]; split <;> omega_arith

private theorem toInt_sub16' {a r : BitVec 16} (h1 : -32768 ≤ a.toInt - r.toInt)
    (h2 : a.toInt - r.toInt < 32768) : (a - r).toInt = a.toInt - r.toInt := by
  rw [BitVec.toInt_sub]; simp only [Int.bmod_def]; split <;> omega_arith

/-- An inverse butterfly on one lane: `a + b`, and `r = d · z - t · q` for
`d = b - a`, `t = sqrdmulh(d, tw z)`. -/
theorem gs_lane {a b : BitVec 16} {X Y : Zq} {z Bx By : Nat} (ha : LRep a X Bx) (hb : LRep b Y By)
    (hz : z < 3329) (hB : Bx + By ≤ 32768) :
    ∃ t, sqdmulhHLane true (b - a) (BitVec.ofNat 16 (tw z)) = some t ∧
      LRep (a + b) (X + Y) (Bx + By) ∧
      LRep ((b - a) * BitVec.ofNat 16 z - t * BitVec.ofNat 16 3329) (ofNat z * (Y - X)) 3329 := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  have hd : (b - a).toInt = b.toInt - a.toInt := toInt_sub16' (by omega_arith) (by omega_arith)
  obtain ⟨t, ht, h1, h2, h3⟩ := mm_ok (b - a) (z := z) (by omega_arith) hz
  refine ⟨t, ht, ?_, ?_⟩
  · have hX := val_lt X
    have hY := val_lt Y
    have e1 : (X + Y).val = (X.val + Y.val) % 3329 := val_add' X Y
    refine ⟨?_, ?_, ?_⟩ <;> rw [toInt_add16' (by omega_arith) (by omega_arith)] <;> [omega_arith; omega_arith; skip]
    rw [e1]; omega_arith
  · refine ⟨h1, h2, ?_⟩
    rw [hd] at h3
    generalize (b - a) * BitVec.ofNat 16 z - t * BitVec.ofNat 16 3329 = r at h1 h2 h3 ⊢
    obtain ⟨k1, hk1⟩ := Int.dvd_of_emod_eq_zero b3
    obtain ⟨k2, hk2⟩ := Int.dvd_of_emod_eq_zero a3
    have hX := val_lt X
    have hY := val_lt Y
    -- `(Y - X).val = Y - X + q·c`
    have eD : ((Y - X).val : Int) = (Y.val : Int) - X.val + 3329 * (if X.val ≤ Y.val then 0 else 1) := by
      rw [val_sub_eq]
      have hq : q = 3329 := rfl
      by_cases h : X.val ≤ Y.val <;> simp only [h, ite_true, ite_false] <;> omega_arith
    have e2 : (ofNat z * (Y - X)).val = z * (Y - X).val % 3329 := by
      rw [val_mul, val_ofNat, Nat.mod_eq_of_lt (show z < q from hz)]
    rw [e2]
    have hm : (b.toInt - a.toInt) * z =
        (((Y - X).val : Int) * z) + 3329 * ((k1 - k2 - (if X.val ≤ Y.val then 0 else 1)) * z) := by
      rw [eD, show b.toInt = Y.val + 3329 * k1 by omega_arith, show a.toInt = X.val + 3329 * k2 by omega_arith]
      split <;> grind
    have hW : ((z * (Y - X).val : Nat) : Int) = ((Y - X).val : Int) * z := by
      rw [Int.natCast_mul, Int.mul_comm]
    rw [hm] at h3
    generalize z * (Y - X).val = W at hW ⊢
    generalize ((Y - X).val : Int) * z = Wi at hW h3
    generalize (k1 - k2 - (if X.val ≤ Y.val then 0 else 1)) * (z : Int) = K at h3
    omega_arith

end VG.Proof.MlKem.AArch64.Ntt16

end

end

/-!
# ML-KEM on AArch64: the lanes of the inverse NTT, reduced

A lane of the 16-bit inverse NTT reduced to less than `q` in absolute value
represents the same coefficient (`n1W_rep`), and made nonnegative is its
value (`normL_val`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Proof.MlKem.AArch64.Ntt16 (LRep gs_lane mm_ok ofNat_zeta zeta_lt nonneg_lane)

/-! ## The coefficients represent `NTT⁻¹`'s -/

/-- A lane reduced to less than `q` in absolute value. -/
theorem n1W_rep {a : BitVec 16} {X : Zq} {B : Nat} (h : LRep a X B) (hB : B ≤ 32768) : LRep (n1W a) X 3329 := by
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨T, hT, b1, b2, b3⟩ := mm_ok a (z := 1) (by omega_arith) (by decide)
  have e1 : n1W a = a - T * BitVec.ofNat 16 3329 := by
    unfold n1W qdW
    rw [show (BitVec.ofNat 16 10) = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.tw 1) from rfl, hT]
    rfl
  rw [show a * BitVec.ofNat 16 1 = a from BitVec.mul_one _] at b1 b2 b3
  rw [e1]
  refine ⟨b1, b2, ?_⟩
  omega_arith

/-- `a`, less than `q` in absolute value, made nonnegative, is its value. -/
theorem normL_val {x : BitVec 16} {X : Zq} (h : LRep x X 3329) : (normL x).toNat = X.val := by
  obtain ⟨b1, b2, b3⟩ := h
  have hn := nonneg_lane b1 b2
  unfold normL
  rw [show BitVec.ofNat 16 qN = BitVec.ofNat 16 3329 from rfl]
  have hX : X.val < 3329 := X.isLt
  have hv : (x + (x.sshiftRight 15 &&& BitVec.ofNat 16 3329)).toInt = (X.val : Int) := by
    rw [hn]
    split <;> omega_arith
  generalize x + (x.sshiftRight 15 &&& BitVec.ofNat 16 3329) = y at hv ⊢
  rw [BitVec.toInt_eq_toNat_cond] at hv
  split at hv <;> omega_arith

end VG.Proof.MlKem.AArch64.NttR

end

end

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
  obtain ⟨k, rfl⟩ : ∃ k, st = k + 1 := ⟨st - 1, by omega_using [hs]⟩
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
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show len < 2 * len by omega_using [hpos])]
      exact Nat.mod_eq_of_lt (by omega_using [hm])
    rw [ite_eq_right (by omega_using [h1]), Nat.add_sub_cancel]

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
    exact Nat.mul_le_mul (by omega_using [hA, hA']) (by omega_using [hdz])
  generalize hE : (M - 1) * dz z = E at hn ⊢
  have hQ1 : A * d ≤ E := by omega_using [hn]
  have hQ2 : -(E : Int) ≤ A * d := by omega_using [hn]
  have hX : A * z * 65536 = 6658 * (A * C) + A * d := by rw [← hd]; grind
  have h2 : 2 * A * C = 2 * (A * C) := by grind
  rw [h2]
  generalize A * C = P at hX
  generalize A * d = Q at hQ1 hQ2 hX
  generalize A * (z : Int) = X at hX ⊢
  omega_using [hQ1, hQ2, hX]

/-- `mm_ok` with the bound of the factor: `r = a · z - t · q` is less than
`mmB M z` in absolute value for `|a| < M`. -/
theorem mm_tight (a : BitVec 16) {z M : Nat} (ha : -(M : Int) < a.toInt) (ha' : a.toInt < M) (hM : M ≤ 32768)
    (hz : z < 3329) :
    ∃ t, sqdmulhHLane true a (BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.tw z)) = some t ∧
      -(mmB M z : Int) < (a * BitVec.ofNat 16 z - t * BitVec.ofNat 16 3329).toInt ∧
      (a * BitVec.ofNat 16 z - t * BitVec.ofNat 16 3329).toInt < mmB M z ∧
      ((a * BitVec.ofNat 16 z - t * BitVec.ofNat 16 3329).toInt - a.toInt * z) % 3329 = 0 := by
  obtain ⟨t, ht, -, -, h3⟩ := Ntt16.mm_ok a (z := z) (by omega_arith) hz
  refine ⟨t, ht, ?_⟩
  have htw := tw_lt hz
  have hc : (BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.tw z)).toInt = Impl.MlKem.AArch64.Ntt16.tw z := by
    rw [BitVec.toInt_ofNat']; simp only [Int.bmod_def]; omega_arith
  have hzt : (BitVec.ofNat 16 z).toInt = z := by
    rw [BitVec.toInt_ofNat']; simp only [Int.bmod_def]; omega_arith
  have hq : (BitVec.ofNat 16 3329).toInt = 3329 := by decide
  have hne : ¬ (a = 0x8000#16 ∧ BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.tw z) = 0x8000#16) := by
    rintro ⟨-, h⟩
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this; omega_arith
  have et : t = _ := Option.some.inj (ht.symm.trans (by simp only [sqdmulhHLane, hne, ite_false]; rfl))
  subst et
  have hmb : mmB M z ≤ 32768 := by
    unfold mmB
    have : dz z ≤ 3329 := by
      -- (`omega` on `↑z * 65536` as it stands has the kernel multiply `z` by 65536 in unary.)
      unfold dz; rw [tw_def]
      generalize (z : Int) * 65536 = X
      omega_arith
    have : (M - 1) * dz z ≤ 32767 * 3329 := Nat.mul_le_mul (by omega_arith) this
    omega_arith
  refine ⟨?_, ?_, h3⟩ <;>
  · have h := core_tight (A := a.toInt) (z := z) ha ha'
    simp only [BitVec.toInt_sub, BitVec.toInt_mul, BitVec.toInt_ofInt, hc, hzt, hq, tw_def]
    rw [Int.shiftRight_eq_div_pow]
    simp only [ite_true, show (2 : Int) ^ 15 = 32768 from rfl]
    generalize (2 * a.toInt * (((z : Int) * 65536 + 3329) / 6658) + 32768) / 65536 = T at *
    generalize a.toInt * (z : Int) = X at *
    simp only [Int.bmod_def]
    omega_arith

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
  have : a.toInt * z = X.val * z + 3329 * (k * z) := by rw [show a.toInt = X.val + 3329 * k by omega_using [hk]]; grind
  rw [this] at b3
  generalize a.toInt * z = A at b3
  generalize k * (z : Int) = K at b3
  omega_using [b3]

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

theorem bF_ends : (∀ p < 256, bF 0 p = 3329 ∧ mmB 3329 3303 ≤ bF 1 p ∧ bF 8 p ≤ 32768) := by lit_decide

/-- The sums of each level fit, and their bounds (reduced or not) are those
of the next level. -/
theorem bF_sum : ∀ st < 7, ∀ p < 256, p % (2 * fLen (st + 1)) < fLen (st + 1) →
    p + fLen (st + 1) < 256 ∧ bF (st + 1) p + bF (st + 1) (p + fLen (st + 1)) ≤ 32768 ∧
    (if fRed (st + 1) p = true then mmB (bF (st + 1) p + bF (st + 1) (p + fLen (st + 1))) 1
      else bF (st + 1) p + bF (st + 1) (p + fLen (st + 1))) ≤ bF (st + 2) p := by lit_decide

/-- The differences of each level fit, their zetas are those of `NTT⁻¹`, and
their products are less than `q`. -/
theorem bF_dif : ∀ st < 7, ∀ p < 256, ¬ p % (2 * fLen (st + 1)) < fLen (st + 1) →
    fLen (st + 1) ≤ p ∧ bF (st + 1) p + bF (st + 1) (p - fLen (st + 1)) ≤ 32768 ∧ 3329 ≤ bF (st + 2) p ∧
    256 / fLen (st + 1) - 1 - p / (2 * fLen (st + 1)) < 128 ∧
    0 < zetaN (256 / fLen (st + 1) - 1 - p / (2 * fLen (st + 1))) ∧
    zetaN (256 / fLen (st + 1) - 1 - p / (2 * fLen (st + 1))) < 3329 := by lit_decide

theorem fLen_eq : ∀ st < 7, fLen (st + 1) = 2 <<< st := by lit_decide

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
    have ih := Lfi_rep W F h (st + 1) (by omega_using [hs])
    rw [Lfi_succ W (by omega_using []), vFi_succ, nttInvL_succ_get F (show st < 7 by omega_using [hs]) hp, ← fLen_eq st (by omega_using [hs])]
    simp only [vFi_succ] at ih
    by_cases hm : p % (2 * fLen (st + 1)) < fLen (st + 1)
    · obtain ⟨hp', hB, hn⟩ := bF_sum st (by omega_using [hs]) p hp hm
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
    · obtain ⟨hl, hB, hn, hk, hz0, hz⟩ := bF_dif st (by omega_using [hs]) p hp hm
      rw [ite_eq_right hm, ite_eq_right hm]
      obtain ⟨T, hT, -, l2⟩ := gs_lane (z := zf (st + 1) p) (ih p hp) (ih (p - fLen (st + 1)) (by omega_using [hp]))
        (by unfold zf qN; omega_using [hz0]) hB
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
