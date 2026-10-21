module

public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sound
public import VerifiedGarbage.Proof.MlKem.NttLayer
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Rows
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Idx
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane

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
  have h3 := Nat.mod_lt p (show 0 < 2 * len by omega)
  apply Nat.div_eq_of_lt_le
  · rw [Nat.mul_comm]
    generalize 2 * len * (p / (2 * len)) = M at h1 ⊢
    omega
  · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    generalize 2 * len * (p / (2 * len)) = M at h1 ⊢
    omega

theorem model (W : Nat → BitVec 16) : Model (Lf W) (Of W) fwdRules := by
  refine ⟨by decide, fun _ st p p' z t hb => ?_, nofun, nofun, nofun, nofun, fun p _ => rfl⟩
  unfold bflyOk fwdRules at hb
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hb
  obtain ⟨⟨⟨⟨⟨hst, rfl⟩, hm⟩, -⟩, rfl⟩, rfl⟩ := hb
  have hpos : 0 < 128 >>> st := by
    rcases (by omega : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨?_, ?_⟩
  · rw [Lf_succ, ite_eq_left hm]; rfl
  · have h1 : (p + (128 >>> st)) % (2 * (128 >>> st)) = p % (2 * (128 >>> st)) + (128 >>> st) := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 128 >>> st < 2 * (128 >>> st) by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [Lf_succ, ite_eq_right (by omega), Nat.add_sub_cancel]
    rfl

/-! ## The coefficients represent `NTT`'s -/

theorem lens_get {st : Nat} (h : st < 7) :
    0 < 128 >>> st ∧ 2 * (128 >>> st) * (128 / (128 >>> st)) = 256 ∧ 128 / (128 >>> st) + 255 / (2 * (128 >>> st)) < 128 := by
  rcases (by omega : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem mmW_eq {b : BitVec 16} {z : Nat} {T : BitVec 16}
    (h : sqdmulhHLane true b (BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.tw z)) = some T) :
    mmW b z (twN z) = b * BitVec.ofNat 16 z - T * BitVec.ofNat 16 3329 := by
  unfold mmW qdW; rw [h]; rfl

theorem pair_lt {p len K : Nat} (hpos : 0 < len) (hp : p < 2 * len * K) (hm : p % (2 * len) < len) :
    p + len < 2 * len * K := by
  have h1 := Nat.div_add_mod p (2 * len)
  have hq : p / (2 * len) < K := (Nat.div_lt_iff_lt_mul (by omega)).2 (by rw [Nat.mul_comm]; exact hp)
  have h2 : 2 * len * (p / (2 * len) + 1) ≤ 2 * len * K := Nat.mul_le_mul_left _ hq
  rw [Nat.mul_add, Nat.mul_one] at h2
  generalize 2 * len * (p / (2 * len)) = M at h1 h2
  omega

/-- The coefficients after `st` layers represent those of `NTT` after `st` layers. -/
theorem Lf_rep (W : Nat → BitVec 16) (F : Poly) (h : ∀ p < 256, LRep (W p) F[p]! 3329) :
    ∀ st ≤ 7, ∀ p < 256, LRep (Lf W st p) (nttL st F)[p]! ((st + 1) * 3329)
  | 0, _, p, hp => by simp only [Lf, nttL_zero]; exact (h p hp).mono (by omega)
  | st + 1, hs, p, hp => by
    have ih := Lf_rep W F h st (by omega)
    obtain ⟨hpos, hl, hz⟩ := lens_get (st := st) (by omega)
    rw [nttL_succ F (by omega), nttLayer_get _ hpos hl hp, Lf_succ]
    generalize 128 >>> st = len at hpos hl hz
    have hdiv : p / (2 * len) ≤ 255 / (2 * len) := Nat.div_le_div_right (show p ≤ 255 by omega)
    have hk : 128 / len + p / (2 * len) < 128 := by omega
    rw [show (st + 1 + 1) * 3329 = (st + 1) * 3329 + 3329 by omega]
    by_cases hm : p % (2 * len) < len
    · rw [ite_eq_left hm, ite_eq_left hm]
      obtain ⟨T, hT, l1, -⟩ := bf_lane (ih p hp) (ih (p + len) (by have := pair_lt hpos (show p < 2 * len * (128 / len) by omega) hm; omega)) (zeta_lt hk) (by omega) (by omega)
      unfold zk
      rw [mmW_eq hT, ← ofNat_zeta hk]
      exact l1
    · rw [ite_eq_right hm, ite_eq_right hm]
      obtain ⟨T, hT, -, l2⟩ := bf_lane (ih (p - len) (by omega)) (ih p hp) (zeta_lt hk) (by omega) (by omega)
      unfold zk
      rw [div_sub_len hpos hm, mmW_eq hT, ← ofNat_zeta hk]
      exact l2

/-- A coefficient less than `2¹⁵` in absolute value, reduced to `[0, q)`. -/
theorem normW_val {x : BitVec 16} {X : Zq} {B : Nat} (h : LRep x X B) (hB : B ≤ 32768) :
    (normW x).toNat = X.val := by
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨T, hT, b1, b2, b3⟩ := mm_ok x (z := 1) (by omega) (by decide)
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
    split <;> omega
  generalize r + (r.sshiftRight 15 &&& BitVec.ofNat 16 3329) = y at hv ⊢
  rw [BitVec.toInt_eq_toNat_cond] at hv
  split at hv <;> omega

/-- The reduced coefficients are those of `NTT`. -/
theorem Of_ntt (W : Nat → BitVec 16) (F : Poly) (h : ∀ p < 256, LRep (W p) F[p]! 3329) {p : Nat} (hp : p < 256) :
    (Of W p).toNat = ((ntt F)[p]!).val := by
  rw [ntt_eq_nttL]
  exact normW_val (Lf_rep W F h 7 (by decide) p hp) (by decide)

end VG.Proof.MlKem.AArch64.NttR
