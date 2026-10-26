module
public import VerifiedGarbage.Spec.Blowfish

import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# A lookup that scans an S-box's planes a doubleword at a time

As `Scan32.lean`, for 64-bit implementations that scan S-box `j` for the
index `x` a row of eight entries (a doubleword of each plane) at a time:
the doublewords of the row that holds `x`, masked to `x`'s byte lane
`L = x mod 8` and plane `b`'s rotated left by `8b` (`hitWord64`), ORed
together; and, rotated right by `8L`, the entry in the low word
(`hitWord64_ror`).
-/

@[expose] public section

namespace VG.Proof.Blowfish

open VG VG.Spec.Blowfish

/-- The mask of byte lane `L` of a doubleword. -/
def laneMask64 (L : Nat) : BitVec 64 := BitVec.ofNat 64 255 <<< (8 * L)

/-- Plane `b`'s doubleword of row `k` of S-box `j`, in the schedule at `p`. -/
def planeWord64 (m : Mem) (p : Addr) (j b k : Nat) : BitVec 64 :=
  m.readW (p + BitVec.ofNat 64 (1024 * j + 256 * b + 8 * k)) 64

/-- The doublewords of the row holding `x`, masked to its lane, plane `b`'s
rotated left by `8b`, ORed. -/
def hitWord64 (m : Mem) (p : Addr) (j x : Nat) : BitVec 64 :=
  let w := fun b => planeWord64 m p j b (x / 8) &&& laneMask64 (x % 8)
  ((w 0 ||| (w 1).rotateRight 56) ||| (w 2).rotateRight 48) ||| (w 3).rotateRight 40

/-- The accumulator once rows `0, …, k - 1` are scanned. -/
def scanAcc64 (m : Mem) (p : Addr) (j x k : Nat) : BitVec 64 :=
  if x / 8 < k then hitWord64 m p j x else 0

theorem byte_rotateRight64 (x : BitVec 64) {r c : Nat} (hr : r < 8) (hc : c < 8) :
    (x.rotateRight (8 * r)).extractLsb' (8 * c) 8 = x.extractLsb' (8 * ((c + r) % 8)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_rotateRight_of_lt (show 8 * r < 64 by omega_arith)]
  by_cases h : 8 * c + i < 64 - 8 * r
  · rw [ite_eq_left h]; congr 1; omega_arith
  · rw [ite_eq_right h, show decide (8 * c + i < 64) = true by simp; omega_arith, Bool.true_and]
    congr 1; omega_arith

theorem byte_laneMask64 {L c : Nat} (hL : L < 8) (hc : c < 8) :
    (laneMask64 L).extractLsb' (8 * c) 8 = if c = L then 255#8 else 0#8 := by
  have h : ∀ L < 8, ∀ c < 8, (laneMask64 L).extractLsb' (8 * c) 8 = if c = L then 255#8 else 0#8 := by
    decide
  exact h L hL c hc

theorem and_255' (b : Byte) : b &&& 255#8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, show (255#8).getLsbD i = true by
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, Bool.and_true]

/-- Byte `c` (of the low word) of the row's doubleword, rotated right by
`8L`, is byte `L` of plane `c`'s doubleword. -/
theorem hitWord64_byte (m : Mem) (p : Addr) (j : Nat) {x c : Nat} (hc : c < 4) :
    ((hitWord64 m p j x).rotateRight (8 * (x % 8))).extractLsb' (8 * c) 8 =
      (planeWord64 m p j c (x / 8)).extractLsb' (8 * (x % 8)) 8 := by
  simp only [hitWord64]
  have hL : x % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize x % 8 = L at hL ⊢
  generalize x / 8 = k
  have r56 : ∀ y : BitVec 64, y.rotateRight 56 = y.rotateRight (8 * 7) := fun _ => rfl
  have r48 : ∀ y : BitVec 64, y.rotateRight 48 = y.rotateRight (8 * 6) := fun _ => rfl
  have r40 : ∀ y : BitVec 64, y.rotateRight 40 = y.rotateRight (8 * 5) := fun _ => rfl
  rw [byte_rotateRight64 _ hL (by omega_arith)]
  have hm : (c + L) % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [BitVec.extractLsb'_or]
  rw [r56, byte_rotateRight64 _ (by decide) hm, r48, byte_rotateRight64 _ (by decide) hm,
    r40, byte_rotateRight64 _ (by decide) hm]
  simp only [BitVec.extractLsb'_and]
  rw [byte_laneMask64 hL hm, byte_laneMask64 hL (Nat.mod_lt _ (by decide)),
    byte_laneMask64 hL (Nat.mod_lt _ (by decide)), byte_laneMask64 hL (Nat.mod_lt _ (by decide))]
  rcases (by omega_arith : L = 0 ∨ L = 1 ∨ L = 2 ∨ L = 3 ∨ L = 4 ∨ L = 5 ∨ L = 6 ∨ L = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases (by omega_arith : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;>
  simp [and_255']

/-- The low word of the row's doubleword, rotated right by `8L`, is S-box
`j`'s entry `x`. -/
theorem hitWord64_ror (m : Mem) (p : Addr) {j : Nat} (hj : j < 4) (x : Byte) :
    ((hitWord64 m p j x.toNat).rotateRight (8 * (x.toNat % 8))).setWidth 32 =
      sEntry (scheduleAt m p) j x := by
  refine word_ext fun c hc => ?_
  have e : (((hitWord64 m p j x.toNat).rotateRight (8 * (x.toNat % 8))).setWidth 32).extractLsb' (8 * c) 8 =
      ((hitWord64 m p j x.toNat).rotateRight (8 * (x.toNat % 8))).extractLsb' (8 * c) 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
      show 8 * c + i < 32 by omega_arith]
  rw [e, hitWord64_byte m p j hc, sEntry_byte m p hj hc, planeWord64]
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]
  rw [Mem.extractLsb'_read m _ (Nat.mod_lt _ (by decide)), Offset.add_add]
  congr 3
  omega_arith

theorem scanAcc64_zero (m : Mem) (p : Addr) (j x : Nat) : scanAcc64 m p j x 0 = 0 := by
  simp [scanAcc64]

theorem scanAcc64_all (m : Mem) (p : Addr) (j : Nat) (x : Byte) :
    scanAcc64 m p j x.toNat 32 = hitWord64 m p j x.toNat := by
  have := x.isLt
  simp only [scanAcc64, show x.toNat / 8 < 32 by omega_arith, ite_true]

/-- A row: the doublewords masked by `M`, the lane mask if the row holds
`x`, else zero. -/
theorem scanAcc64_succ (m : Mem) (p : Addr) (j x k : Nat) (M : BitVec 64)
    (hM : M = if x / 8 = k then laneMask64 (x % 8) else 0) :
    (((scanAcc64 m p j x k ||| (planeWord64 m p j 0 k &&& M)) |||
      (planeWord64 m p j 1 k &&& M).rotateRight 56) ||| (planeWord64 m p j 2 k &&& M).rotateRight 48) |||
      (planeWord64 m p j 3 k &&& M).rotateRight 40 = scanAcc64 m p j x (k + 1) := by
  subst hM
  unfold scanAcc64
  by_cases h : x / 8 = k
  · subst h
    simp [hitWord64]
  · by_cases h' : x / 8 < k
    · simp [h, h', show x / 8 < k + 1 by omega_arith]
    · simp [h, h', show ¬ x / 8 < k + 1 by omega_arith]

/-! ## Rotations by the index's lane -/

/-- The lane mask: 255 rotated left a byte if bit 0 of the lane is set,
then two if bit 1 is, then four if bit 2 is. -/
theorem laneMask64_rot {L : Nat} (hL : L < 8) :
    (let r1 := if decide (L % 2 = 1) then (BitVec.ofNat 64 255).rotateRight 56 else BitVec.ofNat 64 255
     let r2 := if decide (L / 2 % 2 = 1) then r1.rotateRight 48 else r1
     if decide (L / 4 = 1) then r2.rotateRight 32 else r2) = laneMask64 L := by
  have h : ∀ L < 8,
      (let r1 := if decide (L % 2 = 1) then (BitVec.ofNat 64 255).rotateRight 56 else BitVec.ofNat 64 255
       let r2 := if decide (L / 2 % 2 = 1) then r1.rotateRight 48 else r1
       if decide (L / 4 = 1) then r2.rotateRight 32 else r2) = laneMask64 L := by
    decide
  exact h L hL

theorem ror_ror64 (x : BitVec 64) {a b : Nat} (h : a + b < 64) :
    (x.rotateRight a).rotateRight b = x.rotateRight (a + b) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_rotateRight_of_lt (show b < 64 by omega_arith),
    BitVec.getLsbD_rotateRight_of_lt (show a < 64 by omega_arith), BitVec.getLsbD_rotateRight_of_lt h]
  have d : ∀ n, n < 64 → decide (n < 64) = true := fun n hn => decide_eq_true hn
  split <;> split <;> (try split) <;>
    first
    | omega_arith
    | (congr 1; omega_arith)
    | (rw [d _ (by omega_arith), Bool.true_and]; congr 1; omega_arith)
    | (rw [d _ (by omega_arith), Bool.true_and, d _ (by omega_arith), Bool.true_and]; congr 1; omega_arith)

theorem ror_zero64 (x : BitVec 64) : x.rotateRight 0 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

/-- The accumulator rotated right by the lane's bytes. -/
theorem acc_rot64 (x : BitVec 64) {L : Nat} (hL : L < 8) :
    (let r1 := if decide (L % 2 = 1) then x.rotateRight 8 else x
     let r2 := if decide (L / 2 % 2 = 1) then r1.rotateRight 16 else r1
     if decide (L / 4 = 1) then r2.rotateRight 32 else r2) = x.rotateRight (8 * L) := by
  rcases (by omega_arith : L = 0 ∨ L = 1 ∨ L = 2 ∨ L = 3 ∨ L = 4 ∨ L = 5 ∨ L = 6 ∨ L = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
      Nat.reduceEqDiff, decide_true, decide_false, ite_true, ite_false, Bool.false_eq_true,
      ror_zero64, ror_ror64]

end VG.Proof.Blowfish
