import VerifiedGarbage.Proof.Blowfish.F

/-!
# A lookup that scans an S-box's planes a word at a time

What the 32-bit implementations hold while scanning S-box `j` for the index
`x` a row (four entries, a word of each plane) at a time: the words of the
row that holds `x`, masked to `x`'s byte lane `L = x mod 4` and plane `b`'s
rotated left by `8b` (`hitWord`), ORed together; and, rotated right by
`8L`, the entry (`hitWord_ror`).
-/

namespace VG.Proof.Blowfish

open VG VG.Spec.Blowfish

/-- The mask of byte lane `L`. -/
def laneMask (L : Nat) : BitVec 32 := BitVec.ofNat 32 255 <<< (8 * L)

/-- Plane `b`'s word of row `k` of S-box `j`, in the schedule at `p`. -/
def planeWord (m : Mem) (p : Addr) (j b k : Nat) : BitVec 32 :=
  m.readW (p + BitVec.ofNat 64 (1024 * j + 256 * b + 4 * k)) 32

/-- The words of the row holding `x`, masked to its lane, plane `b`'s
rotated left by `8b`, ORed. -/
def hitWord (m : Mem) (p : Addr) (j x : Nat) : BitVec 32 :=
  let w := fun b => planeWord m p j b (x / 4) &&& laneMask (x % 4)
  ((w 0 ||| (w 1).rotateRight 24) ||| (w 2).rotateRight 16) ||| (w 3).rotateRight 8

/-- The accumulator once rows `0, …, k - 1` are scanned. -/
def scanAcc (m : Mem) (p : Addr) (j x k : Nat) : BitVec 32 :=
  if x / 4 < k then hitWord m p j x else 0

theorem byte_rotateRight (x : BitVec 32) {r c : Nat} (hr : r < 4) (hc : c < 4) :
    (x.rotateRight (8 * r)).extractLsb' (8 * c) 8 = x.extractLsb' (8 * ((c + r) % 4)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_rotateRight_of_lt (show 8 * r < 32 by omega)]
  by_cases h : 8 * c + i < 32 - 8 * r
  · rw [ite_eq_left h]; congr 1; omega
  · rw [ite_eq_right h, show decide (8 * c + i < 32) = true by simp; omega, Bool.true_and]
    congr 1; omega

theorem byte_laneMask {L c : Nat} (hL : L < 4) (hc : c < 4) :
    (laneMask L).extractLsb' (8 * c) 8 = if c = L then 255#8 else 0#8 := by
  rcases (by omega : L = 0 ∨ L = 1 ∨ L = 2 ∨ L = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;> decide

theorem and_255 (b : Byte) : b &&& 255#8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, show (255#8).getLsbD i = true by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, Bool.and_true]

/-- Byte `c` of the row's word, rotated right by `8L`, is byte `L` of plane
`c`'s word. -/
theorem hitWord_byte (m : Mem) (p : Addr) (j : Nat) {x c : Nat} (hc : c < 4) :
    ((hitWord m p j x).rotateRight (8 * (x % 4))).extractLsb' (8 * c) 8 =
      (planeWord m p j c (x / 4)).extractLsb' (8 * (x % 4)) 8 := by
  simp only [hitWord]
  have hL : x % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize x % 4 = L at hL ⊢
  generalize x / 4 = k
  have r24 : ∀ y : BitVec 32, y.rotateRight 24 = y.rotateRight (8 * 3) := fun _ => rfl
  have r16 : ∀ y : BitVec 32, y.rotateRight 16 = y.rotateRight (8 * 2) := fun _ => rfl
  have r8 : ∀ y : BitVec 32, y.rotateRight 8 = y.rotateRight (8 * 1) := fun _ => rfl
  rw [byte_rotateRight _ hL hc]
  have hm : (c + L) % 4 < 4 := Nat.mod_lt _ (by decide)
  simp only [BitVec.extractLsb'_or]
  rw [r24, byte_rotateRight _ (by decide) hm, r16, byte_rotateRight _ (by decide) hm,
    r8, byte_rotateRight _ (by decide) hm]
  simp only [BitVec.extractLsb'_and]
  rw [byte_laneMask hL hm, byte_laneMask hL (Nat.mod_lt _ (by decide)),
    byte_laneMask hL (Nat.mod_lt _ (by decide)), byte_laneMask hL (Nat.mod_lt _ (by decide))]
  rcases (by omega : L = 0 ∨ L = 1 ∨ L = 2 ∨ L = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;>
  simp [and_255]

/-- The row's word, rotated right by `8L`, is S-box `j`'s entry `x`. -/
theorem hitWord_ror (m : Mem) (p : Addr) {j : Nat} (hj : j < 4) (x : Byte) :
    (hitWord m p j x.toNat).rotateRight (8 * (x.toNat % 4)) = sEntry (scheduleAt m p) j x := by
  refine word_ext fun c hc => ?_
  rw [hitWord_byte m p j hc, sEntry_byte m p hj hc, planeWord, ← Mem.readW_byte _ _ (Nat.mod_lt _ (by decide)),
    Offset.add_add]
  congr 3
  omega

theorem scanAcc_zero (m : Mem) (p : Addr) (j x : Nat) : scanAcc m p j x 0 = 0 := by
  simp [scanAcc]

theorem scanAcc_all (m : Mem) (p : Addr) (j : Nat) (x : Byte) :
    scanAcc m p j x.toNat 64 = hitWord m p j x.toNat := by
  have := x.isLt
  simp only [scanAcc, show x.toNat / 4 < 64 by omega, ite_true]

/-- A row: the words masked by `M`, the lane mask if the row holds `x`,
else zero. -/
theorem scanAcc_succ (m : Mem) (p : Addr) (j x k : Nat) (M : BitVec 32)
    (hM : M = if x / 4 = k then laneMask (x % 4) else 0) :
    (((scanAcc m p j x k ||| (planeWord m p j 0 k &&& M)) |||
      (planeWord m p j 1 k &&& M).rotateRight 24) ||| (planeWord m p j 2 k &&& M).rotateRight 16) |||
      (planeWord m p j 3 k &&& M).rotateRight 8 = scanAcc m p j x (k + 1) := by
  subst hM
  unfold scanAcc
  by_cases h : x / 4 = k
  · subst h
    simp [hitWord]
  · by_cases h' : x / 4 < k
    · simp [h, h', show x / 4 < k + 1 by omega]
    · simp [h, h', show ¬ x / 4 < k + 1 by omega]

/-! ## Masks -/

/-- `x - 4k < 4` (as 32-bit words) iff row `k` holds `x`. -/
theorem row_hit (x : Byte) {k : Nat} (hk : k < 64) :
    (x.setWidth 32 - BitVec.ofNat 32 (4 * k)).toNat < 4 ↔ x.toNat / 4 = k := by
  have := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x.toNat < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show 4 * k < 2 ^ 32 by omega)]
  omega

/-- What `adc d, ones, #0` leaves after a comparison that set the carry to `c`:
zero if `c`, else all ones. -/
theorem adc_ones (c : Bool) :
    BitVec.allOnes 32 + BitVec.ofNat 32 0 + BitVec.ofNat 32 c.toNat =
      if c then 0 else BitVec.allOnes 32 := by
  cases c <;> decide

/-- `((x XOR t) AND m) XOR t` with the mask `adc` leaves. -/
theorem select_rot (x t : BitVec 32) (c : Bool) :
    ((x ^^^ t) &&& (BitVec.allOnes 32 + BitVec.ofNat 32 0 + BitVec.ofNat 32 c.toNat)) ^^^ t =
      if c then t else x := by
  rw [adc_ones]
  cases c
  · simp only [Bool.false_eq_true, ite_false, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero]
  · simp

end VG.Proof.Blowfish
