import VerifiedGarbage.Impl.Blowfish.Table
import VerifiedGarbage.Proof.Blowfish.Blocks

/-!
# The table of the initial schedule

`initWord_byte`: byte `b` of word `i` of the table is byte `8 i + b` of the
initial schedule's image; `initByte_entry`: byte `b` of entry `i` of that
image is byte `b` of `initial[i]`; `scheduleAt_of_bytes`: memory holding the
bytes of each entry of a schedule holds the schedule.
-/

namespace VG.Proof.Blowfish

open VG VG.Spec.Blowfish VG.Impl.Blowfish

theorem initWord_byte (i : Nat) {b : Nat} (hb : b < 8) :
    (initWord i).extractLsb' (8 * b) 8 = initByte (8 * i + b) := by
  simp only [initWord, List.range, List.range.loop, List.foldl_cons, List.foldl_nil]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := omega) [hj, decide_eq_true, decide_eq_false, BitVec.getLsbD_of_ge]

theorem initByte_entry {i b : Nat} (hi : i < 1042) (hb : b < 4) :
    initByte (entryOff i b) = (initial.getD i 0).extractLsb' (8 * b) 8 := by
  unfold initByte entryOff
  by_cases h : i < 18
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_right_of_eq_false _ _ (eq_false (by omega)), shr_setWidth, show (4096 + 4 * i + b - 4096) / 4 = i by omega,
      show (4096 + 4 * i + b - 4096) % 4 = b by omega]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_left_of_eq_true _ _ (eq_true (by omega)), shr_setWidth,
      show 18 + 256 * ((1024 * ((i - 18) / 256) + 256 * b + (i - 18) % 256) / 1024) +
        (1024 * ((i - 18) / 256) + 256 * b + (i - 18) % 256) % 256 = i by omega,
      show (1024 * ((i - 18) / 256) + 256 * b + (i - 18) % 256) % 1024 / 256 = b by omega]

theorem scheduleAt_of_bytes {m : Mem} {p : Addr} {V : Schedule}
    (h : ∀ i < 1042, ∀ b < 4, m (p + BitVec.ofNat 64 (entryOff i b)) = (V.getD i 0).extractLsb' (8 * b) 8) :
    scheduleAt m p = V := by
  apply Vector.ext; intro i hi
  rw [scheduleAt_get _ _ hi, h i hi 0 (by decide), h i hi 1 (by decide), h i hi 2 (by decide),
    h i hi 3 (by decide), show V.getD i 0 = V[i] by simp [Vector.getD, Array.getD, hi]]
  refine word_ext fun b hb => ?_
  rw [byte_of_le4 _ _ _ _ hb]
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Blowfish
