import VerifiedGarbage.Proof.AesCtr.Inc
import VerifiedGarbage.Proof.Modes.Addr

/-!
# The running counter, for the modes on any 64-bit target

The modes keep the running counter block `V` (a number below `2¹²⁸`) as two
64-bit integers, `hiOf V` and `loOf V`. Stepping it by `N < 2⁶⁴` adds `N` to
the low half and the carry to the high half (`carry_vals`). The counter
block in memory is read as the byte-reversed words at `P` and `P + 8`
(`halves`: `bswap` on x86-64, `rev` on AArch64, both `AesCtr.rv64`), and the
two byte-reversed halves written back are `V`'s 16 big-endian bytes
(`bytes_pair`, `bytes_pair2`). Nothing here depends on a target.
-/

namespace VG.Proof.Modes

open VG
open VG.Spec.Aes (bytesAt)

/-- The high and low halves of the counter block `V`. -/
def hiOf (V : Nat) : BitVec 64 := BitVec.ofNat 64 (V / 2 ^ 64)
def loOf (V : Nat) : BitVec 64 := BitVec.ofNat 64 V

/-- `V + N`: `N` added to the low half, and its carry to the high half. -/
theorem carry_vals (V N : Nat) (hN : N < 2 ^ 64) :
    loOf V + BitVec.ofNat 64 N = loOf (V + N) ∧
    hiOf V + BitVec.ofNat 64 (decide (2 ^ 64 ≤ (loOf V).toNat + (BitVec.ofNat 64 N).toNat)).toNat =
      hiOf (V + N) := by
  refine ⟨by rw [loOf, loOf, BitVec.ofNat_add], ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [hiOf, loOf, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hN]
  by_cases h : 2 ^ 64 ≤ V % 2 ^ 64 + N
  · rw [decide_eq_true h]
    simp only [Bool.toNat_true]
    have : (V + N) / 2 ^ 64 = V / 2 ^ 64 + 1 := by omega
    rw [this]; omega
  · rw [decide_eq_false h]
    simp only [Bool.toNat_false]
    have : (V + N) / 2 ^ 64 = V / 2 ^ 64 := by omega
    rw [this]; omega

/-- The counter block at `P`, as a number. -/
abbrev ctrVal (m : Mem) (P : Addr) : Nat := Spec.Ctr.toNat (bytesAt m P 16)

/-- Its halves are the byte-reversed words at `P` and `P + 8`. -/
theorem halves (m : Mem) (P : Addr) :
    hiOf (ctrVal m P) = AesCtr.rv64 (m.readW P 64) ∧
      loOf (ctrVal m P) = AesCtr.rv64 (m.readW (P + BitVec.ofNat 64 8) 64) := by
  have h := AesCtr.toNat_append (bytesAt m P 8) (bytesAt m (P + BitVec.ofNat 64 8) 8)
  rw [← AesCtr.bytesAt_append, AesCtr.bytesAt_rv64, AesCtr.bytesAt_rv64, AesCtr.toNat_ofNat, AesCtr.toNat_ofNat,
    AesCtr.length_ofNat] at h
  have a1 := (AesCtr.rv64 (m.readW P 64)).isLt
  have a2 := (AesCtr.rv64 (m.readW (P + BitVec.ofNat 64 8) 64)).isLt
  simp only [Nat.reducePow] at a1 a2 h
  rw [Nat.mod_eq_of_lt a1, Nat.mod_eq_of_lt a2] at h
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [hiOf, BitVec.toNat_ofNat, ctrVal, h]
    omega
  · apply BitVec.eq_of_toNat_eq
    rw [loOf, BitVec.toNat_ofNat, ctrVal, h]
    omega

/-- `bytesAt` of the two byte-reversed halves written at `P` and then
`P + 8`: the big-endian bytes of `V`. -/
theorem bytes_pair (m : Mem) (P : Addr) (V : Nat) :
    bytesAt ((m.writeW P (AesCtr.rv64 (hiOf V))).writeW (P + BitVec.ofNat 64 8) (AesCtr.rv64 (loOf V))) P 16 =
      Spec.Ctr.ofNat V 16 := by
  rw [show (16 : Nat) = 8 + 8 from rfl, AesCtr.bytesAt_append, bytesAt_writeW_above _ _ _ (by decide) (by decide)
      (by decide), AesCtr.bytesAt_writeW_rv64, AesCtr.bytesAt_writeW_rv64, AesCtr.ofNat_add]
  congr 1
  · exact AesCtr.ofNat_congr (by simp only [hiOf, BitVec.toNat_ofNat]; omega)
  · exact AesCtr.ofNat_congr (by simp only [loOf, BitVec.toNat_ofNat]; omega)

/-- The same, written at `P + 8` and then `P`. -/
theorem bytes_pair2 (m : Mem) (P : Addr) (V : Nat) :
    bytesAt ((m.writeW (P + BitVec.ofNat 64 8) (AesCtr.rv64 (loOf V))).writeW P (AesCtr.rv64 (hiOf V))) P 16 =
      Spec.Ctr.ofNat V 16 := by
  rw [show (16 : Nat) = 8 + 8 from rfl, AesCtr.bytesAt_append, AesCtr.bytesAt_writeW_rv64,
    AesCtr.bytesAt_writeW_sep _ _ _ (by decide) (by decide), AesCtr.bytesAt_writeW_rv64, AesCtr.ofNat_add]
  congr 1
  · exact AesCtr.ofNat_congr (by simp only [hiOf, BitVec.toNat_ofNat]; omega)
  · exact AesCtr.ofNat_congr (by simp only [loOf, BitVec.toNat_ofNat]; omega)

end VG.Proof.Modes
