module

public import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# RISC-V: rounding a pointer up to a multiple of 8

Untrusted: everything here is checked by Lean. Loads and stores fault
unless naturally aligned, and the contracts state no alignment for argument
buffers, so code that keeps doublewords in a buffer with room to spare
rounds its address up first: `addi d, n, 7 + off` then `andi d, d, -8`
leaves `n + off + pad (n + off)` in `d` (`align_eq`), a multiple of 8
(`align_al`) at most 7 bytes above `n + off` (`pad_lt`).
-/

@[expose] public section

namespace VG.RISCV64.Align

/-- How far `x` is below the next multiple of 8. -/
def pad (x : Addr) : Nat := (8 - x.toNat % 8) % 8

theorem pad_lt (x : Addr) : pad x < 8 := Nat.mod_lt _ (by decide)

theorem and_neg8 (y : BitVec 64) : y &&& BitVec.ofInt 64 (-8) = (y >>> 3) <<< 3 := by
  have : BitVec.ofInt 64 (-8) = BitVec.allOnes 64 <<< 3 := by decide
  rw [this]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes, hi, decide_true, Bool.true_and]
  by_cases h3 : i < 3
  · simp [h3]
  · simp [h3, show 3 + (i - 3) = i by omega, show i - 3 < 64 by omega]

/-- `addi 7` then `andi -8`. -/
theorem align_eq (x : Addr) :
    (x + BitVec.ofInt 64 7) &&& BitVec.ofInt 64 (-8) = x + BitVec.ofNat 64 (pad x) := by
  rw [and_neg8]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, pad]
  have := x.isLt
  rw [show BitVec.toNat (BitVec.ofInt 64 7) = 7 from rfl]
  omega

/-- `addi (off + 7)` then `andi -8`, rounding `p + off` up. -/
theorem align_off_eq (p : Addr) {imm : Int} {off : Nat} (h : imm = (off : Int) + 7)
    (ho : off + 7 < 2 ^ 63) :
    (p + BitVec.ofInt 64 imm) &&& BitVec.ofInt 64 (-8) =
      p + BitVec.ofNat 64 off + BitVec.ofNat 64 (pad (p + BitVec.ofNat 64 off)) := by
  rw [← align_eq, BitVec.add_assoc]
  congr 2
  subst h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_add, BitVec.toNat_ofNat,
    show (BitVec.ofInt 64 7).toNat = 7 from rfl]
  omega

theorem align_al (x : Addr) : (x + BitVec.ofNat 64 (pad x)).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  unfold pad
  have := x.isLt
  omega

/-- An offset by a multiple of 8 of a rounded address is a multiple of 8. -/
theorem align_al_add (x : Addr) {d : Nat} (hd : d % 8 = 0) :
    (x + BitVec.ofNat 64 (pad x) + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  have := align_al x
  rw [BitVec.toNat_add (x + _), BitVec.toNat_ofNat]
  omega

/-- An offset of a rounded address `p + off + pad`, as one of `p`. -/
theorem align_add (p : Addr) (off d : Nat) :
    p + BitVec.ofNat 64 off + BitVec.ofNat 64 (pad (p + BitVec.ofNat 64 off)) + BitVec.ofNat 64 d =
      p + BitVec.ofNat 64 (off + pad (p + BitVec.ofNat 64 off) + d) := by
  rw [BitVec.ofNat_add, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]

end VG.RISCV64.Align
