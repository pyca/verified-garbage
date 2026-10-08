import VerifiedGarbage.Proof.AesGcm.X86_64.Run

/-! # The interleaved working region inside the public scratch buffer -/
namespace VG.Proof.AesGcm.X86_64.AlignedScratch
open VG VG.X86_64

def ptr (aligned : Bool) (p : Addr) : Addr :=
  if aligned then (p + 127) &&& (-64) else p + 64

def offset (aligned : Bool) (p : Addr) : Nat :=
  if aligned then 127 - (p.toNat + 127) % 64 else 64

theorem offset_bounds (aligned : Bool) (p : Addr) :
    64 ≤ offset aligned p ∧ offset aligned p ≤ 127 := by
  cases aligned <;> simp only [offset, Bool.false_eq_true, ↓reduceIte]
  · omega
  · have := Nat.mod_lt (p.toNat + 127) (by decide : 0 < 64); omega

theorem mask_nat (x : Addr) : (x &&& (-64)).toNat = x.toNat / 64 * 64 := by
  have h : (BitVec.allOnes 64 <<< 6 : Addr) = -64 := by decide
  rw [← h, ← BitVec.shiftLeft_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
  simp only [Nat.reducePow]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  simp only [Nat.reducePow]
  have hx := x.isLt
  have hm := Nat.mod_lt x.toNat (by decide : 0 < 64)
  have hd := Nat.mod_add_div x.toNat 64
  rw [Nat.mod_eq_of_lt (by omega)]

theorem ptr_eq (aligned : Bool) (p : Addr) (hp : p.toNat + 2112 ≤ 2^64) :
    ptr aligned p = p + BitVec.ofNat 64 (offset aligned p) := by
  apply BitVec.eq_of_toNat_eq
  cases aligned with
  | false => rfl
  | true =>
    simp only [ptr, offset, ↓reduceIte, mask_nat,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    have hp' : (p.toNat + 127) % 2^64 = p.toNat + 127 := Nat.mod_eq_of_lt (by omega)
    simp only [show (127 : Addr).toNat = 127 from rfl, hp']
    have hm := Nat.mod_lt (p.toNat + 127) (by decide : 0 < 64)
    have hd := Nat.mod_add_div (p.toNat + 127) 64
    rw [Nat.mod_eq_of_lt (show 127 - (p.toNat + 127) % 64 < 2^64 by omega)]
    rw [Nat.mod_eq_of_lt (show p.toNat + (127 - (p.toNat + 127) % 64) < 2^64 by omega)]
    omega

end VG.Proof.AesGcm.X86_64.AlignedScratch
