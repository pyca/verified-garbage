module

import VerifiedGarbage.Proof.MillerRabin.Word32

/-! # Secret square thresholds and window flag updates use only bit operations -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG.Proof.MillerRabin.Word32

theorem squareFlag_value {r q : Nat} (rBound : r < 2 ^ 31) (qBound : q < 2 ^ 31) (E F : Bool) :
    ((BitVec.ofNat 32 F.toNat) ||| ((BitVec.ofNat 32 E.toNat) &&&
      ((BitVec.ofNat 32 r - BitVec.ofNat 32 q) >>> 31))).toNat =
      (F || (E && decide (r < q))).toNat := by
  have bit : ((BitVec.ofNat 32 r - BitVec.ofNat 32 q) >>> 31) =
      BitVec.ofNat 32 (decide (r < q)).toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_lt rBound qBound]
    cases decide (r < q) <;> rfl
  rw [bit]
  cases F <;> cases E <;> cases decide (r < q) <;> rfl

theorem windowFlag_value {d : Nat} (digit : d < 16) (E1 E2 F : Bool) :
    let z := (BitVec.ofNat 32 d - 1) >>> 31
    (((BitVec.ofNat 32 E1.toNat ||| BitVec.ofNat 32 E2.toNat) &&& (z ^^^ 1)) |||
      (z &&& BitVec.ofNat 32 F.toNat)).toNat =
      (if d = 0 then F else E1 || E2).toNat := by
  have bit : ((BitVec.ofNat 32 d - 1) >>> 31) = BitVec.ofNat 32 (decide (d = 0)).toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_zero d digit]
    cases decide (d = 0) <;> rfl
  dsimp only
  rw [bit, BitVec.and_comm (BitVec.ofNat 32 (decide (d = 0)).toNat), flag_bits]
  by_cases zero : d = 0 <;> simp only [zero, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]

end VG.Proof.MillerRabin.X86
