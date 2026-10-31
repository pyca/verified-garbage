module

public import VerifiedGarbage.TCB.VectorCrypto
public import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Framework.Mem

/-! # Byte packing in shared vector values -/

@[expose] public section
namespace VG.Proof.VectorCrypto
open VG.VectorCrypto

/-- Bit `r` of block `k` of `x ++ y`, blocks being `n` bits wide. -/
theorem getLsbD_append_block {w n : Nat} (x : BitVec w) (y : BitVec n) (k : Nat) {r : Nat}
    (hr : r < n) :
    (x ++ y).getLsbD (n * k + r) = if k = 0 then y.getLsbD r else x.getLsbD (n * (k - 1) + r) := by
  rw [BitVec.getLsbD_append]
  by_cases hk : k = 0
  · subst hk; simp [hr]
  · have h : n ≤ n * k := Nat.le_mul_of_pos_right n (by omega)
    simp only [hk, show ¬ n * k + r < n by omega, ↓reduceIte]
    exact congrArg _ (by rw [Nat.mul_sub_one, Nat.sub_add_comm h])

theorem getLsbD_ofVBytes (f : Nat → BitVec 8) {k r : Nat} (hk : k < 16) (hr : r < 8) :
    (ofVBytes f).getLsbD (8 * k + r) = (f k).getLsbD r := by
  simp only [ofVBytes, getLsbD_append_block _ _ _ hr]
  match k, hk with
  | 0, _ => ?_
  | 1, _ => ?_
  | 2, _ => ?_
  | 3, _ => ?_
  | 4, _ => ?_
  | 5, _ => ?_
  | 6, _ => ?_
  | 7, _ => ?_
  | 8, _ => ?_
  | 9, _ => ?_
  | 10, _ => ?_
  | 11, _ => ?_
  | 12, _ => ?_
  | 13, _ => ?_
  | 14, _ => ?_
  | 15, _ => ?_
  | _ + 16, h => exact absurd h (by omega)
  all_goals
    simp only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.mul_zero, Nat.zero_add]

theorem read_write16 (m : Mem) (p : Addr) (v : BitVec (8 * 16)) : (m.write p 16 v).read p 16 = v :=
  Mem.read_eq_of_bytes fun i hi => by
    simp only [Mem.write, Mem.sub_ofNat_toNat p (show i < 2 ^ 64 by omega), hi, ite_true]

end VG.Proof.VectorCrypto
