module

public import VerifiedGarbage.Impl.Gcm.Clmul
public import VerifiedGarbage.TCB.VectorCrypto
public import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-! # Backend-independent reflected GHASH values -/

@[expose] public section
namespace VG.Proof.Gcm.Clmul

open VG.VectorCrypto
open VG.Impl.Gcm.Clmul (poly xInv2Hi)

/-- Doublewords in increasing significance, independent of register numbering. -/
def vdword (v : BitVec 128) (i : Nat) : BitVec 64 := v.extractLsb' (64 * i) 64

def ofVDwords (a b : BitVec 64) : BitVec 128 := b ++ a

theorem vdwords (v : BitVec 128) : v = vdword v 1 ++ vdword v 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 64
  · simp only [h, ↓reduceIte, decide_true, Nat.mul_zero, Nat.zero_add, Bool.true_and]
  · simp only [h, ite_false, decide_eq_true (show i - 64 < 64 by omega), Bool.true_and]
    exact congrArg _ (by omega)

theorem vdword_append_0 (a b : BitVec 64) : vdword (a ++ b) 0 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and, Nat.mul_zero, Nat.zero_add, ite_true]

theorem vdword_append_1 (a b : BitVec 64) : vdword (a ++ b) 1 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and, Nat.mul_one, show ¬ 64 + i < 64 by omega, ite_false, Nat.add_sub_cancel_left]

theorem vdword_xor (a b : BitVec 128) (e : Nat) : vdword (a ^^^ b) e = vdword a e ^^^ vdword b e := by
  simp only [vdword, BitVec.extractLsb'_xor]

/-! ## `ext #8` -/

/-- `ext d, n, m, #8`: the high half of `n`, then the low half of `m`. -/
def ext8 (n m : BitVec 128) : BitVec 128 := ((m ++ n) >>> 64).extractLsb' 0 128

theorem ext8_eq (n m : BitVec 128) : ext8 n m = vdword m 0 ++ vdword n 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [ext8, vdword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and, Nat.zero_add]
  by_cases h : i < 64
  · simp only [h, ite_true, show 64 + i < 128 by omega, decide_true, Bool.true_and]
  · simp only [h, ite_false, show ¬ 64 + i < 128 by omega, decide_eq_true (show i - 64 < 64 by omega),
      Bool.true_and]
    exact congrArg _ (by omega)

theorem vdword_ext8_0 (n m : BitVec 128) : vdword (ext8 n m) 0 = vdword n 1 := by
  rw [ext8_eq, vdword_append_0]

theorem vdword_ext8_1 (n m : BitVec 128) : vdword (ext8 n m) 1 = vdword m 0 := by
  rw [ext8_eq, vdword_append_1]

theorem ext8_ext8 (v : BitVec 128) : ext8 (ext8 v v) (ext8 v v) = v := by
  rw [ext8_eq (ext8 v v), vdword_ext8_0, vdword_ext8_1, ← vdwords]

/-! ## The product of two blocks, as 256 bits -/

/-- A 256-bit carry-less product, as its `lo`, `mid` and `hi` parts. -/
structure Prod where
  lo : BitVec 128
  mid : BitVec 128
  hi : BitVec 128

namespace Prod

/-- The four products of `acc`, of the block `a` as loaded and the key `t`
(`s` its halves swapped), added to `p`. -/
def acc (p : Prod) (a s t : BitVec 128) : Prod :=
  ⟨p.lo ^^^ polyMul (vdword a 1) (vdword s 1),
   p.mid ^^^ polyMul (vdword a 0) (vdword t 0) ^^^ polyMul (vdword a 1) (vdword t 1),
   p.hi ^^^ polyMul (vdword a 0) (vdword s 0)⟩

def zero : Prod := ⟨0, 0, 0⟩

end Prod

/-- The block, with its halves swapped, that `reduce` computes from a product:
`swap(hi ⊕ fold(u)) = swap(hi) ⊕ u ⊕ swap(pmull(u₀, 0xc2 · 2⁵⁶))` for
`u = mid ⊕ fold(lo)`. -/
def reduce (p : Prod) : BitVec 128 :=
  let u := (p.mid ^^^ ext8 p.lo p.lo) ^^^ polyMul (vdword p.lo 0) poly
  (ext8 p.hi p.hi ^^^ u) ^^^ ext8 (polyMul (vdword u 0) poly) (polyMul (vdword u 0) poly)

/-- The reduced product, in the block's loaded representation. -/
def mulV (a t : BitVec 128) : BitVec 128 := reduce (Prod.zero.acc a (ext8 t t) t)

theorem polyMul_zero_left (b : BitVec 64) : polyMul 0 b = 0 := by
  have h : ∀ xs : List Nat, xs.foldl (fun a _ => a) (0 : BitVec 128) = 0 := by
    intro xs; induction xs with
    | nil => rfl
    | cons x xs ih => exact ih
  simp only [polyMul, BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero, Bool.false_eq_true, ite_false]
  exact h _

/-- `x⁻²` (reflected). -/
def xInv2 : BitVec 128 := xInv2Hi ++ 3#64

/-! ## Loads and stores -/

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


theorem getLsbD_read (m : Mem) : ∀ (n : Nat) (a : Addr) (i : Nat), i < 8 * n →
    (m.read a n).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8)
  | 0, _, _, h => absurd h (by omega)
  | n + 1, a, i, h => by
    simp only [Mem.read, BitVec.getLsbD_append]
    by_cases hi : i < 8
    · simp [hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · simp only [hi, ite_false]
      rw [getLsbD_read m n (a + 1) (i - 8) (by omega)]
      have e1 : (i - 8) / 8 = i / 8 - 1 := by omega
      have e2 : (i - 8) % 8 = i % 8 := by omega
      rw [e1, e2]
      congr 2
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
      omega

theorem vdword_read16 (m : Mem) (p : Addr) {e : Nat} (he : e < 2) :
    VG.Proof.Gcm.Clmul.vdword (m.read p 16) e = m.readW (p + BitVec.ofNat 64 (8 * e)) 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [VG.Proof.Gcm.Clmul.vdword, Mem.readW, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hi,
    decide_true, Bool.true_and]
  rw [getLsbD_read m 16 p _ (by omega), getLsbD_read m 8 _ i (by omega), Offset.add_add,
    show 8 * e + i / 8 = (64 * e + i) / 8 by omega, show i % 8 = (64 * e + i) % 8 by omega]

theorem read_write16 (m : Mem) (p : Addr) (v : BitVec (8 * 16)) : (m.write p 16 v).read p 16 = v :=
  Mem.read_eq_of_bytes fun i hi => by
    simp only [Mem.write, Mem.sub_ofNat_toNat p (show i < 2 ^ 64 by omega), hi, ite_true]


end VG.Proof.Gcm.Clmul
