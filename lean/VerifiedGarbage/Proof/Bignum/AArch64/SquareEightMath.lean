module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
import VerifiedGarbage.Proof.Bignum.Triangular
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Eight-limb decomposition of a triangular square. The decomposition
uses the same target-independent triangular identities as the x86-64 tiles. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.Proof.Bignum
open VG.Proof.Bignum.AArch64.Square

theorem crossValue_add (m : Mem) (B : Addr) (e p q : Nat) :
    crossValue m B e (p + q) = crossValue m B e p +
      2 ^ (128 * p) * crossValue m B (e + 8 * p) q +
      2 ^ (64 * p) * wv m B e p * wv m B (e + 8 * p) q := by
  have shift : (fun i => (word m B (e + 8 * (p + i))).toNat) =
      (fun i => (word m B (e + 8 * p + 8 * i)).toNat) := by
    funext i
    rw [show e + 8 * (p + i) = e + 8 * p + 8 * i by omega]
  unfold crossValue
  rw [Triangular.cross_add, shift, value_words, value_words,
    ← Nat.pow_mul, ← Nat.pow_mul, show 64 * (2 * p) = 128 * p by omega]

def chunks (m : Mem) (B : Addr) (e j : Nat) : Nat := wv m B (e + 64 * j) 8

def blockCross (m : Mem) (B : Addr) (e : Nat) : Nat → Nat
 | 0 => 0
 | n + 1 => blockCross m B e n + 2 ^ (1024 * n) * crossValue m B (e + 64 * n) 8

theorem chunks_value (m : Mem) (B : Addr) (e n : Nat) :
    Square.value (2 ^ 512) (chunks m B e) n = wv m B e (8 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Square.value, ih, show 8 * (n + 1) = 8 * n + 8 by omega, wv_add,
      ← Nat.pow_mul 2 512 n]
    simp only [chunks, show 8 * (8 * n) = 64 * n by omega,
      show 64 * (8 * n) = 512 * n by omega]
    rw [Nat.mul_comm (wv m B (e + 64 * n) 8)]

private theorem sum_chunks {a c p d q x y : Nat} :
    (a + c) + p * d + q * x * y = (a + p * d) + (c + x * y * q) := by grind

/-- Within-tile cross products plus the products of distinct tiles are
exactly the cross products of the original 64-bit limbs. -/
theorem chunks_cross (m : Mem) (B : Addr) (e n : Nat) :
    crossValue m B e (8 * n) = blockCross m B e n +
      Square.cross (2 ^ 512) (chunks m B e) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 8 * (n + 1) = 8 * n + 8 by omega, crossValue_add, ih, blockCross,
      Square.cross, chunks_value, ← Nat.pow_mul 2 512 n]
    simp only [chunks, show 8 * (8 * n) = 64 * n by omega,
      show 128 * (8 * n) = 1024 * n by omega, show 64 * (8 * n) = 512 * n by omega]
    exact sum_chunks

end VG.Proof.Bignum.AArch64.SquareEight
