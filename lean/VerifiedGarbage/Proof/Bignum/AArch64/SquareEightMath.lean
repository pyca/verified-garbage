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

end VG.Proof.Bignum.AArch64.SquareEight
