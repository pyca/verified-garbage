import VerifiedGarbage.Proof.Seed.Sbox

/-!
# G, bit by bit

`getLsbD_g`: bit `tb` of byte `a'` of `G(x)` is the XOR, over the bytes `a`
of `x`, of bit `tb` of `S(x_a)` (`S0` for even `a`, `S1` for odd) where the
mask `m_{(a + a') mod 4}` has it (RFC 4269 §2.2).
-/

namespace VG.Proof.Seed

open VG VG.Spec.Seed

/-- Byte `a` of `x`, `X_a`. -/
def byteOf (x : Word) (a : Nat) : Byte := (x >>> (8 * a)).setWidth 8

/-- RFC 4269 §2.2's mask `m_k`. -/
def maskOf (k : Nat) : Byte :=
  match k with | 0 => m0 | 1 => m1 | 2 => m2 | _ => m3

/-- The S-box of byte `a`: `S0` for `X0` and `X2`, `S1` for `X1` and `X3`. -/
def sOf (a : Nat) (b : Byte) : Byte := (sTable (a % 2 == 1)).getD b.toNat 0

/-- `∑ₐ f a` over `a < 4`, as XOR. -/
def xor4 (f : Nat → Bool) : Bool := f 0 ^^ f 1 ^^ f 2 ^^ f 3

theorem getLsbD_byteOf (x : Word) {a t : Nat} (ht : t < 8) :
    (byteOf x a).getLsbD t = x.getLsbD (8 * a + t) := by
  simp only [byteOf, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, ht, decide_true,
    Bool.true_and]

theorem getLsbD_append4 (z3 z2 z1 z0 : Byte) {tb : Nat} (ht : tb < 8) :
    (z3 ++ z2 ++ z1 ++ z0).getLsbD (8 * 0 + tb) = z0.getLsbD tb ∧
    (z3 ++ z2 ++ z1 ++ z0).getLsbD (8 * 1 + tb) = z1.getLsbD tb ∧
    (z3 ++ z2 ++ z1 ++ z0).getLsbD (8 * 2 + tb) = z2.getLsbD tb ∧
    (z3 ++ z2 ++ z1 ++ z0).getLsbD (8 * 3 + tb) = z3.getLsbD tb := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [BitVec.getLsbD_append, ite_eq_left (by omega), Nat.mul_zero, Nat.zero_add]
  · rw [BitVec.getLsbD_append, ite_eq_right (by omega), BitVec.getLsbD_append, ite_eq_left (by omega),
      show 8 * 1 + tb - 8 = tb by omega]
  · rw [BitVec.getLsbD_append, ite_eq_right (by omega), BitVec.getLsbD_append, ite_eq_right (by omega),
      BitVec.getLsbD_append, ite_eq_left (by omega), show 8 * 2 + tb - 8 - 8 = tb by omega]
  · rw [BitVec.getLsbD_append, ite_eq_right (by omega), BitVec.getLsbD_append, ite_eq_right (by omega),
      BitVec.getLsbD_append, ite_eq_right (by omega), show 8 * 3 + tb - 8 - 8 - 8 = tb by omega]

theorem getLsbD_g (x : Word) {a' tb : Nat} (ha : a' < 4) (ht : tb < 8) :
    (g x).getLsbD (8 * a' + tb) =
      xor4 fun a => (sOf a (byteOf x a)).getLsbD tb && (maskOf ((a + a') % 4)).getLsbD tb := by
  have e0 : x.setWidth 8 = byteOf x 0 := by simp [byteOf]
  have e1 : (x >>> 8).setWidth 8 = byteOf x 1 := rfl
  have e2 : (x >>> 16).setWidth 8 = byteOf x 2 := rfl
  have e3 : (x >>> 24).setWidth 8 = byteOf x 3 := rfl
  have h4 := getLsbD_append4 (tb := tb)
  simp only [g, e0, e1, e2, e3, xor4, sOf, sTable]
  rcases (show a' = 0 ∨ a' = 1 ∨ a' = 2 ∨ a' = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [(h4 _ _ _ _ ht).1]; simp [maskOf]
  · rw [(h4 _ _ _ _ ht).2.1]; simp [maskOf]
  · rw [(h4 _ _ _ _ ht).2.2.1]; simp [maskOf]
  · rw [(h4 _ _ _ _ ht).2.2.2]; simp [maskOf]

end VG.Proof.Seed
