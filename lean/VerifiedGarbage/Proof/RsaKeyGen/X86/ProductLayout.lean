module

public import VerifiedGarbage.Proof.Mont.Words32

/-! # Layout of the native unreduced RSA product

The operands may coincide (squaring is permitted). The product and the
multiplier word cannot overlap either operand or each other.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Product
open VG VG.Proof.Mont

structure Layout (size left right out a b mult : Nat) : Prop where
  left_pos : 0 < left
  right_pos : 0 < right
  right_even : right % 2 = 0
  out_bound : out + 4 * (left + right + 2) ≤ size
  a_bound : a + 4 * left ≤ size
  b_bound : b + 4 * right ≤ size
  mult_bound : mult + 4 ≤ size
  a_out : a + 4 * left ≤ out ∨ out + 4 * (left + right + 2) ≤ a
  b_out : b + 4 * right ≤ out ∨ out + 4 * (left + right + 2) ≤ b
  mult_out : mult + 4 ≤ out ∨ out + 4 * (left + right + 2) ≤ mult
  a_mult : a + 4 * left ≤ mult ∨ mult + 4 ≤ a
  b_mult : b + 4 * right ≤ mult ∨ mult + 4 ≤ b

end VG.Proof.RsaKeyGen.X86.Product
