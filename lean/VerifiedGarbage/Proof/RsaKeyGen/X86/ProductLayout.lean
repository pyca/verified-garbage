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

theorem Layout.a_preserved {size left right out a b mult : Nat}
    (L : Layout size left right out a b mult) {m m' : Mem} {base : Addr}
    (bound : size ≤ 2 ^ 64) (i : Nat) (index : i ≤ left)
    (changed : Outs base [(mult, 4), (out, 4 * (left + right + 2))] m m') :
    val32 m' base a i = val32 m base a i := by
  apply changed.val32 _ (by have := L.a_bound; omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have := L.a_mult
    simp only
    omega
  · have := L.a_out
    simp only
    omega

theorem Layout.b_preserved {size left right out a b mult : Nat}
    (L : Layout size left right out a b mult) {m m' : Mem} {base : Addr}
    (bound : size ≤ 2 ^ 64)
    (changed : Outs base [(mult, 4), (out, 4 * (left + right + 2))] m m') :
    val32 m' base b right = val32 m base b right := by
  apply changed.val32 _ (by have := L.b_bound; omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact L.b_mult
  · exact L.b_out

theorem row_outside {m m' : Mem} {base : Addr} {left right out mult i : Nat}
    (index : i < left)
    (changed : Outs base [(mult, 4), (4 * i + out, 4 * right + 8)] m m') :
    Outs base [(mult, 4), (out, 4 * (left + right + 2))] m m' := by
  intro x hx
  apply changed x
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hx _ (List.mem_cons_self ..)
  · have H := hx (out, 4 * (left + right + 2)) (by simp)
    simp only at H ⊢
    omega

end VG.Proof.RsaKeyGen.X86.Product
