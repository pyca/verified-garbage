module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductLayout
import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductWindow

/-! # The contribution of one native row to the complete product -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Product
open VG VG.Proof.Mont

theorem Layout.row_add {size left right out a b mult : Nat}
    (L : Layout size left right out a b mult) {m m' : Mem} {base : Addr} {i increment : Nat}
    (bound : size ≤ 2 ^ 64) (index : i < left)
    (changed : Outs base [(mult, 4), (4 * i + out, 4 * right + 8)] m m')
    (value : val32 m' base (4 * i + out) (right + 2) =
      val32 m base (4 * i + out) (right + 2) + increment) :
    val32 m' base out (left + right + 2) =
      val32 m base out (left + right + 2) + 2 ^ (32 * i) * increment := by
  apply window_add_with_scratch (i := i) (len := right + 2)
    (by have := L.out_bound; omega) (by omega) L.mult_out
  · simpa only [Nat.add_comm out (4 * i), Nat.mul_add, Nat.reduceMul] using changed
  · simpa only [Nat.add_comm out (4 * i)] using value

end VG.Proof.RsaKeyGen.X86.Product
