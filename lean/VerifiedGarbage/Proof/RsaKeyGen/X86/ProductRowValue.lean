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
  have keep {d k : Nat} (lo : out ≤ d) (hi : d + 4 * k ≤ out + 4 * (left + right + 2))
      (sep : d + 4 * k ≤ 4 * i + out ∨ 4 * i + out + 4 * right + 8 ≤ d) :
      val32 m' base d k = val32 m base d k := by
    apply changed.val32 _ (by have := L.out_bound; omega)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := L.mult_out
      simp only
      omega
    · exact sep
  apply parts_add (i := i) (len := right + 2) (by omega)
  · exact keep (Nat.le_refl _) (by omega) (by omega)
  · exact keep (by omega) (by omega) (by omega)
  · simpa only [Nat.add_comm out (4 * i)] using value

end VG.Proof.RsaKeyGen.X86.Product
