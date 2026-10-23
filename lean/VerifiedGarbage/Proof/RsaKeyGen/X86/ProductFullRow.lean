module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Product
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductLayout
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductRow
import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductRowValue
import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductBounds
import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductControl

/-! # One complete public iteration of native RSA multiplication -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Product
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem row_ok {s : State} {base : Addr} {size left right out a b mult i : Nat}
    (hs : Scr s base size) (L : Layout size left right out a b mult)
    (index : i < left) (pointer : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (product : val32 s.mem base out (left + right + 2) = val32 s.mem base a i * val32 s.mem base b right) :
    WP isa (Impl.RsaKeyGen.X86.Product.row left right out a b mult) s fun t =>
      Outs base [(mult, 4), (out, 4 * (left + right + 2))] s.mem t.mem ∧
      val32 t.mem base out (left + right + 2) = val32 t.mem base a (i + 1) * val32 t.mem base b right ∧
      t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (i + 1)) ∧
      t.zf = some (decide (i + 1 = left)) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have hn := hs.nowrap
  have h64 : size ≤ 2 ^ 64 := by omega_arith
  have ha := L.a_bound
  have hb := L.b_bound
  have ho := L.out_bound
  have hm := L.mult_bound
  have sepB := L.b_out
  have sepM := L.mult_out
  have fits := row_fits (m := s.mem) (base := base) (by omega_arith) product
  have rowFits : val32 s.mem base (4 * i + out) (right + 2) +
      w32 s.mem base (4 * i + a) * val32 s.mem base b right < 2 ^ (32 * (right + 2)) := by
    simpa only [Nat.add_comm out (4 * i), Nat.add_comm a (4 * i)] using fits
  unfold Impl.RsaKeyGen.X86.Product.row
  refine WP.seq (WP.mono (accumulate_ok hs L.right_pos L.right_even pointer (by omega_arith) hb (by omega_arith) hm
    (by omega_arith) (by omega_arith) (by have := L.b_mult; omega_arith) rowFits) fun u ⟨O, V, K⟩ => ?_)
  have whole := L.row_add h64 index O V
  have O' := row_outside index O
  have A := L.a_preserved h64 (i + 1) (by omega_arith) O'
  have B := L.b_preserved h64 O'
  have value : val32 u.mem base out (left + right + 2) =
      val32 u.mem base a (i + 1) * val32 u.mem base b right := by
    rw [whole, product, A, B, val32_succ, Nat.add_mul, Nat.mul_assoc,
      Nat.add_comm a (4 * i)]
  have pu : u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [K.1 _ (by decide), K.1 _ (by decide), pointer]
  refine WP.mono (advance_ok pu index (by omega_arith)) fun t ⟨memory, pt, zt, Kt⟩ => ?_
  exact ⟨by rw [memory]; exact O', by rw [memory]; exact value, pt, zt,
    (K.mono (by decide)).trans (Kt.mono (by decide))⟩

end VG.Proof.RsaKeyGen.X86.Product
