module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Product
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductLayout
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductWindow
import VerifiedGarbage.Proof.Mont.X86.Loop
import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductRow
import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductBounds
/-! # Complete native integer multiplication for RSA key assembly

Both loop bounds depend only on the public operand widths. The result is
the ordinary integer product, with no modular reduction or truncation.
-/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ProductRowValue.lean`, which only this module imported.
section

/-! # The contribution of one native row to the complete product -/

section
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
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ProductControl.lean`, which only this module imported.
section

/-! # Public control of the native RSA multiplication rows -/

section
namespace VG.Proof.RsaKeyGen.X86.Product
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86

theorem advance_ok {s : State} {i left : Nat}
    (pointer : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (index : i < left) (bound : 4 * left < 2 ^ 32) :
    WP isa (.block (Impl.RsaKeyGen.X86.Product.advance left)) s fun t =>
      t.mem = s.mem ∧
      t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (i + 1)) ∧
      t.zf = some (decide (i + 1 = left)) ∧
      Keeps [.ebp, .edx] s t := by
  unfold Impl.RsaKeyGen.X86.Product.advance
  refine wp_addS rfl fun u U _ => wp_movS rfl fun v V _ =>
    wp_addS rfl fun w W _ => wp_cmpS rfl fun t T z => WP.block_nil ?_
  have K : Keeps [.ebp, .edx] s t :=
    ((U.keeps.mono (by decide)).widen V.keeps).trans ((W.keeps.mono (by decide)).widen (T.keeps []))
  have P : t.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i) + 4 := by
    rw [T.gpr, W.other _ (by decide), V.other _ (by decide), U.gpr, pointer]
  have D : w.gpr .edx = s.gpr .edi + BitVec.ofNat 32 (4 * left) := by
    rw [W.gpr, V.gpr, U.other _ (by decide)]
  refine ⟨by rw [T.mem, W.mem, V.mem, U.mem], ?_, ?_, K⟩
  · rw [P, K.1 _ (by decide), row_ebp]
  · rw [z, W.other _ (by decide), V.other _ (by decide), U.gpr, pointer, D,
      row_zf _ index bound]

end VG.Proof.RsaKeyGen.X86.Product
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ProductFullRow.lean`, which only this module imported.
section

/-! # One complete public iteration of native RSA multiplication -/

section
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
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Product
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86

theorem correct {s : State} {base : Addr} {size left right out a b mult : Nat}
    (hs : Scr s base size) (L : Layout size left right out a b mult) :
    WP isa (Impl.RsaKeyGen.X86.Product.code left right out a b mult) s fun t =>
      Outs base [(mult, 4), (out, 4 * (left + right + 2))] s.mem t.mem ∧
      val32 t.mem base out (left + right + 2) = val32 s.mem base a left * val32 s.mem base b right ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have h64 : size ≤ 2 ^ 64 := by have := hs.nowrap; omega
  unfold Impl.RsaKeyGen.X86.Product.code
  refine WP.seq (WP.mono (zerosW_ok hs (by omega) L.out_bound) fun u ⟨O, zero, K⟩ => ?_)
  refine WP.seq (wp_movS rfl fun v V _ => WP.block_nil ?_)
  let I : Nat → State → Prop := fun i t =>
    Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
    Outs base [(mult, 4), (out, 4 * (left + right + 2))] s.mem t.mem ∧
    t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * i) ∧
    val32 t.mem base out (left + right + 2) = val32 t.mem base a i * val32 t.mem base b right
  have initial : I 0 v := by
    refine ⟨(K.mono (by decide)).trans (V.keeps.mono (by decide)), ?_, ?_, ?_⟩
    · rw [V.mem]
      exact Outs.of_outside O (by simp)
    · rw [V.gpr, V.other _ (by decide)]
      exact (BitVec.add_zero _).symm
    · rw [V.mem, zero]
      simp only [val32, Nat.zero_mul]
  refine WP.mono (WP.loop (M := isa) (Q := I left)
    (fun n t => ∃ i, n = left - i ∧ i < left ∧ I i t) ?_ left v
      ⟨0, by omega, L.left_pos, initial⟩) ?_
  · rintro n t ⟨i, rfl, hi, Kt, Ot, pt, value⟩
    have ht := hs.of_keeps Kt (by decide)
    refine WP.mono (row_ok ht L hi pt value) fun w ⟨Ow, valuew, pw, zw, Kw⟩ => ?_
    have next : I (i + 1) w := ⟨Kt.trans Kw, Ot.trans Ow, pw, valuew⟩
    by_cases last : i + 1 = left
    · exact .inl ⟨by simp only [eval, zw, last, decide_true, Option.map_some, Bool.not_true], last ▸ next⟩
    · exact .inr ⟨by simp only [eval, zw, decide_eq_false last, Option.map_some, Bool.not_false],
        left - (i + 1), by omega, i + 1, rfl, by omega, next⟩
  · intro t ⟨Kt, Ot, _, value⟩
    refine ⟨Ot, ?_, Kt⟩
    rw [value, L.a_preserved h64 left (Nat.le_refl _) Ot, L.b_preserved h64 Ot]

end VG.Proof.RsaKeyGen.X86.Product
