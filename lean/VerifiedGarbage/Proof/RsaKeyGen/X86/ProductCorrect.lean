module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Product
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductLayout
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductFullRow
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Complete native integer multiplication for RSA key assembly

Both loop bounds depend only on the public operand widths. The result is
the ordinary integer product, with no modular reduction or truncation.
-/

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
