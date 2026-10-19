module

public import VerifiedGarbage.Impl.Bignum.X86.ExponentCheck
public import VerifiedGarbage.Proof.Bignum.ExponentTestMath
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Test the public exponent's upper bound, parity and lower bound -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem exponentBoundsTest_ok (s : State) :
    WP isa (.block exponentBoundsTest) s fun t =>
      t.zf = some (exponentBounds (s.gpr .ebx) (s.gpr .edx)) ∧
      t.mem = s.mem ∧ Keeps [.ebp, .eax] s t := by
  unfold exponentBoundsTest
  refine wp_movS rfl fun s1 a _ => ?_
  refine wp_shr (by decide) fun s2 b _ => ?_
  refine wp_movS rfl fun s3 c _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s4 d => ?_
  refine wp_logicS (.inr rfl) rfl fun s5 e => ?_
  refine wp_orS rfl fun s6 f => ?_
  refine wp_cmpS rfl fun t g z => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [z, f.gpr, e.other .ebp (by decide), d.other .ebp (by decide),
      c.other .ebp (by decide), b.gpr, a.gpr, e.gpr, d.gpr, c.gpr,
      b.other .ebx (by decide), a.other .ebx (by decide)]
    simp only [exponentBounds, ite_true, show AluOp.xor ≠ AluOp.and by decide,
      ite_false, BitVec.ofNat_eq_ofNat, BitVec.sub_zero]
  · rw [g.mem, f.mem, e.mem, d.mem, c.mem, b.mem, a.mem]
  · exact ((((((a.keeps.mono (by decide)).widen b.keeps).widen c.keeps).widen d.keeps).widen
      e.keeps).widen f.keeps).trans (g.keeps _)

theorem exponentOneTest_ok (s : State) :
    WP isa (.block exponentOneTest) s fun t =>
      t.zf = some (exponentIsOne (s.gpr .ebx) (s.gpr .edx)) ∧
      t.mem = s.mem ∧ Keeps [.ebp, .eax] s t := by
  unfold exponentOneTest
  refine wp_movS rfl fun s1 a _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s2 b => ?_
  refine wp_orS rfl fun s3 c => ?_
  refine wp_cmpS rfl fun t d z => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [z, c.gpr, b.gpr, a.gpr, b.other .edx (by decide), a.other .edx (by decide)]
    simp only [exponentIsOne, show AluOp.xor ≠ AluOp.and by decide,
      ite_false, BitVec.ofNat_eq_ofNat, BitVec.sub_zero]
  · rw [d.mem, c.mem, b.mem, a.mem]
  · exact (((a.keeps.mono (by decide)).widen b.keeps).widen c.keeps).trans (d.keeps _)

theorem exponentResult_ok (s : State) (b : Bool) :
    WP isa (exponentResult b) s fun t => t.gpr .eax = BitVec.ofNat 32 b.toNat ∧
      t.mem = s.mem ∧ Keeps [.ebp, .eax] s t := by
  unfold exponentResult
  refine wp_movS rfl fun t h _ => WP.block_nil ?_
  exact ⟨h.gpr, h.mem, h.keeps.mono (by decide)⟩

end VG.Proof.Bignum.X86
