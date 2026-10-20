module

public import VerifiedGarbage.Impl.Bignum.X86.SparseExponent
import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ExponentWord
import VerifiedGarbage.Proof.Mont.X86.Ops
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Isa

/-! # The tests of the public exponent's low bit and of what is left of it -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.PublicContext

theorem sub0 (x : BitVec 32) : x - 0 = x := BitVec.sub_zero x

theorem bitTest_ok {s : State} {base : Addr} {bytes : Nat} (hs : Scr s base bytes)
    (hb : 128 + 4 ≤ bytes) :
    WP isa (.block bitTest) s fun t =>
      t.mem = s.mem ∧ Keeps [.ecx] s t ∧ t.zf = some (decide (w32 s.mem base 128 % 2 = 0)) := by
  unfold bitTest exponentOffset
  refine wp_movS (readSrc_sc hs hb) fun s₁ u₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₂ u₂ => ?_
  refine wp_cmpS rfl fun t ft zt => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [ft.mem, u₂.mem, u₁.mem]
  · exact ((u₁.keeps.trans (u₂.keeps)).trans (ft.keeps _))
  · rw [zt, u₂.gpr, u₁.gpr, ite_eq_left rfl, sub0]
    congr 1
    by_cases h : w32 s.mem base 128 % 2 = 0
    · rw [decide_eq_true h, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [lowBit_nat]
      exact h
    · rw [decide_eq_false h]
      apply beq_false_of_ne
      intro e
      have := congrArg BitVec.toNat e
      rw [lowBit_nat] at this
      exact h this

theorem exponentLeft_ok {s : State} {base : Addr} {bytes : Nat} (hs : Scr s base bytes)
    (hb : 128 + 8 ≤ bytes) :
    WP isa (.block exponentLeft) s fun t =>
      t.mem = s.mem ∧ Keeps [.eax] s t ∧ t.zf = some (decide (val32 s.mem base 128 2 = 0)) := by
  unfold exponentLeft exponentOffset
  refine wp_movS (readSrc_sc hs (by omega)) fun s₁ u₁ _ => ?_
  have hs₁ := hs.of_keeps u₁.keeps (by decide)
  refine wp_orS (readSrc_sc hs₁ (by omega)) fun s₂ u₂ => ?_
  refine wp_cmpS rfl fun t ft zt => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [ft.mem, u₂.mem, u₁.mem]
  · exact ((u₁.keeps.trans (u₂.keeps)).trans (ft.keeps _))
  · rw [zt, u₂.gpr, u₁.gpr, u₁.mem, sub0]
    congr 1
    have hv : val32 s.mem base 128 2 = w32 s.mem base 128 + 2 ^ 32 * w32 s.mem base (128 + 4) := by
      simp only [val32]; omega
    rw [hv]
    have key : (s.mem.readW (off base 128) 32 ||| s.mem.readW (off base (128 + 4)) 32) = 0 ↔
        w32 s.mem base 128 + 2 ^ 32 * w32 s.mem base (128 + 4) = 0 := by
      rw [show (0 : BitVec 32) = 0#32 from rfl, BitVec.or_eq_zero_iff]
      constructor
      · rintro ⟨h₁, h₂⟩
        simp only [w32, h₁, h₂, BitVec.toNat_zero]
      · intro z
        exact ⟨BitVec.eq_of_toNat_eq (by change w32 s.mem base 128 = 0; omega),
          BitVec.eq_of_toNat_eq (by change w32 s.mem base (128 + 4) = 0; omega)⟩
    exact Bool.eq_iff_iff.mpr (by rw [beq_iff_eq, decide_eq_true_iff]; exact key)

end VG.Proof.Bignum.X86.PublicContext
