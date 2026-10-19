module
public import VerifiedGarbage.Proof.Bignum.X86.PublicBody
public import VerifiedGarbage.Proof.Mont.X86.PowerStep

import VerifiedGarbage.Proof.Bignum.X86.PublicLoopGeneral
import VerifiedGarbage.Proof.Bignum.MontRepresentation
import VerifiedGarbage.Proof.Bignum.X86.PublicMath
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ContextFrame

/-! # Precomputed exponentiation remains memory-safe for any reduced stored power -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.PublicContext

theorem precomputedExponent_safe {n bytes m : Nat} {base : Addr} {s : State}
    (h : Context n m base bytes s)
    (hone : wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 4) n = 1)
    (hr2 : wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 5) n < m) :
    WP isa (exponentiate n) s fun t =>
      Context n m base bytes t ∧ wordsVal t.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 7) n < m ∧
      Outs base (exponentRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  have cn : size n ≤ 2 ^ 64 := by have := h.size_le; have := h.scr.nowrap; omega
  unfold exponentiate
  refine WP.seq (WP.mono (multiply_ok h (o := 7) (a := 5) (b := 4)
    (by unfold operand; decide) (by unfold operand; decide) (by unfold operand; decide)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [hone]; exact h.gt_one)) fun s₁ ⟨c₁, K₁, lt₁, _⟩ => ?_)
  have R₁ : wordsVal s₁.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 5) n < m := by
    rw [slot_value h (by unfold operand; decide) (by decide) (by decide) K₁]
    exact hr2
  have O₁ := slot_value h (i := 4) (by unfold operand; decide) (by decide) (by decide) K₁
  refine WP.seq (WP.mono (multiply_ok c₁ (o := 6) (a := 6) (b := 5)
    (by unfold operand; decide) (by unfold operand; decide) (by unfold operand; decide)
    (by decide) (by decide) (by decide) (by decide) R₁) fun s₂ ⟨c₂, K₂, lt₂, _⟩ => ?_)
  have Y₂ : wordsVal s₂.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 7) n < m := by
    rw [slot_value c₁ (by unfold operand; decide) (by decide) (by decide) K₂]
    exact lt₁
  have O₂ : wordsVal s₂.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 4) n = 1 := by
    rw [slot_value c₁ (by unfold operand; decide) (by decide) (by decide) K₂, O₁, hone]
  obtain ⟨y, Y⟩ := mont_representation h.coprime Y₂
  obtain ⟨b, B⟩ := mont_representation h.coprime lt₂
  refine WP.seq (wp_movS rfl fun s₃ u₃ _ => WP.block_nil ?_)
  have c₃ : Context n m base bytes s₃ := ⟨c₂.scr.of_keeps u₃.keeps (by decide), c₂.size_le,
    u₃.mem ▸ c₂.mod, c₂.gt_one, u₃.mem ▸ c₂.inverse⟩
  refine WP.seq (WP.mono (exponentLoop_general c₃ (u₃.mem ▸ Y) (u₃.mem ▸ B) u₃.gpr)
    fun s₄ I => ?_)
  have O₄ : wordsVal s₄.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 4) n = 1 := by
    rw [exponent_one I.mem cn, u₃.mem, O₂]
  refine WP.mono (multiply_ok I.context (o := 7) (a := 7) (b := 4)
    (by unfold operand; decide) (by unfold operand; decide) (by unfold operand; decide)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [O₄]; exact h.gt_one)) fun t ⟨ct, Kt, ltt, _⟩ => ?_
  refine ⟨ct, ltt, ?_, ?_⟩
  · have o₁ := exponent_op K₁ (.inr rfl)
    have o₂ := exponent_op K₂ (.inl rfl)
    have o₃ : Outs base (exponentRanges n) s₂.mem s₃.mem := u₃.mem ▸ Outs.refl _ _ _
    exact (((o₁.trans o₂).trans o₃).trans I.mem).trans (exponent_op Kt (.inr rfl))
  · exact (((((OpKeep.keeps K₁).trans (OpKeep.keeps K₂)).mono (by decide)).widen u₃.keeps).trans
      I.keeps).trans ((OpKeep.keeps Kt).mono (by decide))

end VG.Proof.Bignum.X86.PublicContext
