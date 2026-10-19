module

public import VerifiedGarbage.Proof.Bignum.X86.SparseLoop
public import VerifiedGarbage.Proof.Bignum.MontRepresentation
public import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath
public import VerifiedGarbage.Proof.Mont.X86.PowerStep

/-! # Safe execution for all packed values, RSA correctness for a valid stored R² -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.PublicContext

/-- The loop and the conversion out of Montgomery form, from any result `y`
and base `a` in Montgomery form. -/
theorem sparseTail_ok {n bytes m a y : Nat} {base : Addr} {s : State}
    (h : Context n m base bytes s) (hone : wordsVal s.mem base (slot n 4) n = 1)
    (hy : wordsVal s.mem base (slot n 7) n = y * 2 ^ (64 * n) % m)
    (hb : wordsVal s.mem base (slot n 6) n = a * 2 ^ (64 * n) % m) :
    WP isa (.seq (.loop (sparseRound n) .ne) (multiply n 7 7 4)) s fun t =>
      Context n m base bytes t ∧ wordsVal t.mem base (slot n 7) n < m ∧
      wordsVal t.mem base (slot n 7) n = y * a ^ val32 s.mem base 128 2 % m ∧
      Outs base (exponentRanges n) s.mem t.mem ∧ Keeps clob s t := by
  have cn : size n ≤ 2 ^ 64 := by have := h.size_le; have := h.scr.nowrap; omega
  refine WP.seq (WP.mono (sparseLoop_ok h hy hb) fun s₁ ⟨I, hz⟩ => ?_)
  have O₁ : wordsVal s₁.mem base (slot n 4) n = 1 := by rw [exponent_one I.mem cn, hone]
  refine WP.mono (multiply_ok I.context (o := 7) (a := 7) (b := 4)
    (by unfold operand; decide) (by unfold operand; decide) (by unfold operand; decide)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [O₁]; exact h.gt_one)) fun t ⟨ct, Kt, ltt, Vt⟩ => ⟨ct, ltt, ?_, ?_, ?_⟩
  · have v := VG.Proof.Dsa.mont_decode (A := wordsVal s₁.mem base (slot n 7) n)
      (out := wordsVal t.mem base (slot n 7) n) h.coprime
      (by rw [I.finished hz, Nat.mod_mod]) (by rw [Vt, O₁])
    rwa [Nat.mod_eq_of_lt ltt, Nat.mod_mod] at v
  · exact I.mem.trans (exponent_op Kt (.inr rfl))
  · exact I.keeps.trans (OpKeep.keeps Kt)

theorem precomputedExponent_ok {n bytes m : Nat} {base : Addr} {s : State}
    (h : Context n m base bytes s) (hone : wordsVal s.mem base (slot n 4) n = 1)
    (hr2 : wordsVal s.mem base (slot n 5) n < m) :
    WP isa (sparseExponentiate n) s fun t =>
      Context n m base bytes t ∧ wordsVal t.mem base (slot n 7) n < m ∧
      (wordsVal s.mem base (slot n 5) n = 2 ^ (128 * n) % m →
        wordsVal t.mem base (slot n 7) n =
          wordsVal s.mem base (slot n 6) n ^ val32 s.mem base 128 2 % m) ∧
      Outs base (exponentRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  have hm0 : 0 < m := by have := h.gt_one; omega
  unfold sparseExponentiate
  refine WP.seq (WP.mono (multiply_ok h (o := 7) (a := 5) (b := 4)
    (by unfold operand; decide) (by unfold operand; decide) (by unfold operand; decide)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [hone]; exact h.gt_one)) fun s₁ ⟨c₁, K₁, lt₁, V₁⟩ => ?_)
  have R₁ : wordsVal s₁.mem base (slot n 5) n = wordsVal s.mem base (slot n 5) n :=
    slot_value h (by unfold operand; decide) (by decide) (by decide) K₁
  have B₁ := slot_value h (i := 6) (by unfold operand; decide) (by decide) (by decide) K₁
  have E₁ := header_value (d := 128) (k := 2) (by decide) K₁
  have O₁ := slot_value h (i := 4) (by unfold operand; decide) (by decide) (by decide) K₁
  refine WP.seq (WP.mono (multiply_ok c₁ (o := 6) (a := 6) (b := 5)
    (by unfold operand; decide) (by unfold operand; decide) (by unfold operand; decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [R₁]; exact hr2))
    fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  have Y₂ : wordsVal s₂.mem base (slot n 7) n = wordsVal s₁.mem base (slot n 7) n :=
    slot_value c₁ (by unfold operand; decide) (by decide) (by decide) K₂
  have E₂ : val32 s₂.mem base 128 2 = val32 s.mem base 128 2 := by
    rw [header_value (by decide) K₂, E₁]
  have O₂ : wordsVal s₂.mem base (slot n 4) n = 1 := by
    rw [slot_value c₁ (by unfold operand; decide) (by decide) (by decide) K₂, O₁, hone]
  have frame (t : State) (O : Outs base (exponentRanges n) s₂.mem t.mem) (K : Keeps clob s₂ t) :
      Outs base (exponentRanges n) s.mem t.mem ∧ Keeps powerClob s t :=
    ⟨((exponent_op K₁ (.inr rfl)).trans (exponent_op K₂ (.inl rfl))).trans O,
      (((OpKeep.keeps K₁).trans (OpKeep.keeps K₂)).trans K).mono (by decide)⟩
  by_cases good : wordsVal s.mem base (slot n 5) n = 2 ^ (128 * n) % m
  · have Y : wordsVal s₂.mem base (slot n 7) n = 1 * 2 ^ (64 * n) % m := by
      rw [Y₂, Nat.one_mul]
      exact mont_one h.coprime lt₁ (by rw [V₁, hone, good, Nat.mul_one, Nat.mod_mod])
    have B : wordsVal s₂.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 6) n * 2 ^ (64 * n) % m :=
      mont_encode h.coprime lt₂ (by rw [V₂, R₁, B₁, good])
    refine WP.mono (sparseTail_ok c₂ O₂ Y B) fun t ⟨ct, lt, V, O, K⟩ => ?_
    refine ⟨ct, lt, fun _ => ?_, frame t O K⟩
    rw [V, E₂, Nat.one_mul]
  · obtain ⟨y, Y⟩ := VG.Proof.Bignum.mont_representation h.coprime
      (show wordsVal s₂.mem base (slot n 7) n < m by rw [Y₂]; exact lt₁)
    obtain ⟨b, B⟩ := VG.Proof.Bignum.mont_representation h.coprime lt₂
    refine WP.mono (sparseTail_ok c₂ O₂ Y B) fun t ⟨ct, lt, _, O, K⟩ =>
      ⟨ct, lt, fun g => absurd g good, frame t O K⟩

end VG.Proof.Bignum.X86.PublicContext
