module

public import VerifiedGarbage.Impl.Bignum.X86.SparseExponent
public import VerifiedGarbage.Proof.Bignum.X86.PublicBody
public import VerifiedGarbage.Proof.Mont.X86.ExponentWord

/-! # One iteration of the exponentiation that skips the products of clear bits -/

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

theorem sparseRound_ok {n bytes m y b : Nat} {base : Addr} {s : State}
    (h : Context n m base bytes s)
    (hy : wordsVal s.mem base (slot n 7) n = y * 2 ^ (64 * n) % m)
    (hb : wordsVal s.mem base (slot n 6) n = b * 2 ^ (64 * n) % m) :
    WP isa (sparseRound n) s fun t =>
      Context n m base bytes t ∧
      wordsVal t.mem base (slot n 7) n =
        (if val32 s.mem base 128 2 % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m ∧
      wordsVal t.mem base (slot n 6) n = (b * b) * 2 ^ (64 * n) % m ∧
      val32 t.mem base 128 2 = val32 s.mem base 128 2 / 2 ∧
      t.zf = some (decide (val32 s.mem base 128 2 / 2 = 0)) ∧
      Outs base (exponentRanges n) s.mem t.mem ∧ Keeps clob s t := by
  have sz := h.size_le
  have nw := h.scr.nowrap
  have cn : size n ≤ 2 ^ 64 := by omega
  have header := slot_header n 8
  have expBound : 128 + 4 * 2 ≤ bytes := by change slot n 8 ≤ bytes at sz; omega
  have hm0 : 0 < m := by have := h.gt_one; omega
  have lt6 : wordsVal s.mem base (slot n 6) n < m := by rw [hb]; exact Nat.mod_lt _ hm0
  have o₇ : Outs base (exponentRanges n) s.mem s.mem := Outs.refl _ _ _
  -- The product of a set bit, in place: `y` becomes `y * b`, or stays.
  have product : WP isa (sparseProduct n) s fun u =>
      Context n m base bytes u ∧
      wordsVal u.mem base (slot n 7) n =
        (if val32 s.mem base 128 2 % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m ∧
      wordsVal u.mem base (slot n 6) n = wordsVal s.mem base (slot n 6) n ∧
      val32 u.mem base 128 2 = val32 s.mem base 128 2 ∧
      Outs base (exponentRanges n) s.mem u.mem ∧ Keeps clob s u := by
    unfold sparseProduct
    refine WP.seq (WP.mono (bitTest_ok h.scr (by omega)) fun s₁ ⟨M₁, K₁, Z₁⟩ => ?_)
    have c₁ : Context n m base bytes s₁ := ⟨h.scr.of_keeps K₁ (by decide), h.size_le,
      M₁ ▸ h.mod, h.gt_one, M₁ ▸ h.inverse⟩
    have par : val32 s.mem base 128 2 % 2 = w32 s.mem base 128 % 2 := val32_parity _ _ _ _
    by_cases bit : w32 s.mem base 128 % 2 = 0
    · refine WP.ite true (by change s₁.zf = _; rw [Z₁, decide_eq_true bit]) (fun _ => WP.block_nil ?_)
        (fun e => nomatch e)
      refine ⟨c₁, ?_, by rw [M₁], by rw [M₁], by rw [M₁]; exact o₇, K₁.mono (by decide)⟩
      rw [M₁, hy, ite_eq_right (by omega)]
    · refine WP.ite false (by change s₁.zf = _; rw [Z₁, decide_eq_false bit]) (fun e => nomatch e)
        (fun _ => ?_)
      refine WP.mono (multiply_ok c₁ (o := 7) (a := 7) (b := 6)
        (by unfold operand; decide) (by unfold operand; decide) (by unfold operand; decide)
        (by decide) (by decide) (by decide) (by decide) (by rw [M₁]; exact lt6))
        fun u ⟨c₂, K₂, lt₂, V₂⟩ => ⟨c₂, ?_, ?_, ?_, ?_, ?_⟩
      · rw [ite_eq_left (by omega)]
        have v := VG.Proof.Dsa.mont_product h.coprime (a := y) (b := b)
          (by rw [M₁, hy, Nat.mod_mod]) (by rw [M₁, hb, Nat.mod_mod]) V₂
        rwa [Nat.mod_eq_of_lt lt₂] at v
      · rw [slot_value c₁ (by unfold operand; decide) (by decide) (by decide) K₂, M₁]
      · rw [header_value (by decide) K₂, M₁]
      · exact M₁ ▸ exponent_op K₂ (.inr rfl)
      · exact (K₁.mono (by decide)).trans (OpKeep.keeps K₂)
  unfold sparseRound
  refine WP.seq (WP.mono product fun s₁ ⟨c₁, Y₁, B₁, E₁, O₁, K₁⟩ => ?_)
  refine WP.seq (WP.mono (multiply_ok c₁ (o := 6) (a := 6) (b := 6)
    (by unfold operand; decide) (by unfold operand; decide) (by unfold operand; decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [B₁]; exact lt6))
    fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  have B₂ : wordsVal s₂.mem base (slot n 6) n = (b * b) * 2 ^ (64 * n) % m := by
    have v := VG.Proof.Dsa.mont_product h.coprime (a := b) (b := b)
      (by rw [B₁, hb, Nat.mod_mod]) (by rw [B₁, hb, Nat.mod_mod]) V₂
    rwa [Nat.mod_eq_of_lt lt₂] at v
  have Y₂ : wordsVal s₂.mem base (slot n 7) n = wordsVal s₁.mem base (slot n 7) n :=
    slot_value c₁ (by unfold operand; decide) (by decide) (by decide) K₂
  have E₂ : val32 s₂.mem base 128 2 = val32 s₁.mem base 128 2 := header_value (by decide) K₂
  refine WP.block_append (WP.mono (shiftExponent_ok c₂.scr 2 128 expBound) fun s₃ ⟨O₃, E₃, K₃⟩ => ?_)
  have c₃ := c₂.outside_keep K₃ (by decide) (by decide) O₃ (.inr (by have := slot_header n 0; omega)) (by decide)
  refine WP.mono (exponentLeft_ok c₃.scr expBound) fun t ⟨M₄, K₄, Z₄⟩ => ?_
  have c₄ : Context n m base bytes t := ⟨c₃.scr.of_keeps K₄ (by decide), c₃.size_le,
    M₄ ▸ c₃.mod, c₃.gt_one, M₄ ▸ c₃.inverse⟩
  have E : val32 s₃.mem base 128 2 = val32 s.mem base 128 2 / 2 := by rw [E₃, E₂, E₁]
  have h6 := slot_header n 6
  have h7 := slot_header n 7
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  have b7 := slot_bound (n := n) (i := 7) (by decide)
  refine ⟨c₄, ?_, ?_, by rw [M₄, E], by rw [Z₄, E], ?_, ?_⟩
  · rw [M₄, wordsVal_eq_val32, O₃.val32 (by omega) (by unfold stride at b7; omega),
      ← wordsVal_eq_val32, Y₂, Y₁]
  · rw [M₄, wordsVal_eq_val32, O₃.val32 (by omega) (by unfold stride at b6; omega),
      ← wordsVal_eq_val32, B₂]
  · have o₂ : Outs base (exponentRanges n) s₁.mem s₂.mem := exponent_op K₂ (.inl rfl)
    rw [M₄]
    exact (O₁.trans o₂).trans (Outs.of_outside O₃ (by simp [exponentRanges]))
  · exact (((K₁.trans (OpKeep.keeps K₂)).trans (K₃.mono (by decide))).trans (K₄.mono (by decide)))

end VG.Proof.Bignum.X86.PublicContext
