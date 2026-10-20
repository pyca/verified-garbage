module
public import VerifiedGarbage.Impl.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # A constant in the working space, by a zeroing loop and its nonzero words (x86, 32-bit) -/

@[expose] public section

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Mont VG.Proof.Mont

theorem ite_of_pos {α : Type} {p : Prop} [Decidable p] {a b : α} (h : p) : (if p then a else b) = a := by
  simp only [h, ite_true]

theorem ite_of_neg {α : Type} {p : Prop} [Decidable p] {a b : α} (h : ¬p) : (if p then a else b) = b := by
  simp only [h, ite_false]

/-- The stores of `x`'s nonzero words, over zeros. -/
theorem constWords_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {o x k : Nat}
    (hk : o + 4 * k ≤ size) (hz : ∀ i < k, w32 s.mem base (o + 4 * i) = 0) :
    ∀ j ≤ k, WP isa (.block ((List.range j).flatMap fun i =>
      if x >>> (32 * i) % 2 ^ 32 = 0 then []
      else [.mov .eax (.imm (BitVec.ofNat 32 (x >>> (32 * i)))), .store (sc (o + 4 * i)) .eax])) s fun u =>
      (∀ i < k, w32 u.mem base (o + 4 * i) = if i < j then x >>> (32 * i) % 2 ^ 32 else 0) ∧
      Keeps [.eax] s u ∧ Outside base o (4 * k) s.mem u.mem
  | 0, _ => WP.block_nil ⟨fun i hi => by rw [ite_of_neg (Nat.not_lt_zero _)]; exact hz i hi, Keeps.refl _ _,
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | j + 1, hj => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (constWords_ok hs hk hz j (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
    by_cases h0 : x >>> (32 * j) % 2 ^ 32 = 0
    · rw [ite_of_pos h0]
      refine WP.block_nil ⟨fun i hi => ?_, k₁, O₁⟩
      rw [e₁ i hi]
      by_cases hij : i < j
      · rw [ite_of_pos hij, ite_of_pos (by omega)]
      · rw [ite_of_neg hij]
        by_cases hji : i = j
        · subst hji; rw [ite_of_pos (by omega), h0]
        · rw [ite_of_neg (by omega)]
    · rw [ite_of_neg h0]
      have hs₁ := hs.of_keeps k₁ (by decide)
      refine wp_movS rfl fun s₂ u₂ _ => ?_
      have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
      refine wp_storeS (hs₂.ea (d := o + 4 * j) (by omega)) (hs₂.write (d := o + 4 * j) (n := 4) (by omega))
        fun s₃ m₃ => WP.block_nil ?_
      have O₂ : Outside base (o + 4 * j) 4 s₁.mem s₃.mem := by
        rw [m₃.mem, u₂.mem]; exact writeW32_outside _ _ _ (by omega)
      refine ⟨fun i hi => ?_, (k₁.trans u₂.keeps).trans (m₃.keeps _),
        O₁.trans (O₂.mono (by omega) (by omega))⟩
      by_cases hji : i = j
      · subst hji
        rw [m₃.mem, u₂.mem, w32_write_self, u₂.gpr, BitVec.toNat_ofNat, ite_of_pos (by omega)]
      · rw [O₂.w32 (by omega) (by omega), e₁ i hi]
        by_cases hij : i < j
        · rw [ite_of_pos hij, ite_of_pos (by omega)]
        · rw [ite_of_neg hij, ite_of_neg (by omega)]

/-- `[o] = x` (`k` words), for `x < 2^(32k)`. -/
theorem setConstW_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {o k x : Nat}
    (hk0 : 0 < k) (hk : o + 4 * k ≤ size) (hx : x < 2 ^ (32 * k)) :
    WP isa (setConstW k o x) s fun u =>
      val32 u.mem base o k = x ∧ Keeps [.eax, .ebp, .edx] s u ∧ Outside base o (4 * k) s.mem u.mem := by
  have hn := hs.nowrap
  unfold setConstW
  refine WP.seq (WP.mono (zerosW_ok hs hk0 hk) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  have hz : ∀ i < k, w32 s₁.mem base (o + 4 * i) = 0 := by
    intro i hi
    have := val32_append s₁.mem base o i (k - i)
    rw [show i + (k - i) = k by omega, V₁, show k - i = (k - i - 1) + 1 by omega, val32] at this
    have : 2 ^ (32 * i) * (w32 s₁.mem base (o + 4 * i) + 2 ^ 32 * val32 s₁.mem base (o + 4 * i + 4) (k - i - 1)) = 0 := by
      omega
    rcases Nat.mul_eq_zero.mp this with h | h
    · exact absurd h (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
    · omega
  refine WP.mono (constWords_ok hs₁ hk hz k (Nat.le_refl _)) fun u ⟨e, K, O⟩ => ⟨?_, K₁.trans (K.mono (by decide)),
    O₁.trans O⟩
  exact VG.Proof.Weierstrass.X86.val32_of_shifts _ _ o k x hx fun j hj => by rw [e j hj, ite_of_pos hj]

end VG.Proof.Mont.X86
