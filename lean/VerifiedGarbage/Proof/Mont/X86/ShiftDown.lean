module

import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ExponentWord
public import VerifiedGarbage.Impl.Mont.X86.Exponent
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Shifting a number's words down by a bit, in a loop over its words

`shiftDown` computes what `shiftExponent` does: each word but the top one in
a loop, bringing in the next word's low bit, then the top word.
-/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86

/-- Words each shifted down by a bit, bringing in the next word's low bit
(zero for the top word), are the number halved. -/
theorem val32_halve (m m' : Mem) (base : Addr) : ∀ (k out : Nat),
    (∀ i < k, w32 m' base (out + 4 * i) = w32 m base (out + 4 * i) / 2 +
      2 ^ 31 * (if i + 1 = k then 0 else w32 m base (out + 4 * (i + 1)) % 2)) →
    val32 m' base out k = val32 m base out k / 2
  | 0, _, _ => by simp only [val32, Nat.zero_div]
  | k + 1, out, h => by
    have ih := val32_halve m m' base k (out + 4) fun i hi => by
      have e := h (i + 1) (by omega)
      rw [show out + 4 * (i + 1) = out + 4 + 4 * i by omega,
        show out + 4 * (i + 1 + 1) = out + 4 + 4 * (i + 1) by omega] at e
      rw [e]
      simp only [Nat.add_right_cancel_iff]
    have e := h 0 (by omega)
    rw [Nat.mul_zero, Nat.add_zero, show out + 4 * (0 + 1) = out + 4 by omega] at e
    rw [val32, val32, e, ih]
    cases k with
    | zero =>
      rw [ite_eq_left rfl]
      simp only [val32]
      omega
    | succ k =>
      rw [ite_eq_right (by omega), ← val32_parity m base (out + 4) k]
      omega

/-- The `k` words at `out` (`2 ≤ k`) halved. -/
theorem shiftDown_ok {s : State} {base : Addr} {size k out : Nat} (hs : Scr s base size)
    (hk : 2 ≤ k) (ho : out + 4 * k ≤ size) :
    WP isa (shiftDown k out) s fun t =>
      Outside base out (4 * k) s.mem t.mem ∧
      val32 t.mem base out k = val32 s.mem base out k / 2 ∧
      Keeps [.eax, .edx, .ebp] s t := by
  have hn := hs.nowrap
  unfold shiftDown
  refine WP.seq (wordLoop_ok (fun j t => Keeps [.eax, .edx, .ebp] s t ∧
      Outside base out (4 * j) s.mem t.mem ∧
      ∀ i < j, w32 t.mem base (out + 4 * i) =
        w32 s.mem base (out + 4 * i) / 2 + 2 ^ 31 * (w32 s.mem base (out + 4 * (i + 1)) % 2))
    (by omega) (by have := hs.size_lt; omega)
    (fun j u u' ⟨K, O, W⟩ ⟨hm, hr, hw, hg⟩ =>
      ⟨⟨fun r h => (hg r (by simp_all) (by simp_all)).trans (K.1 r h), hr.trans K.2.1, hw.trans K.2.2⟩,
        hm ▸ O, hm ▸ W⟩)
    ⟨Keeps.refl _ _, VG.Proof.Mont.Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    (fun j hj t ⟨K, O, W⟩ ej => ?_) (fun u ⟨K, O, W⟩ => ?_))
  · have ht := hs.of_keeps K (by decide)
    refine wp_movS (readSrc_at' ht ej (d := out + 4) (by omega)) fun s₁ u₁ _ => ?_
    refine wp_logicS (.inl rfl) rfl fun s₂ u₂ => ?_
    refine wp_ror (by decide) fun s₃ u₃ => ?_
    have k₃ : Keeps [.eax, .edx] t s₃ := ((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps
    have hs₃ := ht.of_keeps k₃ (by decide)
    have ej₃ : s₃.gpr .ebp = s₃.gpr .edi + BitVec.ofNat 32 (4 * j) := by
      rw [k₃.1 _ (by decide), k₃.1 _ (by decide)]; exact ej
    refine wp_movS (readSrc_at' hs₃ ej₃ (d := out) (by omega)) fun s₄ u₄ _ => ?_
    refine wp_shr (by decide) fun s₅ u₅ _ => ?_
    refine wp_addS rfl fun s₆ u₆ _ => ?_
    have k₆ : Keeps [.eax, .edx] t s₆ := ((k₃.widen u₄.keeps).widen u₅.keeps).widen u₆.keeps
    have hs₆ := ht.of_keeps k₆ (by decide)
    have ej₆ : s₆.gpr .ebp = s₆.gpr .edi + BitVec.ofNat 32 (4 * j) := by
      rw [k₆.1 _ (by decide), k₆.1 _ (by decide)]; exact ej
    have mem₆ : s₆.mem = t.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    refine wp_storeS (hs₆.ea_at' ej₆ (d := out) (by omega)) (hs₆.write (d := out + 4 * j) (n := 4) (by omega))
      fun s₇ m₇ => WP.block_nil ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · exact K.trans ((k₆.mono (by decide)).trans (m₇.keeps _))
    · rw [m₇.mem, mem₆]
      exact (O.mono (Nat.le_refl _) (by omega)).trans
        ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
    · intro i hi
      rw [m₇.mem, mem₆]
      by_cases hij : i < j
      · rw [(writeW32_outside t.mem base (d := out + 4 * j) _ (by omega)).w32 (by omega) (by omega)]
        exact W i hij
      · obtain rfl : i = j := by omega
        rw [w32_write_self, u₆.gpr, u₅.gpr, u₄.gpr, u₅.other .eax (by decide), u₄.other .eax (by decide),
          u₃.gpr, u₂.gpr, u₁.gpr, u₃.mem, u₂.mem, u₁.mem, ite_eq_left rfl, shifted_word,
          show out + 4 + 4 * i = out + 4 * (i + 1) by omega]
        change w32 t.mem base _ / 2 + 2 ^ 31 * (w32 t.mem base _ % 2) = _
        rw [O.w32 (d := out + 4 * i) (by omega) (by omega), O.w32 (d := out + 4 * (i + 1)) (by omega) (by omega)]
    · rw [m₇.gpr, k₆.1 _ (by decide)]
    · rw [m₇.gpr, k₆.1 _ (by decide)]
  · have hu := hs.of_keeps K (by decide)
    refine WP.mono (shiftWord_ok hu true (out := out + 4 * (k - 1)) (by omega) (fun h => nomatch h))
      fun t ⟨O₁, V₁, K₁⟩ => ⟨?_, ?_, K.trans (K₁.mono (by decide))⟩
    · exact (O.mono (Nat.le_refl _) (by omega)).trans (O₁.mono (by omega) (by omega))
    · refine val32_halve s.mem t.mem base k out fun i hi => ?_
      by_cases hik : i + 1 = k
      · obtain rfl : i = k - 1 := by omega
        rw [ite_eq_left hik, V₁, ite_eq_left rfl, O.w32 (d := out + 4 * (k - 1)) (by omega) (by omega)]
      · rw [ite_eq_right hik, O₁.w32 (d := out + 4 * i) (by omega) (by omega)]
        exact W i (by omega)

end VG.Proof.Mont.X86.Dynamic
