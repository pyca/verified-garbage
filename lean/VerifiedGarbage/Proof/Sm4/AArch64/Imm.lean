import VerifiedGarbage.Impl.Aes.AArch64.Linear
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# 64-bit constants on AArch64

`imm_ok`: `imm d v` (`movz` of the lowest halfword, then `movk` of each
other halfword that is not zero) leaves `v` in `d` and changes nothing
else.
-/

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64
open VG.Impl.Aes.AArch64 (imm half)

theorem getLsbD_half (v : BitVec 64) {k i : Nat} (hi : i < 16) :
    (half v k).getLsbD i = v.getLsbD (16 * k + i) := by
  simp [half, hi, Nat.add_comm]

theorem getLsbD_ffff {j : Nat} : (0xFFFF : BitVec 64).getLsbD j = decide (j < 16 ∧ j < 64) := by
  rw [show (0xFFFF : BitVec 64) = BitVec.ofNat 64 (2 ^ 16 - 1) from rfl, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]
  by_cases h : j < 64 <;> simp [h] <;> omega

/-- The bits of `movk d, #(half v k), lsl #16 k`. -/
theorem movk_bit (x v : BitVec 64) {k i : Nat} (hk : k < 4) (hi : i < 64) :
    ((x &&& ~~~((0xFFFF : BitVec 64) <<< (16 * k))) ||| ((half v k).setWidth 64 <<< (16 * k))).getLsbD i =
      if i / 16 = k then v.getLsbD i else x.getLsbD i := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, getLsbD_ffff, hi, decide_true, Bool.true_and]
  by_cases h : i / 16 = k
  · subst h
    have h1 : ¬ i < 16 * (i / 16) := by omega
    have h2 : i - 16 * (i / 16) < 16 := by omega
    rw [getLsbD_half v h2, show 16 * (i / 16) + (i - 16 * (i / 16)) = i by omega]
    simp [h1, h2, show i - 16 * (i / 16) < 64 by omega]
  · by_cases h1 : i < 16 * k
    · simp [h1, h]
    · have h2 : ¬ (i - 16 * k < 16) := by omega
      simp [h1, h2, h, BitVec.getLsbD_of_ge (half v k) (i - 16 * k) (by omega)]

theorem read_x'' (s : State) (r : Reg) : s.read .x r = s.gpr r := by
  simp only [State.read, BitVec.setWidth_eq]

/-- The `movk`s of the halfwords in `R`: the bits of the other halfwords stay. -/
theorem movks_ok (d : Reg) (v : BitVec 64) : ∀ (R : List Nat) (t : State), (∀ k ∈ R, k < 4) →
    (∀ i < 64, i / 16 ∉ R → (t.gpr d).getLsbD i = v.getLsbD i) →
    ∃ t', runBlock isa (R.map fun k => .movk .x d (half v k) k) t = some t' ∧ t'.gpr d = v ∧
      (∀ r, r ≠ d → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr
  | [], t, _, h => ⟨t, rfl, BitVec.eq_of_getLsbD_eq fun i hi => h i hi List.not_mem_nil, fun _ _ => rfl,
      rfl, rfl, rfl⟩
  | k :: R, t, hR, h => by
    have hk := hR k List.mem_cons_self
    let t₁ := t.write .x d ((t.read .x d &&& ~~~((0xFFFF : BitVec 64) <<< (16 * k))) |||
      ((half v k).setWidth 64 <<< (16 * k)))
    have e₁ : exec (.movk .x d (half v k) k) t = some t₁ := by
      simp only [exec, Size.bits, show 16 * k < 64 by omega, ite_true]; rfl
    have b₁ : ∀ i < 64, (t₁.gpr d).getLsbD i = if i / 16 = k then v.getLsbD i else (t.gpr d).getLsbD i := by
      intro i hi
      simp only [t₁, RegUpd.gpr_write_self, BitVec.setWidth_eq, read_x'']
      exact movk_bit _ _ hk hi
    obtain ⟨t', e', v', o', m', rd', wr'⟩ := movks_ok d v R t₁ (fun j hj => hR j (List.mem_cons_of_mem _ hj))
      (fun i hi hn => by
        rw [b₁ i hi]
        by_cases hik : i / 16 = k
        · simp [hik]
        · simp only [hik, ↓reduceIte]
          exact h i hi (by simp only [List.mem_cons, not_or]; exact ⟨hik, hn⟩))
    refine ⟨t', ?_, v', fun r hr => ?_, by rw [m']; rfl, by rw [rd']; rfl, by rw [wr']; rfl⟩
    · rw [List.map_cons, runBlock_cons, e₁, runStep_some, e']
    · rw [o' r hr]; exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- `imm d v` leaves `v` in `d`. -/
theorem imm_ok (s : State) (d : Reg) (v : BitVec 64) :
    ∃ s', runBlock isa (imm d v) s = some s' ∧ s'.gpr d = v ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let t₀ := s.write .x d ((half v 0).setWidth 64 <<< (16 * 0))
  have e₀ : exec (.movz .x d (half v 0) 0) s = some t₀ := by
    simp only [exec, Size.bits, show 16 * 0 < 64 by omega, ite_true]; rfl
  have b₀ : ∀ i < 64, (t₀.gpr d).getLsbD i = if i / 16 = 0 then v.getLsbD i else false := by
    intro i hi
    simp only [t₀, RegUpd.gpr_write_self, BitVec.setWidth_eq, Nat.mul_zero, BitVec.shiftLeft_zero,
      BitVec.getLsbD_setWidth]
    by_cases h : i / 16 = 0
    · rw [show i = 16 * 0 + i by omega, getLsbD_half v (by omega)]; simp [h, hi]
    · simp [h, BitVec.getLsbD_of_ge (half v 0) i (by omega)]
  obtain ⟨t', e', v', o', m', rd', wr'⟩ := movks_ok d v (([1, 2, 3] : List Nat).filter (half v · != 0)) t₀
    (fun k hk => by simp only [List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hk; omega)
    (fun i hi hn => by
      rw [b₀ i hi]
      by_cases h : i / 16 = 0
      · simp [h]
      · simp only [h, ↓reduceIte]
        have hz : half v (i / 16) = 0 := by
          simp only [List.mem_filter, List.mem_cons, List.not_mem_nil, or_false, bne_iff_ne, ne_eq,
            not_and, Decidable.not_not] at hn
          exact hn (by omega)
        rw [show i = 16 * (i / 16) + i % 16 by omega, ← getLsbD_half v (by omega), hz]; simp)
  refine ⟨t', ?_, v', fun r hr => ?_, by rw [m']; rfl, by rw [rd']; rfl, by rw [wr']; rfl⟩
  · simp only [imm, runBlock_cons, e₀, runStep_some]; exact e'
  · rw [o' r hr]; exact RegUpd.gpr_write_of_ne _ _ _ hr

end VG.Proof.Sm4.AArch64
