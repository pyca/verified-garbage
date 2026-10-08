import VerifiedGarbage.Proof.Seed.X86_64.KeyRound
import VerifiedGarbage.Proof.Seed.KeySchedule

/-!
# The sixteen rounds of the key schedule on x86-64

`keyRounds_ok`: after `n` rounds, `r10` and `r11` hold the key words of
round `n + 1` (`keyWords`), and the lanes of `G`'s first `2 * n` inputs hold
them (`gInput`).
-/

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64 VG.Proof.Seed

theorem hi_append (a b : BitVec 32) : ((a ++ b) >>> 32).setWidth 32 = a := by
  ext i hi
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  simp [show ¬ (32 + i < 32) by omega, hi]

theorem split64 (t : BitVec 64) : t.extractLsb' 32 32 ++ t.setWidth 32 = t := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  split <;> simp_all <;> (congr 1; omega)

theorem ror56 (t : BitVec 64) : t.rotateRight 56 = t.rotateLeft 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateLeft]

theorem kcs_eq : ∀ j < 16, kcs.getD j 0 = Spec.Seed.kc.getD j 0 := by decide

/-- The key words `k` as `r10` and `r11` hold them. -/
def kx (k : Quad) : BitVec 64 := k.1 ++ k.2.1
def ky (k : Quad) : BitVec 64 := k.2.2.1 ++ k.2.2.2

/-- After `n` rounds of the key schedule. -/
structure KeyInv (key : Spec.Seed.Block) (s₀ : State) (n : Nat) (s : State) : Prop where
  r10 : s.gpr .r10 = kx (keyWords key n)
  r11 : s.gpr .r11 = ky (keyWords key n)
  lanes : ∀ i < 2 * n, lv s (gSlot i) (i % 16) = gInput key i
  regs : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [arraysR s₀] s₀.mem s.mem

theorem keyRounds_ok (key : Spec.Seed.Block) {s₀ : State} (h : Room s₀)
    (h10 : s₀.gpr .r10 = kx (keyWords key 0)) (h11 : s₀.gpr .r11 = ky (keyWords key 0)) :
    ∀ n ≤ 16, ∃ s, runBlock isa ((List.range n).flatMap keyRound) s₀ = some s ∧ KeyInv key s₀ n s
  | 0, _ => ⟨s₀, runBlock_nil, h10, h11, fun i hi => by omega, fun _ _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨s, hs, inv⟩ := keyRounds_ok key h h10 h11 n (by omega)
    have r9 : s.gpr .r9 = s₀.gpr .r9 := inv.regs _ (by decide) (by decide) (by decide) (by decide)
    obtain ⟨s', hs', l0, l1, lk, r10', r11', regs', rd', wr', f'⟩ :=
      keyRound_ok (j := n) (by omega) (room_congr h r9 inv.wr)
    refine ⟨s', ?_, ⟨?_, ?_, fun i hi => ?_, fun r a b c d => ?_, by rw [rd', inv.rd], by rw [wr', inv.wr], ?_⟩⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact runBlock_trans hs hs'
    · rw [r10', inv.r10]
      simp only [keyWords, keyStep]
      split
      · simp only [kx]; exact (split64 _).symm
      · rfl
    · rw [r11', inv.r11]
      simp only [keyWords, keyStep]
      split
      · rfl
      · simp only [ky, ror56]; exact (split64 _).symm
    · have g0 : gInput key (2 * n) = (keyWords key n).1 + (keyWords key n).2.2.1 - Spec.Seed.kc.getD n 0 := by
        simp only [gInput, show 2 * n / 2 = n by omega, show 2 * n % 2 = 0 by omega, ite_true]
      have g1 : gInput key (2 * n + 1) =
          (keyWords key n).2.1 - (keyWords key n).2.2.2 + Spec.Seed.kc.getD n 0 := by
        simp only [gInput, show (2 * n + 1) / 2 = n by omega, show (2 * n + 1) % 2 = 1 by omega]
        rfl
      by_cases hi0 : i = 2 * n
      · subst hi0
        rw [l0, g0, gIn0, inv.r10, inv.r11, kx, ky, hi_append, hi_append, kcs_eq n (by omega)]
      by_cases hi1 : i = 2 * n + 1
      · subst hi1
        rw [l1, g1, gIn1, inv.r10, inv.r11, kx, ky, BitVec.setWidth_append_eq_right,
          BitVec.setWidth_append_eq_right, kcs_eq n (by omega)]
      · rw [lk _ (gSlot_mem i) _ (Nat.mod_lt _ (by decide)) (gIn_apart _ (by omega) _ (by omega) hi0)
          (gIn_apart _ (by omega) _ (by omega) hi1)]
        exact inv.lanes i (by omega)
    · rw [regs' r a b c d, inv.regs r a b c d]
    · have : arraysR s = arraysR s₀ := by simp only [arraysR, r9]
      rw [this] at f'
      exact inv.frame.trans f'

end VG.Proof.Seed.X86_64
