import VerifiedGarbage.Proof.Mont.X86.SparseStep

/-! # Carry and borrow chains for sparse x86 reduction -/
namespace VG.Proof.Mont.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

theorem sparseChain_succ (acc : Nat) (op op' : AluOp) (k : Nat) :
    sparseChain acc op op' (k + 1) = sparseChain acc op op' k ++
      sparseStep acc k (if k = 0 then op else op') (k == 0) := by
  simp only [sparseChain, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

theorem sparseChainAdd_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {acc i w : Nat} (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (hw : 4 * i + acc = w) :
    ∀ k, w + 4 * (k + 1) ≤ size →
    WP isa (.block (sparseChain acc .add .adc (k + 1))) s fun u =>
      Outside base w (4 * (k + 1)) s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ val32 u.mem base w (k + 1) + 2 ^ (32 * (k + 1)) * c.toNat =
        val32 s.mem base w (k + 1) + (s.gpr .ecx).toNat) ∧ Keeps [.eax] s u
  | 0, hb => by
    change WP isa (.block (sparseStep acc 0 .add true)) s _
    refine WP.mono (sparseStepAdd_ok hs (.inl ⟨rfl, rfl⟩) true hp (j := 0) (by omega))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ?_
    simp only [Nat.mul_zero, Nat.add_zero, hw, ite_true, Bool.toNat_false] at O V
    refine ⟨O, ⟨c, hc, ?_⟩, K⟩
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using V
  | k + 1, hb => by
    have hn := hs.nowrap
    rw [sparseChain_succ]
    simp only [Nat.add_one_ne_zero, ite_false, beq_eq_false_iff_ne.mpr (Nat.add_one_ne_zero k)]
    refine WP.block_append (WP.mono (sparseChainAdd_ok hs hp hw k (by omega))
      fun s₁ ⟨O₁, ⟨c₁, hc₁, V₁⟩, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    have hp₁ : s₁.gpr .ebp = s₁.gpr .edi + BitVec.ofNat 32 (4 * i) := by
      rw [K₁.1 _ (by decide), K₁.1 _ (by decide)]; exact hp
    refine WP.mono (sparseStepAdd_ok hs₁ (.inr ⟨rfl, hc₁⟩) false hp₁ (j := k + 1) (by omega))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ?_
    have he : 4 * i + (acc + 4 * (k + 1)) = w + 4 * (k + 1) := by omega
    rw [he] at O V
    simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at V
    rw [O₁.w32 (by omega) (by omega)] at V
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (O.mono (by omega) (by omega)),
      ⟨c, hc, ?_⟩, K₁.trans K⟩
    rw [val32_succ u.mem, val32_succ s.mem, O.val32 (by omega) (by omega), pow32_succ (k + 1)]
    generalize 2 ^ (32 * (k + 1)) = P at *
    grind

theorem sparseChainSub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {acc i w : Nat} (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (hw : 4 * i + acc = w) :
    ∀ k, w + 4 * (k + 1) ≤ size →
    WP isa (.block (sparseChain acc .sub .sbb (k + 1))) s fun u =>
      Outside base w (4 * (k + 1)) s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ val32 u.mem base w (k + 1) + (s.gpr .ecx).toNat =
        val32 s.mem base w (k + 1) + 2 ^ (32 * (k + 1)) * c.toNat) ∧ Keeps [.eax] s u
  | 0, hb => by
    change WP isa (.block (sparseStep acc 0 .sub true)) s _
    refine WP.mono (sparseStepSub_ok hs (.inl ⟨rfl, rfl⟩) true hp (j := 0) (by omega))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ?_
    simp only [Nat.mul_zero, Nat.add_zero, hw, ite_true, Bool.toNat_false] at O V
    refine ⟨O, ⟨c, hc, ?_⟩, K⟩
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using V
  | k + 1, hb => by
    have hn := hs.nowrap
    rw [sparseChain_succ]
    simp only [Nat.add_one_ne_zero, ite_false, beq_eq_false_iff_ne.mpr (Nat.add_one_ne_zero k)]
    refine WP.block_append (WP.mono (sparseChainSub_ok hs hp hw k (by omega))
      fun s₁ ⟨O₁, ⟨c₁, hc₁, V₁⟩, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    have hp₁ : s₁.gpr .ebp = s₁.gpr .edi + BitVec.ofNat 32 (4 * i) := by
      rw [K₁.1 _ (by decide), K₁.1 _ (by decide)]; exact hp
    refine WP.mono (sparseStepSub_ok hs₁ (.inr ⟨rfl, hc₁⟩) false hp₁ (j := k + 1) (by omega))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ?_
    have he : 4 * i + (acc + 4 * (k + 1)) = w + 4 * (k + 1) := by omega
    rw [he] at O V
    simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at V
    rw [O₁.w32 (by omega) (by omega)] at V
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (O.mono (by omega) (by omega)),
      ⟨c, hc, ?_⟩, K₁.trans K⟩
    rw [val32_succ u.mem, val32_succ s.mem, O.val32 (by omega) (by omega), pow32_succ (k + 1)]
    generalize 2 ^ (32 * (k + 1)) = P at *
    grind

end VG.Proof.Mont.X86
