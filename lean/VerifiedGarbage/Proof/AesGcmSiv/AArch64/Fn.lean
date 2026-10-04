import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Cmp

/-!
# AES-GCM-SIV on AArch64: the arguments and the entry

Untrusted: everything here is checked by Lean. The precondition `onePre`
gives the public arguments (`prmOf`), how they lie (`lay_of`) and what the
state may access (`perm_of`). `entry` saves our caller's registers at
`W + 128`, as AES-GCM does, and keeps the arguments in `x19`–`x26`
(`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (covers_of_mem covers_left SavedAt savedR save_ok savedMem_frame savedAt_save)

/-- The public arguments of a state. -/
def prmOf (s : State) : Prm where
  K := s.gpr .x0
  W := s.gpr .x7
  N := s.gpr .x2
  A := s.gpr .x3
  D := s.gpr .x5
  SP := s.sp
  R := (s.gpr .x1).toNat
  al := (s.gpr .x4).toNat
  n := (s.gpr .x6).toNat

theorem lay_of {s : State} (h : onePre s) : Lay (prmOf s) := by
  obtain ⟨_, _, d1, d2, d3, d4, d5, d6, d7, b1, b2, b3, b4, b5, hR⟩ := h
  exact ⟨b1, b5, b2, b3, b4, d2, d1, d4, d3, d6, d5, d7, hR, BitVec.isLt _, BitVec.isLt _⟩

theorem perm_of {s : State} (h : onePre s) : Perm (prmOf s) s := by
  obtain ⟨hrd, hwr, -⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .x0, 240⟩ : Region), ⟨s.gpr .x2, 12⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat⟩],
      Covers [r] (s.rd ++ s.wr) := fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region), ⟨s.gpr .x7, 4096⟩], Covers [r] s.wr :=
    fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨mrd _ List.mem_cons_self, mrd _ (List.mem_cons_of_mem _ List.mem_cons_self),
    mrd _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), mwr _ List.mem_cons_self,
    mwr _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- `entry`. -/
theorem entry_ok {s : State} (h : onePre s) :
    WP isa (.block entry) s fun s₁ => Env (prmOf s) s₁ ∧ SavedAt s₁.mem (prmOf s).W s ∧
      Frame [savedR (prmOf s).W] s.mem s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have P := perm_of h
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s .x7 (W := s.gpr .x7) rfl P.w2560
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.run ⟨_, by grun [], rfl⟩ fun s₂ hs₂ => ?_⟩)
  subst hs₂
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp only [sp_write]; rw [sp₁]; rfl,
    P.of_eq (by simp only [rd_write]; exact rd₁) (by simp only [wr_write]; exact wr₁)⟩, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [gpr_write, g₁, prmOf, ofNat_toNat64]; done)
  · simp only [mem_write]; rw [m₁]; exact savedAt_save _ _ _
  · simp only [mem_write]; rw [m₁]; exact savedMem_frame _ _ _
  · simp only [rd_write]; exact rd₁
  · simp only [wr_write]; exact wr₁

/-! ## Regions -/

/-- Proves that a region is disjoint from each of a list of regions: parts
of `W`, the data, or the key schedule. -/
macro "disj_tac" L:term : tactic => `(tactic| (
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true]
  repeat' apply And.intro
  all_goals first
    | (with_reducible refine Lay.w_w $L (.inl ?_) ?_ ?_) <;> decide
    | (with_reducible refine Lay.w_w $L (.inr ?_) ?_ ?_) <;> decide
    | (with_reducible refine Lay.d_w' $L ?_) <;> decide
    | (with_reducible refine (Lay.d_w' $L ?_).symm) <;> decide
    | (with_reducible refine Lay.k_w' $L ?_) <;> decide
    | (with_reducible refine Lay.n_w' $L ?_) <;> decide
    | (with_reducible refine Lay.a_w' $L ?_) <;> decide
    | with_reducible exact Lay.k_d $L
    | with_reducible exact Lay.n_d $L
    | with_reducible exact Lay.a_d $L
    | with_reducible exact (Lay.d_w $L).symm))

end VG.Proof.AesGcmSiv.AArch64
