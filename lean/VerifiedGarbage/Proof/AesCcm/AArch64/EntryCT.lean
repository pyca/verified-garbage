import VerifiedGarbage.Proof.AesCcm.AArch64.Rel

/-!
# AES-CCM on AArch64: the arguments and the entry in two runs

Untrusted: everything here is checked by Lean. Two runs with the same public
arguments have the same public values (`args_two`). The entry loads `work`,
the tag length and `tag` from the stack, which the taint analysis takes as
secret (it reads memory): the block is split after the loads
(`Proof.AesGcm.AArch64.RelCT.block_split`), and the rest runs from `x9`,
`x10` and `x11`, which hold `work`, the tag length and `tag`, public, in both
runs (`entry_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.Taint VG.Impl.AesCcm.AArch64
open VG.Impl.AesGcm.AArch64 (save)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint save_ok)

/-- Two runs with the same public arguments: both from the public values of
the first. -/
theorem args_two {σ₁ σ₂ : State} (A₁ : Args (cxOf σ₁) (σ₁.gpr .x2) σ₁) (A₂ : Args (cxOf σ₂) (σ₂.gpr .x2) σ₂)
    (hq : onePub σ₁ σ₂) : Args (cxOf σ₁) (σ₁.gpr .x2) σ₁ ∧ Args (cxOf σ₁) (σ₁.gpr .x2) σ₂ := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have hcx : cxOf σ₂ = cxOf σ₁ := by
    simp only [cxOf, q0, q1, q3, q4, q5, q6, q7, qsp, qa 0 (by decide), qa 1 (by decide), qa 2 (by decide)]
  rw [hcx, ← q2] at A₂
  exact ⟨A₁, A₂⟩

/-- The entry in two runs. -/
theorem entry_rel {c : Cx} {N : Addr} {σ₁ σ₂ : State} (A₁ : Args c N σ₁) (A₂ : Args c N σ₂)
    (hq : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  have run : ∀ {σ : State}, Args c N σ →
      WP isa (.block (([.ldrSp .x9 16, .ldrSp .x10 8, .ldrSp .x11 0] : List Instr) ++ save .x9)) σ fun s' =>
        s'.gpr .x9 = c.W ∧ s'.gpr .x10 = BitVec.ofNat 64 c.tl ∧ s'.gpr .x11 = c.T ∧
        (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s'.gpr r = σ.gpr r) ∧ s'.sp = σ.sp := fun A =>
    WP.block_append (WP.mono (ldr_ok A) fun s₁ ⟨x9₁, x10₁, x11₁, g₁, sp₁, _, _, wr₁⟩ => by
      obtain ⟨s₂, run₂, g₂, sp₂, _, _, _⟩ := save_ok s₁ .x9 x9₁ (by rw [wr₁]; exact A.perm.w)
      exact WP.of_runBlock ⟨s₂, run₂, by rw [g₂, x9₁], by rw [g₂, x10₁], by rw [g₂, x11₁],
        fun r h h' h'' => by rw [g₂, g₁ r h h' h''], by rw [sp₂, sp₁]⟩)
  have qsp : σ₁.sp = σ₂.sp := by rw [A₁.sp, A₂.sp]
  show RelCT isa _ (.block (([.ldrSp .x9 16, .ldrSp .x10 8, .ldrSp .x11 0] : List Instr) ++ save .x9 ++ _)) _
  refine Proof.AesGcm.AArch64.RelCT.block_split (rel_seq (Proof.AesGcm.AArch64.RelCT.block_split
      (rel_seq (rel_taint [] qsp (by simp) ⟨_, by taint_decide⟩) (ldr_ok A₁) (ldr_ok A₂)
        fun τ₁ τ₂ ⟨x9₁, _, _, _, sp₁, _⟩ ⟨x9₂, _, _, _, sp₂, _⟩ => ?_))
    (run A₁) (run A₂) fun τ₁ τ₂ ⟨x9₁, x10₁, x11₁, g₁, sp₁⟩ ⟨x9₂, x10₂, x11₂, g₂, sp₂⟩ => ?_)
  · exact rel_taint [.x9] (by rw [sp₁, sp₂, qsp]) (by agree_tac [x9₁, x9₂]) ⟨_, by taint_decide⟩
  refine rel_taint [.x9, .x10, .x11, .x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] (by rw [sp₁, sp₂, qsp]) ?_
    ⟨_, by taint_decide⟩
  intro r hr
  by_cases h9 : r = .x9
  · subst h9; rw [x9₁, x9₂]
  by_cases h10 : r = .x10
  · subst h10; rw [x10₁, x10₂]
  by_cases h11 : r = .x11
  · subst h11; rw [x11₁, x11₂]
  rw [g₁ r h9 h10 h11, g₂ r h9 h10 h11]
  exact hq r (by simp only [List.mem_cons, List.not_mem_nil, or_false, h9, h10, h11, false_or] at hr ⊢; exact hr)

end VG.Proof.AesCcm.AArch64
