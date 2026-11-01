module

import VerifiedGarbage.Proof.AesCcm.RISCV64.Callee
public import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
public import VerifiedGarbage.Proof.AesCtr.RISCV64.Call
public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common

/-!
# AES-CCM on RISCV64: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs from given states (`Eq2 σ₁ σ₂`) piece by piece, as
AArch64's do (`Proof/AesCcm/AArch64/Rel.lean`): the code between calls by
the taint analysis, from the registers the environment pins to the same
public values in both runs and those the correctness proofs pin
(`rel_env`); each call by its callee's proof (`rel_upd`, `rel_ctr`). Between
pieces, what the next one needs of each run holds after every run of the
previous one (`Runs`): by its correctness proof (`Runs.of_wp`), or, for the
registers code without calls does not write, by its instructions alone
(`Runs.keep`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_taint)

/-- The registers the environment pins. -/
abbrev envRegs : List Reg := [.s1, .s2, .s3, .s4, .s9, .s10]

/-- Two runs in the same environment agree on its registers. -/
theorem Env.agree {c : Cx} {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) :
    ∀ r ∈ envRegs, σ₁.gpr r = σ₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [E₁.s1, E₂.s1]
  · rw [E₁.s2, E₂.s2]
  · rw [E₁.s3, E₂.s3]
  · rw [E₁.s4, E₂.s4]
  · rw [E₁.s9, E₂.s9]
  · rw [E₁.s10, E₂.s10]

/-- Code the taint analysis checks, from the environment's registers and
`rs`, on which the two runs agree. -/
theorem rel_env {c : Cx} {code : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (E₁ : Env c σ₁) (E₂ : Env c σ₂)
    (hsp : σ₁.sp = σ₂.sp) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ rs)) code h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) code TT :=
  let ⟨_, hc⟩ := hc
  rel_taint (envRegs ++ rs) hsp (fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact Env.agree E₁ E₂ r h
    · exact hr r h) hc

/-- A branch on whether a register is 0, on which the two runs agree. -/
theorem rel_iteZ {t e : Prog isa} {σ₁ σ₂ : State} {r : Reg} (hr : σ₁.gpr r = σ₂.gpr r)
    (ht : RelCT isa (Eq2 σ₁ σ₂) t TT) (he : RelCT isa (Eq2 σ₁ σ₂) e TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.ite (.zero r) t e) TT :=
  RelCT.ite (fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      rw [eval_zero, eval_zero, hr])
    (ht.mono (fun _ _ h => h.1) fun _ _ h => h) (he.mono (fun _ _ h => h.1) fun _ _ h => h)

/-! ## What every run leaves -/

/-- Every run of `c` from `s` ends in a state satisfying `F`. -/
def Runs (c : Prog isa) (s : State) (F : State → Prop) : Prop := ∀ t s', Exec isa c s t s' → F s'

theorem Runs.of_wp {c : Prog isa} {s : State} {F : State → Prop} (h : WP isa c s F) : Runs c s F :=
  fun _ _ he => by
    obtain ⟨_, _, he', hf⟩ := h
    obtain ⟨-, rfl⟩ := Exec.det he he'
    exact hf

theorem Runs.mono {c : Prog isa} {s : State} {F G : State → Prop} (h : Runs c s F) (hg : ∀ s', F s' → G s') :
    Runs c s G := fun _ _ he => hg _ (h _ _ he)

theorem Runs.and {c : Prog isa} {s : State} {F G : State → Prop} (hf : Runs c s F) (hg : Runs c s G) :
    Runs c s fun s' => F s' ∧ G s' := fun _ _ he => ⟨hf _ _ he, hg _ _ he⟩

/-- Code without calls whose instructions write only `rs` keeps the other
registers, the permissions and the stack pointer. -/
theorem Runs.keep {c : Prog isa} {s : State} (rs : List Reg) (hc : writesOnly rs c = true)
    (hn : c.noCalls = true := by decide +kernel) : Runs c s fun s' => Keep rs s s' ∧ s'.sp = s.sp := by
  intro t s' he
  refine ⟨⟨fun r hr => Exec.gpr (fun i hi => ?_) he (.inl hn), (Exec.rdwr he).1, (Exec.rdwr he).2.1⟩, Exec.sp he⟩
  unfold writesOnly at hc
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  have hh := hc i hi
  intro hd
  rw [hd] at hh
  exact hr (List.contains_iff_mem.mp hh)

/-- Pieces related as `(a; b); c` are related as `a; (b; c)`. -/
theorem rel_seqR {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : Runs c₁ σ₁ F₁) (w₂ : Runs c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ?_ ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨(h₁ _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1, w₁ _ _ e₁, w₂ _ _ e₂⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
    exact h₂ _ _ hp.1 hp.2 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

/-- Two runs from any states related by `P`, from those of each pair. -/
theorem rel_of_eq2 {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, P σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) c Q) : RelCT isa P c Q :=
  fun s₁ s₂ _ _ _ _ hp e₁ e₂ => h s₁ s₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

/-- What every run leaves, added to two related runs. -/
theorem rel_post {σ₁ σ₂ : State} {c : Prog isa} {F₁ F₂ : State → Prop} (h : RelCT isa (Eq2 σ₁ σ₂) c TT)
    (w₁ : Runs c σ₁ F₁) (w₂ : Runs c σ₂ F₂) : RelCT isa (Eq2 σ₁ σ₂) c fun a b => F₁ a ∧ F₂ b :=
  fun _ _ _ _ _ _ hp e₁ e₂ => by
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨(h _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1, w₁ _ _ e₁, w₂ _ _ e₂⟩

/-! ## The calls -/

/-- A call of `vg_cmac_aes_update` with the same arguments in both runs. -/
theorem rel_upd {σ₁ σ₂ : State} {K C D S : Addr} {R n : Nat}
    (h₁ : Proof.CmacAes.Stream.RISCV64.UArgs σ₁ K C D S R n) (h₂ : Proof.CmacAes.Stream.RISCV64.UArgs σ₂ K C D S R n)
    (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) Impl.CmacAes.Stream.RISCV64.updCall TT :=
  Proof.CmacAes.Stream.RISCV64.upd_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨h₁, h₂, hsp⟩

/-- A call of `vg_aes_ctr32` with the same arguments in both runs. -/
theorem rel_ctr {σ₁ σ₂ : State} {K C D S : Addr} {R n : Nat}
    (h₁ : Proof.AesCtr.RISCV64.CtrCall σ₁ K C D S R n) (h₂ : Proof.AesCtr.RISCV64.CtrCall σ₂ K C D S R n)
    (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) Impl.AesCtr.RISCV64.ctrCall TT :=
  Proof.AesCtr.RISCV64.ctr_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨h₁, h₂, hsp⟩

/-- After a call of `vg_cmac_aes_update`: the environment and our registers. -/
theorem upd_runs {c : Cx} {s : State} {K C D S : Addr} {R n : Nat} (E : Env c s)
    (h : Proof.CmacAes.Stream.RISCV64.UArgs s K C D S R n) :
    Runs Impl.CmacAes.Stream.RISCV64.updCall s fun s' => Env c s' ∧ s'.sp = s.sp ∧
      ∀ r ∈ [Reg.s5, .s6, .s7, .s8], s'.gpr r = s.gpr r :=
  Runs.of_wp (WP.mono (Proof.CmacAes.Stream.RISCV64.upd_call h) fun _ U =>
    ⟨E.of_pk (PK.ofSaved U.rd U.wr U.sp U.saved), U.sp, fun r hr => U.saved r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)⟩)

/-- After a call of `vg_aes_ctr32`: the environment and our registers. -/
theorem ctr_runs {c : Cx} {s : State} {K C D S : Addr} {R n : Nat} (E : Env c s)
    (h : Proof.AesCtr.RISCV64.CtrCall s K C D S R n) :
    Runs Impl.AesCtr.RISCV64.ctrCall s fun s' => Env c s' ∧ s'.sp = s.sp ∧
      ∀ r ∈ [Reg.s5, .s6, .s7, .s8], s'.gpr r = s.gpr r :=
  Runs.of_wp (WP.mono (Proof.AesCtr.RISCV64.ctr_call h) fun _ U =>
    ⟨E.of_pk (PK.ofSaved U.rd U.wr U.sp U.saved), U.sp, fun r hr => U.saved r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)⟩)

end VG.Proof.AesCcm.RISCV64
