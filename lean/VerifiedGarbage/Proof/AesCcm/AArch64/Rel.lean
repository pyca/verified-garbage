import VerifiedGarbage.Proof.AesCcm.AArch64.Open
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel

/-!
# AES-CCM on AArch64: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs from given states (`Eq2 σ₁ σ₂`) piece by piece, as AES-GCM's
do (`Proof.AesGcm.AArch64.rel_seq`): the code between calls by the taint
analysis, from the registers the environment pins to the same public values
in both runs and those the correctness proofs pin (`rel_env`); each call by
its callee's proof (`rel_upd`, `Proof.AesGcm.AArch64.rel_ctr`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.Taint
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint)

/-- Two runs in the same environment agree on its registers. -/
theorem Env.agree {c : Cx} {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) :
    ∀ r ∈ envRegs, σ₁.gpr r = σ₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [E₁.x19, E₂.x19]
  · rw [E₁.x20, E₂.x20]
  · rw [E₁.x21, E₂.x21]
  · rw [E₁.x22, E₂.x22]
  · rw [E₁.x27, E₂.x27]
  · rw [E₁.x28, E₂.x28]

/-- Code the taint analysis checks, from the environment's registers and
`rs`, on which the two runs agree. -/
theorem rel_env {c : Cx} {code : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (E₁ : Env c σ₁) (E₂ : Env c σ₂)
    (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ rs)) code h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) code TT :=
  rel_taint (envRegs ++ rs) (by rw [E₁.sp, E₂.sp]) (fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact Env.agree E₁ E₂ r h
    · exact hr r h) hc

/-- A call of `vg_cmac_aes_update` with the same arguments in both runs. -/
theorem rel_upd (v : Proof.CmacAes.AArch64.UpdateImpl) {σ₁ σ₂ : State} {K C D S : Addr} {R n : Nat}
    (h₁ : Proof.CmacAes.Stream.AArch64.UArgs σ₁ K C D S R n) (h₂ : Proof.CmacAes.Stream.AArch64.UArgs σ₂ K C D S R n)
    (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) (.call v.callee.name v.callee.code) TT :=
  Proof.CmacAes.Stream.AArch64.upd_rel v _ fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨h₁, h₂, hsp⟩

/-- `a; (b; (c; (d; (e; f))))`, related as `(a; (b; (c; (d; e)))); f`. -/
theorem rel_assoc5 {P Q : State → State → Prop} {a b c d e f : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b (.seq c (.seq d e)))) f) Q) :
    RelCT isa P (.seq a (.seq b (.seq c (.seq d (.seq e f))))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with
    | seq d₁ e₁ => cases e₁ with | seq x₁ f₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with
    | seq d₂ e₂ => cases e₂ with | seq x₂ f₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ (.seq d₁ x₁)))) f₁)
    (.seq (.seq a₂ (.seq b₂ (.seq c₂ (.seq d₂ x₂)))) f₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

end VG.Proof.AesCcm.AArch64
