module

public import VerifiedGarbage.Proof.Modes.X86_64.CfbFinal
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# CFB of a message's last piece on x86-64: in constant time

`cfbFinal_rel`: two runs of `cfbFinal a whole enc` whose public arguments
agree leak the same trace. The taint analysis cannot check the whole
function at once: the inlined functions save and restore the callee-saved
registers through memory that it forgets, so the public values `cfbFinal`
keeps there (the rest's address and length) would be secret after them.
Runs are related piece by piece instead (`Eq2`, from states the correctness
proof describes in each run): the frame is pushed and popped at `rsp`, the
same in both runs; each straight-line block and the XOR loop by the taint
analysis, from the registers the correctness proof pins to the same values
in both runs; and the inlined functions by their own constant-time proofs
(`relCT_inline`).
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.Impl.Modes.X86_64

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : State) (a b : State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : State) : Prop := True

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_regs {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa (Eq2 σ₁ σ₂) c TT := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s₁ s₂ h => by
    obtain ⟨rfl, rfl⟩ := h; exact Taint.agree_ofRegs hr) hc

/-- An empty block. -/
theorem rel_skip {σ₁ σ₂ : State} : RelCT isa (Eq2 σ₁ σ₂) (.block []) TT := by
  intro x y t₁ t₂ x' y' _ e₁ e₂
  cases e₁ with
  | block h₁ =>
    cases e₂ with
    | block h₂ =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂
      exact ⟨rfl, trivial⟩

/-- A frame pushed at the same `rsp` in both runs. -/
theorem rel_frame {rs : List Reg} {r : Reg} {k : Nat} {body : Prog isa} {σ₁ σ₂ : State}
    (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) (hb : RelCT isa (Eq2 (pushed rs σ₁) (pushed rs σ₂)) body TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.frame (.push rs) body (.pop r k)) TT :=
  RelCT.frame (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact hsp)
    (hb.mono (fun _ _ ⟨s₁, s₂, ⟨e₁, e₂⟩, hx, hy⟩ => by subst e₁ e₂; exact ⟨hx, hy⟩) fun _ _ h => h)

/-- Constant time, from runs related from any two states the precondition
holds in with the same public data. -/
theorem ct_of {pre : State → Prop} {pub : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, pre σ₁ → pre σ₂ → pub σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) c TT) : ConstantTime isa pre pub c :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ => (h s₁ s₂ h₁ h₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- Inlined verified code, constant time from its contract, narrowed in each
run to regions the run's permit. -/
theorem rel_inline {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {u₁ u₂ : State} {r₁ w₁ r₂ w₂ : List Region}
    (p₁ : k.pre (u₁.withRegions r₁ w₁)) (p₂ : k.pre (u₂.withRegions r₂ w₂))
    (hp : k.pub (u₁.withRegions r₁ w₁) (u₂.withRegions r₂ w₂))
    (c₁ : Covers (r₁ ++ w₁) (u₁.rd ++ u₁.wr)) (cw₁ : Covers w₁ u₁.wr)
    (c₂ : Covers (r₂ ++ w₂) (u₂.rd ++ u₂.wr)) (cw₂ : Covers w₂ u₂.wr) :
    RelCT isa (Eq2 u₁ u₂) c TT :=
  regionModel.relCT_inline (c := c) (Pre := k.pre) (Post := k.post) (Pub := k.pub)
    (fun s hs => let ⟨t, s', e, _, p⟩ := hv s hs; ⟨t, s', e, p⟩) hct fun x₁ x₂ ⟨e₁, e₂⟩ => by
      subst e₁ e₂; exact ⟨_, _, _, _, p₁, p₂, hp, c₁, cw₁, c₂, cw₂⟩

end VG.Proof.Modes.X86_64
