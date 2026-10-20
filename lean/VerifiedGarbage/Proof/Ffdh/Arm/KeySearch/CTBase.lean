module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! Relational proof helpers for native ARMv7 controller states sharing
public descriptors and stack pointers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm

/-- Both runs satisfy `Φ a`, for the same `a`, with the same stack pointer. -/
def Two {α : Type} (Φ : α → State → Prop) (s₁ s₂ : State) : Prop := ∃ a, Φ a s₁ ∧ Φ a s₂ ∧ s₁.sp = s₂.sp

theorem two_post {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two Φ) c fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨a, h₁, h₂, hsp⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw a s₁ h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw a s₂ h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, a, y₁, y₂, by rw [(Exec.rdwr e₁).2.2, (Exec.rdwr e₂).2.2, hsp]⟩

/-- `Φ a` fixes the registers `rs`. -/
def Pins {α : Type} (Φ : α → State → Prop) (rs : List Reg) : Prop :=
  ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem two_taint {α : Type} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint VG.Arm.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨a, h₁, h₂, _⟩ => Taint.agree_ofRegs (hpin a _ _ h₁ h₂)) h

/-- A piece checked by the taint analysis, with what correctness gives after it. -/
theorem two_piece {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint VG.Arm.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) : RelCT isa (Two Φ) c (Two Ψ) :=
  two_post (two_taint rs hpin h) hw

theorem two_map {α β : Type} {Φ : α → State → Prop} {Φ' : β → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (g : α → β) (h : ∀ a s, Φ a s → Φ' (g a) s) (hct : RelCT isa (Two Φ') c Q) :
    RelCT isa (Two Φ) c Q :=
  hct.mono (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨g a, h _ _ h₁, h _ _ h₂, hsp⟩) fun _ _ h => h

theorem two_mono {α : Type} {Φ Φ' : α → State → Prop} (h : ∀ a s, Φ a s → Φ' a s) {s₁ s₂ : State}
    (hp : Two Φ s₁ s₂) : Two Φ' s₁ s₂ :=
  let ⟨a, h₁, h₂, hsp⟩ := hp; ⟨a, h a _ h₁, h a _ h₂, hsp⟩

/-- A branch whose condition `Φ a` fixes. -/
theorem two_ite {α : Type} {Φ : α → State → Prop} {cond : isa.Cond} {th el : Prog isa}
    {Q : State → State → Prop}
    (hc : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → isa.eval cond s₁ = isa.eval cond s₂)
    (ht : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some true) th Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some false) el Q) :
    RelCT isa (Two Φ) (.ite cond th el) Q := by
  refine RelCT.ite (fun _ _ ⟨a, h₁, h₂, _⟩ => hc a _ _ h₁ h₂) (ht.mono ?_ fun _ _ h => h)
    (he.mono ?_ fun _ _ h => h)
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, ⟨h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩, hsp⟩
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, ⟨h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩, hsp⟩


end VG.Proof.Ffdh.Arm.KeySearch
