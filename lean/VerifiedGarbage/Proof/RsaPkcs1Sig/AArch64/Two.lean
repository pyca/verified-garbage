import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# Constant time by two runs on AArch64

As for x86-64's multiword arithmetic (`Proof/Bignum/X86_64/Mont.lean`): two
runs are related by `Two Φ` when both satisfy `Φ a` for the same public data
`a` (whatever their secrets). The pieces of code whose addresses and
branches depend only on the stack pointer and on registers that `Φ a` fixes
are checked by the taint analysis (`two_taint`); what each run satisfies
afterwards follows from correctness (`two_post`). Branches whose conditions
come from public data the taint analysis cannot track (it is loaded from
memory, or the result of a call) agree since `Φ a` fixes them (`two_ite`).
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64

open VG VG.AArch64

/-- Both runs satisfy `Φ a`, for the same `a`. -/
def Two {α : Type} (Φ : α → State → Prop) (s₁ s₂ : State) : Prop := ∃ a, Φ a s₁ ∧ Φ a s₂

theorem two_post {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two Φ) c fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨a, h₁, h₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw a s₁ h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw a s₂ h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, a, y₁, y₂⟩

/-- `Φ a` fixes the stack pointer and the registers `rs`. -/
def Pins {α : Type} (Φ : α → State → Prop) (rs : List Reg) : Prop :=
  ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem two_taint {α : Type} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (VG.AArch64.Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs rs) (fun _ _ ⟨a, h₁, h₂⟩ => by
    obtain ⟨hsp, hr⟩ := hpin a _ _ h₁ h₂
    exact ⟨hsp, fun r hr' => hr r (VG.AArch64.Taint.mem_ofRegs.mp hr')⟩) h

theorem two_map {α β : Type} {Φ : α → State → Prop} {Φ' : β → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (g : α → β) (h : ∀ a s, Φ a s → Φ' (g a) s) (hct : RelCT isa (Two Φ') c Q) :
    RelCT isa (Two Φ) c Q :=
  hct.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨g a, h _ _ h₁, h _ _ h₂⟩) fun _ _ h => h

theorem two_mono {α : Type} {Φ Φ' : α → State → Prop} (h : ∀ a s, Φ a s → Φ' a s) {s₁ s₂ : State}
    (hp : Two Φ s₁ s₂) : Two Φ' s₁ s₂ :=
  let ⟨a, h₁, h₂⟩ := hp; ⟨a, h a _ h₁, h a _ h₂⟩

/-- A branch whose condition `Φ a` fixes. -/
theorem two_ite {α : Type} {Φ : α → State → Prop} {cond : isa.Cond} {th el : Prog isa}
    {Q : State → State → Prop}
    (hc : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → isa.eval cond s₁ = isa.eval cond s₂)
    (ht : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some true) th Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some false) el Q) :
    RelCT isa (Two Φ) (.ite cond th el) Q := by
  refine RelCT.ite (fun _ _ ⟨a, h₁, h₂⟩ => hc a _ _ h₁ h₂) (ht.mono ?_ fun _ _ h => h) (he.mono ?_ fun _ _ h => h)
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩

/-- A frame allocating a buffer, its body from both allocated states. -/
theorem two_alloc {α : Type} {Φ : α → State → Prop} {bytes : Nat} {body : Prog isa}
    {R : State → State → Prop}
    (hb : RelCT isa (Two fun a u => ∃ s, Φ a s ∧ u = allocated bytes s) body R) :
    RelCT isa (Two Φ) (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True :=
  RelCT.alloc (hb.mono (fun _ _ ⟨s, t, ⟨a, h₁, h₂⟩, e₁, e₂⟩ => ⟨a, ⟨s, h₁, e₁⟩, t, h₂, e₂⟩) fun _ _ h => h)

end VG.Proof.RsaPkcs1Sig.AArch64
