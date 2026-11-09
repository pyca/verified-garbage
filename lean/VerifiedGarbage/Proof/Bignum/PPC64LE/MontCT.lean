module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFn
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFn
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Mont.Words32

/-!
# Montgomery multiplication on PPC64LE: constant time

The taint analysis treats memory as secret, so the bases loaded from the
header are secret to it although they are public. Two runs are related by
`Two Φ` when both satisfy `Φ d` for the same public data `d`, with the same
stack pointer; each piece of `mul` is checked by the taint analysis from the
registers that `Φ d` fixes (`two_taint`), and what each run satisfies after
it follows from correctness (`two_post`): after `args` the addresses of the
header's words, after `loads` the bases, `w` and the counter, and the scratch
buffer's address throughout.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Impl.Bignum.PPC64LE VG.Impl.Bignum

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
    {hc : VG.Taint.Hint T} (h : (taint.check (ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taint) (ofRegs rs)
    (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨hsp, fun r hr => hpin a _ _ h₁ h₂ r (RegSet.mem_ofList.mp hr)⟩) h

end VG.Proof.Bignum.PPC64LE
