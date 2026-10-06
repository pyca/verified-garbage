import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# RSAES-PKCS1-v1_5 on x86-64: a frame's trace

A function's frame leaks what its body does (`relCT_alloc`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64

theorem alloc_push {bytes : Nat} {s s₁ : State} (h : isa.push (.alloc bytes) s = some s₁) :
    s₁ = allocState bytes s := by
  simp only [isa, push] at h
  split at h
  · cases h; rfl
  · cases h

/-- A frame of `bytes` bytes leaks what its body does. -/
theorem relCT_alloc {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocState bytes s₁ ∧ b = allocState bytes s₂)
      body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain rfl := alloc_push p₁
      obtain rfl := alloc_push p₂
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      simp only [isa, push, pop] at p₁ q₁ p₂ q₂ ⊢
      exact ⟨rfl, trivial⟩

end VG.Proof.RsaPkcs1Enc.X86_64
