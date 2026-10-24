module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.Ctx
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.RsaKeyGen

/-!
# The blinded Miller–Rabin loop on PPC64LE: constant time, the public data

Two runs of the loop are related as RSA's signature verification relates
them (`Proof/RsaPkcs1Sig/PPC64LE/Two.lean`): both satisfy the same predicate
for the same public data `BD` (the working space, the candidate, the tape and
the search's parameters, and the stack pointer), whatever else memory holds.
The candidate and the tape are public (DSA's primes are), so every branch and
address follows from them; the taint analysis checks the pieces whose
addresses and branches depend only on registers that the predicate fixes
(`two_taint`), and the predicate fixes the others from correctness.
`pins_env`: the working space's registers (`Env`) and the stack pointer.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE.Blinded

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Proof.MillerRabin.PPC64LE (Env)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Two Pins two_post two_taint two_ite)

/-- The public data of the loop. -/
structure BD where
  B : Addr
  R : Addr
  L : Nat
  w : Nat
  c : Nat
  rl : Nat
  t : Nat
  b : Nat
  ch : Nat
  r : Spec.RsaKeyGen.Rand
  sp : Addr

/-- The loop's context for the public data `a`. -/
def Ctx (a : BD) (s : State) : Prop :=
  BCtx s a.B a.L a.w a.c a.R a.rl a.t a.b a.ch ∧ Spec.Rsa.bytesAt s.mem a.R a.rl = a.r ∧ s.sp = a.sp

/-- A predicate that gives the working space's registers and the stack
pointer fixes them. -/
theorem pins_env {α : Type} {Φ : α → State → Prop} (f : α → BD)
    (h : ∀ a s, Φ a s → Env s (f a).B (8 * (f a).L) (f a).w ∧ s.sp = (f a).sp) :
    Pins Φ [.r10, .r11, .r29, .r31] := by
  intro a s₁ s₂ h₁ h₂
  obtain ⟨e₁, p₁⟩ := h a s₁ h₁
  obtain ⟨e₂, p₂⟩ := h a s₂ h₂
  refine ⟨p₁.trans p₂.symm, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [e₁.h10, e₂.h10]
  · rw [e₁.h11, e₂.h11]
  · rw [e₁.h29, e₂.h29]
  · rw [e₁.h31, e₂.h31]

/-- Pins of fewer registers. -/
theorem Pins.sub {α : Type} {Φ : α → State → Prop} {rs rs' : List Reg} (h : Pins Φ rs)
    (hs : ∀ r ∈ rs', r ∈ rs) : Pins Φ rs' := fun a s₁ s₂ h₁ h₂ =>
  ⟨(h a s₁ s₂ h₁ h₂).1, fun r hr => (h a s₁ s₂ h₁ h₂).2 r (hs r hr)⟩

/-- Pins of more registers, each fixed by the predicate. -/
theorem Pins.cons {α : Type} {Φ : α → State → Prop} {rs : List Reg} (h : Pins Φ rs) (r : Reg)
    (hr : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → s₁.gpr r = s₂.gpr r) : Pins Φ (r :: rs) := fun a s₁ s₂ h₁ h₂ =>
  ⟨(h a s₁ s₂ h₁ h₂).1, fun r' hr' => by
    rcases List.mem_cons.mp hr' with rfl | hr'
    · exact hr a s₁ s₂ h₁ h₂
    · exact (h a s₁ s₂ h₁ h₂).2 r' hr'⟩

/-- A predicate implied by one with pins has them. -/
theorem Pins.of_imp {α : Type} {Φ Ψ : α → State → Prop} {rs : List Reg} (h : Pins Φ rs)
    (hi : ∀ a s, Ψ a s → Φ a s) : Pins Ψ rs := fun a s₁ s₂ h₁ h₂ => h a s₁ s₂ (hi a s₁ h₁) (hi a s₂ h₂)

/-- Two runs related through a map of their public data. -/
theorem two_map {α β : Type} {Φ : α → State → Prop} {Ψ : β → State → Prop} (f : α → β)
    (hf : ∀ a s, Φ a s → Ψ (f a) s) {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Two Ψ) c Q) : RelCT isa (Two Φ) c Q :=
  h.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨f a, hf a _ h₁, hf a _ h₂⟩) fun _ _ h => h

end VG.Proof.MillerRabin.PPC64LE.Blinded
