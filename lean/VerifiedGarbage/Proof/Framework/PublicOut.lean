module

public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Framework.PostMono
import VerifiedGarbage.Proof.Framework.Semantics

-- separate module: every function with public outputs (`Api.publicOut`) shares it

/-!
# Public outputs (`Api.publicOut`)

A function's public outputs are equal in two runs that agree on what is public
(`PublicOut.Of`). It is proven from a postcondition (`post'`) that says enough of
them: that determines them, in a run, from what the two runs agree on. That
postcondition, of the code as it is emitted, is stronger than the contract's,
which it implies (`VerifiedScrubbed.post_mono`).
-/

@[expose] public section

namespace VG

/-- The public outputs `o` of code that meets a contract with the postcondition `post'`,
if it determines them. -/
theorem PublicOut.of_post {T : Target} {c : Prog T.isa} {A : Abi T.isa} {sig : Sig} {o : PublicOut sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)} {post post' : sig.Post A.ptrBits}
    {writeArgs : Bool} {stack : Nat} {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (h : Verified T c (sig.contract A pre post' writeArgs stack leak))
    (ho : ∀ vals, A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) = some vals → ∀ s₁ s₂ s₁' s₂',
      (sig.contract A pre post writeArgs stack leak).pre s₁ →
      (sig.contract A pre post writeArgs stack leak).pre s₂ →
      (sig.contract A pre post writeArgs stack leak).pub s₁ s₂ →
      Curry.apply _ (o.given A.ptrBits) (vals s₁) (A.mem s₁) =
        Curry.apply _ (o.given A.ptrBits) (vals s₂) (A.mem s₂) →
      Curry.apply _ post' (vals s₁) (A.mem s₁) (A.mem s₁') ((A.ret s₁').setWidth _) →
      Curry.apply _ post' (vals s₂) (A.mem s₂) (A.mem s₂') ((A.ret s₂').setWidth _) →
      Curry.apply _ (o.out A.ptrBits) (vals s₁) (A.mem s₁) (A.mem s₁') ((A.ret s₁').setWidth _) =
        Curry.apply _ (o.out A.ptrBits) (vals s₂) (A.mem s₂) (A.mem s₂') ((A.ret s₂').setWidth _)) :
    o.Of A c (sig.contract A pre post writeArgs stack leak) := by
  unfold PublicOut.Of
  split
  · exact True.intro
  · rename_i vals hv
    intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub hg e₁ e₂
    have hp : ∀ s t s', (sig.contract A pre post writeArgs stack leak).pre s → Exec T.isa c s t s' →
        Curry.apply _ post' (vals s) (A.mem s) (A.mem s') ((A.ret s').setWidth _) := by
      intro s t s' hs e
      obtain ⟨t', u, e', -, hq⟩ := h.1 s hs
      obtain ⟨-, rfl⟩ := Exec.det e e'
      simp only [Sig.contract] at hq
      rw [hv] at hq
      exact hq
    exact ho vals hv s₁ s₂ s₁' s₂' h₁ h₂ hpub hg (hp _ _ _ h₁ e₁) (hp _ _ _ h₂ e₂)

/-- `VerifiedScrubbed` for a weaker postcondition, all else the same. No target's
`noResidue` depends on the postcondition: on each, `hR` is `id`. -/
theorem VerifiedScrubbed.post_mono {T : Target} {c : Prog T.isa} {A : Abi T.isa} {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)} {post post' : sig.Post A.ptrBits}
    {writeArgs : Bool} {stack : Nat} {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    {rb : Nat} (h : VerifiedScrubbed T c (sig.contract A pre post' writeArgs stack leak) rb)
    (hR : (T.noResidue.elim False fun R => R c (sig.contract A pre post' writeArgs stack leak) rb) →
      T.noResidue.elim False fun R => R c (sig.contract A pre post writeArgs stack leak) rb)
    (hp : sig.PostImp A.ptrBits post' post) :
    VerifiedScrubbed T c (sig.contract A pre post writeArgs stack leak) rb where
  verified := h.verified.post_mono hp
  noResidue := hR h.noResidue
  retAbi := h.retAbi

end VG
