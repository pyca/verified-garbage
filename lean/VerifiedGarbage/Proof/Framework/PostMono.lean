module

public import VerifiedGarbage.Proof.Framework.Contract

/-!
# Strengthening the postcondition of a contract built with `Sig.contract`

A proof of a function against `sig.contract A pre post …` is a proof
against `sig.contract A pre post' …` (with the same precondition, public
data and leakage) when `post` implies `post'` at every argument
(`Verified.post_mono`). The functions whose contracts in `Spec/` are stated
for a key (an AES key whose schedule is in memory, say) are proven against
a contract on what is in memory, and moved to the key's with it.
-/

@[expose] public section

namespace VG

/-- `R` relates `f` and `g` at every argument. -/
def Curry.Forall₂ {α : Type} (R : α → α → Prop) : (ws : List ArgWord) → Curry ws α → Curry ws α → Prop
  | [], f, g => R f g
  | _ :: ws, f, g => ∀ x, Curry.Forall₂ R ws (f x) (g x)

theorem Curry.Forall₂.apply {α : Type} {R : α → α → Prop} :
    ∀ {ws : List ArgWord} {f g : Curry ws α}, Curry.Forall₂ R ws f g →
      ∀ vs, R (Curry.apply ws f vs) (Curry.apply ws g vs)
  | [], _, _, h, vs => by cases vs <;> exact h
  | _ :: _, _, _, h, [] => Curry.Forall₂.apply (h _) []
  | _ :: _, _, _, h, _ :: vs => Curry.Forall₂.apply (h _) vs

/-- A postcondition `post'` that `post` implies, at every argument, memory
on entry and exit and return value. -/
abbrev Sig.PostImp (sig : Sig) (pb : Nat) (post post' : sig.Post pb) : Prop :=
  Curry.Forall₂ (fun p q => ∀ m m' r, p m m' r → q m m' r) (sig.words pb) post post'

/-- Moving a proof to a stronger postcondition, all else the same. -/
theorem Verified.post_mono {T : Target} {c : Prog T.isa} {A : Abi T.isa} {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)} {post post' : sig.Post A.ptrBits}
    {writeArgs : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (h : Verified T c (sig.contract A pre post writeArgs stack leak))
    (hp : sig.PostImp A.ptrBits post post') :
    Verified T c (sig.contract A pre post' writeArgs stack leak) :=
  h.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h => by
        revert h
        simp only [Sig.contract]
        split
        · exact id
        · exact hp.apply _ _ _ _
      pub := fun _ _ _ _ h => h
      sat := h.2.2 }

end VG
