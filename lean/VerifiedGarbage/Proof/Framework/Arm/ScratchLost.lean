module

public import VerifiedGarbage.Proof.Framework.Arm.StackScratch
public import VerifiedGarbage.Proof.Framework.Arm.RegScratch

/-!
# Scratch-buffer wrappers that assume nothing of a released frame (ARMv7)

Temporary aliases: `Verified.stackScratchL`, `Verified.stackScratch` and
`Verified.regScratch` now take `hpostOut` themselves (the postcondition
reads the memory on return only within the function's buffers, when the
precondition holds, so that it holds whatever the frame's released bytes
hold); the `…Lost` names pass it through until the proofs use those.
-/

@[expose] public section

namespace VG.Arm

open VG.Impl.StackScratch.Arm

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes m : Nat} {r : Reg} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- `Verified.stackScratchL`, if the postcondition also reads the memory on
return only within the function's buffers (`hpostOut`). -/
theorem Verified.stackScratchLLost {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hcl : ScratchOnStack sig) (hN : nsaa sig = 4 * m)
    (hloc : (locs sig).all (Loc.ok (4 * m)) = true) (hb : Fits m bytes e n)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hpostOut : ∀ vs mm m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      Curry.apply (sig.words abi.ptrBits) pre vs mm →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs mm m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs mm m₂ r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hleak : Sig.LeakLocalL abi.ptrBits sig leak := by trivial) :
    Verified target (withStackScratch bytes m c) (sig.contract abi pre post wa (stack + bytes) leak) :=
  Verified.stackScratchL h hcl hN hloc hb hpre hpost hpostOut hsat hleak

/-- `Verified.stackScratch`, if the postcondition also reads the memory on
return only within the function's buffers (`hpostOut`). -/
theorem Verified.stackScratchLost {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hcl : ScratchOnStack sig) (hN : nsaa sig = 4 * m)
    (hloc : (locs sig).all (Loc.ok (4 * m)) = true) (hb : Fits m bytes e n)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hpostOut : ∀ vs mm m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      Curry.apply (sig.words abi.ptrBits) pre vs mm →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs mm m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs mm m₂ r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (withStackScratch bytes m c) (sig.contract abi pre post wa (stack + bytes) leak) :=
  Verified.stackScratch h hcl hN hloc hb hpre hpost hpostOut hsat hleak

/-- `Verified.regScratch`, if the postcondition reads the memory on return
only within the function's buffers (`hpostOut`). -/
theorem Verified.regScratchLost {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hcl : ScratchInReg sig r) (hloc : (locs sig).all (Loc.avoids r) = true) (hb : FitsR bytes e n)
    (hpostOut : ∀ vs mm m₁ m₂ ret, vs.length = (sig.words abi.ptrBits).length →
      Curry.apply (sig.words abi.ptrBits) pre vs mm →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs mm m₁ ret →
        Curry.apply (sig.words abi.ptrBits) post vs mm m₂ ret)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target (withRegScratch bytes r c)
      (sig.contract abi pre post wa (stack + bytes) leak) :=
  Verified.regScratch h hcl hloc hb hpostOut hsat hl

end

end VG.Arm
