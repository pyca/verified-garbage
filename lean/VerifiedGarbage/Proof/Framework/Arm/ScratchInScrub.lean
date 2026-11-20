module

public import VerifiedGarbage.Proof.Framework.Arm.StackScratch
public import VerifiedGarbage.Proof.Framework.Arm.RegScratch

/-!
# A scratch frame that the function's cleanup zeroes (ARMv7)

A function as emitted on ARM is `Impl.Residue.Arm.scrubF rb n c`, whose
cleanup zeroes the `n` bytes below the stack pointer, where every frame of
`c` was, those of the functions it calls included (`Arm.Scrub.CodeOk`). So
the frame in which `c` keeps its working space needs no wipe of its own: it
is `withStackScratch` (or `withRegScratch`), not `withStackScratchWiped`,
and `NoResidue` comes from the cleanup alone.

`Verified.stackScratchInScrubArm` and `Verified.regScratchInScrubArm` are
`Verified.stackScratch` and `Verified.regScratch` with the arguments of
`Verified.stackScratchWiped` and `Verified.regScratchWiped`, but the number
of words wiped (`hw`): the postcondition's locality (`hpostOut`, `hpost`)
whatever the precondition. A proof of the wiped frame becomes one of the
frame without the wipe by the theorem's name and one `(by decide)` fewer.
-/

@[expose] public section

namespace VG.Arm

open VG.Impl.StackScratch.Arm

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes m : Nat} {r : Reg} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- `Verified.stackScratch`, for a postcondition that reads the memory on
return only within the function's buffers whatever the precondition: the
arguments of `Verified.stackScratchWiped` without its `hw`. -/
theorem Verified.stackScratchInScrubArm {c : Prog isa}
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
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs mm m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs mm m₂ r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (withStackScratch bytes m c) (sig.contract abi pre post wa (stack + bytes) leak) :=
  Verified.stackScratch h hcl hN hloc hb hpre hpost
    (fun vs mm m₁ m₂ r hl _ => hpostOut vs mm m₁ m₂ r hl) hsat hleak

/-- `Verified.regScratch`, for a postcondition that reads the memory on
return only within the function's buffers whatever the precondition: the
arguments of `Verified.regScratchWiped` without its `hw`. -/
theorem Verified.regScratchInScrubArm {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hcl : ScratchInReg sig r) (hloc : (locs sig).all (Loc.avoids r) = true) (hb : FitsR bytes e n)
    (hpost : ∀ vs mm m₁ m₂ ret, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs mm m₁ ret →
        Curry.apply (sig.words abi.ptrBits) post vs mm m₂ ret)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target (withRegScratch bytes r c) (sig.contract abi pre post wa (stack + bytes) leak) :=
  Verified.regScratch h hcl hloc hb (fun vs mm m₁ m₂ ret hl' _ => hpost vs mm m₁ m₂ ret hl') hsat hl

end

end VG.Arm
