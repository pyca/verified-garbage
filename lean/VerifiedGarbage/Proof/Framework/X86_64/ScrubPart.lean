module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubPaths
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.X86_64.UpperLock
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.ResidueKeep
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.Offset

/-!
# x86-64 residue: clearing only the registers that may hold secrets

`scrub v rb xs ps gs ks cs c` clears the SSE registers `xs` and the
general-purpose registers `ps` and `gs` (and the upper bits of `rax`).
`Verified.scrubM` takes those from the code's instructions: every SSE
register if any instruction may write one, every caller-saved register any
instruction may write (`xsOf`, `gsOf`). Code that calls a function using the
vector registers on one path only, and clears them itself at the end of that
path, needs none of them cleared on return; nor the general-purpose registers
it leaves public on every path.

`Verified.scrubPart` clears the registers `xs` and `gs` given, any of them,
if two runs end agreeing on every register the clearing keeps (`RegsOk`):
the clearing of fewer registers runs along the same trace to the same state
but for the registers it keeps, so it is verified, and returns without
secret residue, if the clearing of those `Verified.scrubM` chooses does
(`hall`). The clearing of the stack and of MXCSR is the same in both.
`RegsOk` follows from what each run leaves in those registers, as
`resOk_of_leaves` gives the stack's `ResOk` (`RegLeaves`, `regsOk_of_leaves`).
`withScrubResCR` is `RScrub.withScrubResC` with the registers cleared given.

Code that clears what it leaves need not wipe the stack either, but for
the return addresses its calls leave below the stack pointer: which of the
state's `unknowns` each is depends on the path, and on how many calls the
functions it calls make. Two runs that agree on them on entry, along the
same trace, leave the same ones (`StackLock.lock`): their traces split
alike (`UpperLock.lock`), so their calls are the same calls, from the same
stack pointer, and push the same unknowns. So, too, with the vector
registers of code that clears them after the calls that use them
(`VecLock.step`, `VecLock.lock`, `regsOk_of_vec`): what they hold after
each piece of the code is either what they held before it or zero, as the
path says.

It is a module of its own, not part of `Scrub.lean`, so that the many
modules that import `Scrub.lean` are not rebuilt for it.
-/

@[expose] public section

open VG.Impl.Scrub.X86_64

namespace VG.X86_64.Scrub

open VG.X86_64 VG.X86_64.Residue

section
variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

end

/-! ## Registrations -/

end VG.X86_64.Scrub

/-! ## Return addresses, in two runs along the same path -/

namespace VG.X86_64.StackLock

open VG VG.X86_64 VG.X86_64.UpperLock

namespace Plain

end Plain

/-- `Plain` of code made of blocks, branches, loops and calls of plain code
(the hypotheses in context). -/
macro "plain_tac" : tactic => `(tactic| repeat' first
  | with_reducible assumption
  | refine Plain.seq ?_ ?_
  | refine Plain.ite ?_ ?_
  | refine Plain.loop ?_
  | refine Plain.call ?_
  | exact Plain.block (by decide))

namespace RelS

variable {S : Addr → Prop} {P Q R : State → State → Prop}

end RelS

section
open VG.Impl.StackScratch.X86_64
variable {sig : Sig} {nm : String} {e : Elem} {n bytes stack : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {c : Prog isa}

end

end VG.X86_64.StackLock

/-! ## The vector registers, in two runs along the same path -/

namespace VG.X86_64.VecLock

open VG VG.X86_64 VG.X86_64.UpperLock VG.Impl.Scrub.X86_64

end VG.X86_64.VecLock

namespace VG.X86_64.HLock

open VG VG.X86_64 VG.X86_64.UpperLock VG.Impl.Scrub.X86_64

end VG.X86_64.HLock

namespace VG.X86_64.Scrub

open VG.Impl.Scrub.X86_64

section
variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

end

end VG.X86_64.Scrub

namespace VG.X86_64.RScrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64

end VG.X86_64.RScrub
