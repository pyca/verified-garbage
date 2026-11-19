module

public import VerifiedGarbage.TCB.X86.Isa

/-!
# What a function's cleanup needs of the code it calls, as Booleans (x86, 32-bit)

The cleanup of a function on x86 (`X86.Scrub.scrubFOf`,
`Proof/Framework/X86/ScrubProved.lean`) needs of its code, callees included,
that it has no MMX instruction (`Instr.isMmx`), makes no indirect call
(`noIcall`), and uses at most the stack it zeroes (`stackUse`). Its tail
clears every register a callee may change whatever the code, so nothing is
needed of the registers the code writes.

These hold of a function and of the code it calls separately: an
implementation that several functions call, a variant
(`Proof/Variants/<Iface>/X86.lean`), proves its part once, where it is
defined (`calleeOk`, by `lit_decide`, with the stack it states), and a
function that calls it proves the rest of its own code, whatever the
implementation (`X86.Scrub.scrubFSide_of_fill`,
`Proof/Framework/X86/ScrubCall.lean`).

These are definitions on code only, for the modules that state an
implementation's facts without the proofs about the cleanup.
-/

@[expose] public section

namespace VG.X86

/-- An MMX instruction, or the push or pop of an MMX frame. -/
def Instr.isMmx : Instr → Bool
  | .mop _ | .mmxStore .. | .mmxEnter | .emms => true
  | _ => false

/-- `c`, and the functions it calls, make no indirect call. -/
def noIcall : Prog isa → Bool
  | .block _ => true
  | .seq a b => noIcall a && noIcall b
  | .ite _ t e => noIcall t && noIcall e
  | .loop b _ => noIcall b
  | .call _ b => noIcall b
  | .frame _ b _ => noIcall b
  | .icall .. => false

/-- What the cleanup of a function that calls `c` needs of `c`, but its
stack: `c`, and the functions it calls, make no indirect call and have no
MMX instruction (`noIcall c` and `c.allInstrs (!·.isMmx)`, in one pass,
`calleeOk_iff`). Only the kernel evaluates it: a block is walked with
`List.rec`, as `Code.allInstrs` walks it. -/
noncomputable def calleeOk : Prog isa → Bool
  | .block is => List.rec (motive := fun _ => Bool) true (fun i _ ih => !i.isMmx && ih) is
  | .seq a b => calleeOk a && calleeOk b
  | .ite _ t e => calleeOk t && calleeOk e
  | .loop b _ => calleeOk b
  | .call _ b => calleeOk b
  | .frame i b j => !i.isMmx && calleeOk b && !j.isMmx
  | .icall .. => false

end VG.X86
