module

public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.Framework.CodeWalk
public import VerifiedGarbage.Proof.Framework.InlineMatch

/-!
# What a function's cleanup needs of the code it calls, as Booleans (x86, 32-bit)

The cleanup of a function on x86 (`Impl.Scrub.X86.scrubAll`, whose theorem
is `X86.Scrub.verifiedScrubbedAll`, `Proof/Framework/X86/ScrubProved.lean`) needs of its code, callees included,
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

/-- `Instr.isMmx`, with its cases closed (`inline_match%`). -/
def Instr.isMmxK : Instr → Bool := inline_match% VG.X86.Instr.isMmx

theorem Instr.isMmxK_eq (i : Instr) : i.isMmxK = i.isMmx := by cases i <;> rfl

theorem Instr.isMmxK_fn : (fun i : Instr => !i.isMmxK) = fun i => !i.isMmx :=
  funext fun i => by rw [Instr.isMmxK_eq]

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
`calleeOk_iff`). Only the kernel evaluates it. -/
noncomputable def calleeOk (c : Prog isa) : Bool := CodeWalk.sideAll (fun i => !i.isMmxK) [] c

theorem inames_nil_iff (c : Prog isa) : CodeWalk.inames c = [] ↔ noIcall c = true := by
  induction c with
  | block => simp only [CodeWalk.inames, noIcall]
  | seq a b iha ihb | ite _ a b iha ihb =>
    simp only [CodeWalk.inames, noIcall, List.append_eq_nil_iff, Bool.and_eq_true, iha, ihb]
  | loop b _ ih | call _ b ih | frame _ b _ ih => exact ih
  | icall => simp only [CodeWalk.inames, noIcall, List.cons_append, reduceCtorEq]

theorem calleeOk_iff (c : Prog isa) :
    calleeOk c = true ↔ noIcall c = true ∧ c.allInstrs (fun i => !i.isMmx) = true := by
  rw [calleeOk, CodeWalk.sideAll_iff, Instr.isMmxK_fn, ← inames_nil_iff, and_comm, List.eq_nil_iff_forall_not_mem]
  simp only [List.not_mem_nil]

end VG.X86
