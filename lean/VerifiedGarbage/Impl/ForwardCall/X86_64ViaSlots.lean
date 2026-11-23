module

public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.Impl.ICall

/-!
# Calls of functions through slots, at any frame depth (x86-64)

`Code.viaSlots slots d c` is `c` with each of its calls of a function `n` of
`slots` made an indirect call through the slot of `n` (`call qword ptr
[rsp + disp]`, one candidate, `Code.icalls`), where `(off, n)` is in `slots`
and the slot is `off` bytes above the stack pointer on entry. `d` is how far
below that the stack pointer is where `c` runs: each frame `c` pushes adds
its bytes, so the call reads `[rsp + off + d]`, the same word at any depth.
The code of the functions `c` calls is not changed: only `c`'s own calls are
made through slots. The printed code of such a call does not name its
callee, so `c` made so is the same code whatever functions the slots hold.
-/

@[expose] public section

namespace VG.Impl.ForwardCall.X86_64

open VG.X86_64

/-- The bytes of stack a frame's push takes (`Instr.frameBytes`). -/
def pushBytes : Instr → Nat
  | .push rs => 8 * rs.length
  | .alloc bytes => bytes
  | _ => 0

/-- The offset of `n`'s slot in `slots`, if it has one. -/
def slotOff (slots : List (Int × String)) (n : String) : Option Int :=
  (slots.find? (·.2 == n)).map (·.1)

/-- The call of `n`, whose code is `b`, through the word at `rsp + disp`. -/
def slotCall (disp : Int) (n : String) (b : Prog isa) : Prog isa :=
  Code.icalls (.callm { base := .rsp, disp := disp }) [(n, b)]

/-- `c`, `d` bytes below the stack pointer on entry, with each call of a
function of `slots` made through its slot. -/
def Code.viaSlots (slots : List (Int × String)) : Nat → Prog isa → Prog isa
  | _, .block is => .block is
  | d, .seq a b => .seq (viaSlots slots d a) (viaSlots slots d b)
  | d, .ite cd a b => .ite cd (viaSlots slots d a) (viaSlots slots d b)
  | d, .loop b cd => .loop (viaSlots slots d b) cd
  | d, .call m b => match slotOff slots m with
    | some off => slotCall (off + d) m b
    | none => .call m b
  | d, .frame i b j => .frame i (viaSlots slots (d + pushBytes i) b) j
  | _, .icall i m b nx => .icall i m b nx

end VG.Impl.ForwardCall.X86_64
