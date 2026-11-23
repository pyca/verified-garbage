module

public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Impl.ICall

/-!
# Calling functions by addresses held in MMX registers (x86, 32-bit)

A function that is the same code for every implementation of the functions
it calls calls each by its address, which its entry leaves in an MMX
register that nothing else writes: `movd eax, mm`, then `call eax`, an
indirect call of one candidate (`Code.icalls`), whose printed code does not
name the callee. `Code.viaMm fs c` is `c` with each call of a function of
`fs` made so, by the register `fs` gives it.

The entry of such a function, `entryMm fs k name core`, is an MMX frame
(`TCB/X86/Isa.lean`): it puts the address of each function of `fs` in its
register (`loadFn`: `symPush` gives the address in `eax`, then `movd mm,
eax`), copies its `k` stack words into the bottom of a frame of its own
(`copyTo`), so that `core`, which it calls, finds its arguments at its own
`esp`, and leaves the frame with `emms`. The callees are functions emitted
with the code: none has an MMX frame of its own, so none faults, and none
writes an MMX register, so each still holds its address at each call.
-/

@[expose] public section

namespace VG.Impl.ViaMm.X86

open VG.X86

/-- The call of `n`, whose code is `b`, by the address in the low 32 bits of
`r`. -/
def callVia (r : MReg) (n : String) (b : Prog isa) : Prog isa :=
  .seq (.block [.mmxMovd .eax r]) (Code.icalls (.callr .eax) [(n, b)])

/-- `c` with each call of a function that `fs` maps to an MMX register made a
call by the address in that register. -/
def Code.viaMm (fs : List (String × MReg)) : Prog isa → Prog isa
  | .block is => .block is
  | .seq a b => .seq (viaMm fs a) (viaMm fs b)
  | .ite cd a b => .ite cd (viaMm fs a) (viaMm fs b)
  | .loop b cd => .loop (viaMm fs b) cd
  | .call m b => match fs.lookup m with
    | some r => callVia r m (viaMm fs b)
    | none => .call m (viaMm fs b)
  | .frame i b j => .frame i (viaMm fs b) j
  | .icall i m b nx => .icall i m b nx

/-- `n`'s address into `r`: `call 2f; 2: mov eax, [esp]; add eax, n - 2b`
(`symPush`), its word popped, then `movd r, eax`. -/
def loadFn (n : String) (r : MReg) : Prog isa :=
  .frame (.symPush .eax n) (.block [.mop (.movd r .eax)]) (.free 4)

/-- The address of each function of `fs` into its register. -/
def loadFns : List (String × MReg) → Prog isa
  | [] => .block []
  | (n, r) :: fs => .seq (loadFn n r) (loadFns fs)

/-- `mov eax, [esp + bytes + 4 + 4j]; mov [esp + 4j], eax`: argument slot `j`
of the caller's frame into slot `j` of this one, from its bottom. -/
def copyTo (bytes j : Nat) : List Instr :=
  [.mov .eax (.mem ⟨.esp, bytes + 4 + 4 * j⟩), .store ⟨.esp, 4 * j⟩ .eax]

/-- The call of `name`, whose code is `core`, with the `k` (at least 1)
argument slots copied into a frame of their own, at the stack pointer of the
call, where `core` finds its arguments. -/
def callCopy (k : Nat) (name : String) (core : Prog isa) : Prog isa :=
  .frame (.alloc (4 * k)) (.seq (.block ((List.range k).flatMap (copyTo (4 * k)))) (.call name core))
    (.free (4 * k))

/-- The entry: the addresses of `fs` into their registers, then `body`, in an
MMX frame. -/
def mmFrame (fs : List (String × MReg)) (body : Prog isa) : Prog isa :=
  .frame .mmxEnter (.seq (loadFns fs) body) .emms

end VG.Impl.ViaMm.X86
