module

public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# A call that forwards a function's stack arguments (x86-64)

`forward bytes m name body` calls the function `name`, whose code is `body`,
with the arguments its caller was given: the six argument registers as they
are, and a copy of the `m` stack arguments. It allocates a frame of `bytes`
bytes, copies the stack arguments to its bottom (`copies`), where the callee,
entered 8 bytes lower by the call, finds them, and calls. It passes them
through `rax`, which no argument is in.
-/

@[expose] public section

namespace VG.Impl.ForwardCall.X86_64

open VG.X86_64

/-- `mov rax, [rsp + bytes + 8 + 8j]; mov [rsp + 8j], rax`: copy stack
argument `j` from the caller's frame to the bottom of this one. -/
def copyDown (bytes j : Nat) : List Instr :=
  [.mov .rax (.mem { base := .rsp, disp := ((bytes + 8 + 8 * j : Nat) : Int) }),
    .store { base := .rsp, disp := ((8 * j : Nat) : Int) } .rax]

/-- Copy the `m` stack arguments. -/
def copies (bytes m : Nat) : List Instr := (List.range m).flatMap (copyDown bytes)

/-- A call of `name`, whose code is `body`, with this function's `m` stack
arguments copied into a frame of `bytes` bytes. -/
def forward (bytes m : Nat) (name : String) (body : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block (copies bytes m)) (.call name body)) (.free bytes)

end VG.Impl.ForwardCall.X86_64
