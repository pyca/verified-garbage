module

public import VerifiedGarbage.Impl.ForwardCall.X86_64

/-!
# A call that forwards a function's stack arguments and the addresses of functions (x86-64)

`forwardS bytes m fns name body` is `forward bytes m name body` that also
stores the addresses of the functions `fns` in the frame's words above the
copies of the `m` stack arguments: the callee, which calls them indirectly
through those words (`call qword ptr [rsp + disp]`), finds them there, just
above its stack arguments. It passes them through `rax`, as the copies.
-/

@[expose] public section

namespace VG.Impl.ForwardCall.X86_64

open VG.X86_64

/-- `lea rax, [rip + n]; mov [rsp + 8j], rax`: the address of the function
`n` into word `j` of this frame. -/
def storeAddr (j : Nat) (n : String) : List Instr :=
  [.leaSym .rax n, .store { base := .rsp, disp := ((8 * j : Nat) : Int) } .rax]

/-- The addresses of the functions `fns` into the words of this frame from
word `j` up. -/
def storeAddrs : Nat → List String → List Instr
  | _, [] => []
  | j, n :: ns => storeAddr j n ++ storeAddrs (j + 1) ns

/-- A call of `name`, whose code is `body`, with this function's `m` stack
arguments copied into a frame of `bytes` bytes, and above them the addresses
of `fns`. -/
def forwardS (bytes m : Nat) (fns : List String) (name : String) (body : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block (copies bytes m ++ storeAddrs m fns)) (.call name body)) (.free bytes)

end VG.Impl.ForwardCall.X86_64
