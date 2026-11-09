module

public import VerifiedGarbage.TCB.X86.Isa

/-!
# X25519 and X448 exchange, with RFC 7748's check, on x86

`vg_x25519_exchange` and `vg_x448_exchange(out, scalar, point, scratch)
-> u32`, cdecl (every argument on the stack, at `[esp + 4]` on entry), call
the unchecked function (`vg_x25519`, `vg_x448`) with the same arguments,
then OR together the `n` bytes it wrote to `out` and return 1 if that is
nonzero, 0 otherwise (RFC 7748 §6.1, §6.2).

A frame of 16 bytes holds the call's four arguments, copied from ours,
which are then at `esp + 20` … `esp + 32`; once it is freed, `out` is loaded
from ours again. The bytes are loaded one at a time (`movzx`), and no branch
depends on them: the result is `((acc - 1) >> 31) ^ 1`, which is 1 iff the
OR `acc`, below 256, is not zero.
-/

@[expose] public section

namespace VG.Impl.Xdh.X86

open VG.X86

/-- Our four arguments, from `esp + 20` on, copied to the frame's four words. -/
def copyArgs : List Instr :=
  [.mov .eax (.mem ⟨.esp, 20⟩), .store ⟨.esp, 0⟩ .eax, .mov .eax (.mem ⟨.esp, 24⟩), .store ⟨.esp, 4⟩ .eax,
    .mov .eax (.mem ⟨.esp, 28⟩), .store ⟨.esp, 8⟩ .eax, .mov .eax (.mem ⟨.esp, 32⟩), .store ⟨.esp, 12⟩ .eax]

/-- `out`, our first argument, into `edx`. -/
def restore : List Instr := [.mov .edx (.mem ⟨.esp, 4⟩)]

/-- ORs the first `i` bytes at `edx` into `ecx`, with `eax`. -/
def orBytes : Nat → List Instr
  | 0 => []
  | i + 1 => orBytes i ++ [.movzx8 .eax ⟨.edx, i⟩, .alu .or .ecx (.reg .eax)]

/-- `eax := 1` if the `n` bytes at `edx` are not all zero, else `0`. -/
def check (n : Nat) : List Instr :=
  .mov .ecx (.imm 0) :: orBytes n ++
    [.alu .sub .ecx (.imm 1), .shift .shr .ecx 31, .alu .xor .ecx (.imm 1), .mov .eax (.reg .ecx)]

/-- The call of `name`, whose code is `callee`, then the check of the `n`
bytes it wrote to `out`. -/
def exchange (name : String) (callee : Prog isa) (n : Nat) : Prog isa :=
  .seq (.frame (.alloc 16) (.seq (.block copyArgs) (.call name callee)) (.free 16))
    (.seq (.block restore) (.block (check n)))

end VG.Impl.Xdh.X86
