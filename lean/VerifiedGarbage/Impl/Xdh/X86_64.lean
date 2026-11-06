module

public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# X25519 and X448 exchange, with RFC 7748's check, on x86-64

`vg_x25519_exchange` and `vg_x448_exchange(out = rdi, scalar = rsi,
point = rdx, scratch = rcx) -> u32` call the unchecked function (`vg_x25519`,
`vg_x448`, or a variant) with the same arguments, then OR together the `n`
bytes it wrote to `out` and return 1 if that is nonzero, 0 otherwise
(RFC 7748 §6.1, §6.2).

`out` waits for the call in a frame of 8 bytes (`push rdi`), whose pop
loads it into `rdx`; the frame also aligns the stack for the call. The bytes
are loaded one at a time (`movzx`), and no branch depends on them: the result
is `((acc - 1) >> 63) ^ 1`, which is 1 iff the OR `acc`, below 256, is not
zero.
-/

@[expose] public section

namespace VG.Impl.Xdh.X86_64

open VG.X86_64

/-- ORs the first `i` bytes at `rdx` into `rcx`, with `rax`. -/
def orBytes : Nat → List Instr
  | 0 => []
  | i + 1 => orBytes i ++ [.movzx8 .rax ⟨.rdx, none, 1, (i : Int)⟩, .alu .or .rcx (.reg .rax)]

/-- `rax := 1` if the `n` bytes at `rdx` are not all zero, else `0`. -/
def check (n : Nat) : List Instr :=
  .mov .rcx (.imm 0) :: orBytes n ++
    [.alu .sub .rcx (.imm 1), .shift .shr .rcx 63, .alu .xor .rcx (.imm 1), .mov .rax (.reg .rcx)]

/-- The call of `name`, whose code is `callee`, then the check of the `n`
bytes it wrote to `out`. -/
def exchange (name : String) (callee : Prog isa) (n : Nat) : Prog isa :=
  .seq (.frame (.push [.rdi]) (.call name callee) (.pop .rdx 1)) (.block (check n))

end VG.Impl.Xdh.X86_64
