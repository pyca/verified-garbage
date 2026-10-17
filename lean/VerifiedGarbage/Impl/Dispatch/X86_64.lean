module

public import VerifiedGarbage.Impl.Dispatch
public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Choosing code by a public selector on x86-64

`chain cases` is `Dispatch.chain` with the selector in `rax`: each test is
`cmp rax, k` (an immediate, sign-extended: for keys below `2^31`), and a
case runs if `ZF` is set. Only the flags change: the code of a case starts
with `rax` the selector, and every other register and the memory as before.
-/

@[expose] public section

namespace VG.Impl.Dispatch.X86_64

open VG.X86_64

/-- `cmp rax, k`. -/
def test (k : Nat) : List Instr := [.alu .cmp .rax (.imm (BitVec.ofNat 32 k))]

/-- The case of `cases` whose key is `rax`. -/
def chain (cases : List (Nat × Prog isa)) : Prog isa := Dispatch.chain test .e cases

end VG.Impl.Dispatch.X86_64
