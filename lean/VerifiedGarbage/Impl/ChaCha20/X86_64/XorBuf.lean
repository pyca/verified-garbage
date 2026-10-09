import VerifiedGarbage.Impl.ChaCha20.X86_64

/-!
# XORing keystream from a buffer into the data, eight bytes at a time

`xorBuf d b` XORs the `rdx` bytes at `b` (keystream, in a buffer) into the
`rdx` bytes at `d` (the data): eight bytes at a time while at least eight
remain, then a byte at a time. `rcx` counts the bytes done; `rax` counts
down the whole quadwords left (from `rdx / 8`) and then serves, with `r8`,
as scratch.

The branches are on `rcx`, `rax` and `rdx` only, which depend on the length
alone, and every address is `d` or `b` plus `rcx`, so only the pointers and
the length can affect timing.
-/

namespace VG.Impl.ChaCha20.X86_64.XorBuf

open VG.X86_64

/-- `[base + rcx]`. -/
def idx (base : Reg) : MemOp := { base := base, index := some .rcx }

/-- XOR the quadword at `b + rcx` into that at `d + rcx`. -/
def qBody (d b : Reg) : List Instr :=
  [.mov .r8 (.mem (idx d)), .alu .xor .r8 (.mem (idx b)), .store (idx d) .r8,
   .alu .add .rcx (.imm 8), .alu .sub .rax (.imm 1)]

/-- XOR the byte at `b + rcx` into that at `d + rcx`. -/
def bBody (d b : Reg) : List Instr :=
  [.movzx8 .rax (idx d), .movzx8 .r8 (idx b), .alu .xor .rax (.reg .r8), .store8 (idx d) .rax,
   .alu .add .rcx (.imm 1), .alu .cmp .rcx (.reg .rdx)]

def xorBuf (d b : Reg) : Prog isa :=
  .seq (.block [.mov32 .rcx (.imm 0), .mov .rax (.reg .rdx), .shift .shr .rax 3])
  (.seq (.ite .e (.block []) (.loop (.block (qBody d b)) .ne))
  (.seq (.block [.alu .cmp .rcx (.reg .rdx)])
    (.ite .e (.block []) (.loop (.block (bBody d b)) .ne))))

/-! ## Out of place

`xorBufTo d s b` writes to the `rdx` bytes at `d` the `rdx` bytes at `s`
(the data) XORed with those at `b` (keystream), in the same way. -/

/-- The quadword at `s + rcx` XORed with that at `b + rcx`, to `d + rcx`. -/
def qBodyTo (d s b : Reg) : List Instr :=
  [.mov .r8 (.mem (idx s)), .alu .xor .r8 (.mem (idx b)), .store (idx d) .r8,
   .alu .add .rcx (.imm 8), .alu .sub .rax (.imm 1)]

/-- The byte at `s + rcx` XORed with that at `b + rcx`, to `d + rcx`. -/
def bBodyTo (d s b : Reg) : List Instr :=
  [.movzx8 .rax (idx s), .movzx8 .r8 (idx b), .alu .xor .rax (.reg .r8), .store8 (idx d) .rax,
   .alu .add .rcx (.imm 1), .alu .cmp .rcx (.reg .rdx)]

def xorBufTo (d s b : Reg) : Prog isa :=
  .seq (.block [.mov32 .rcx (.imm 0), .mov .rax (.reg .rdx), .shift .shr .rax 3])
  (.seq (.ite .e (.block []) (.loop (.block (qBodyTo d s b)) .ne))
  (.seq (.block [.alu .cmp .rcx (.reg .rdx)])
    (.ite .e (.block []) (.loop (.block (bBodyTo d s b)) .ne))))

end VG.Impl.ChaCha20.X86_64.XorBuf
