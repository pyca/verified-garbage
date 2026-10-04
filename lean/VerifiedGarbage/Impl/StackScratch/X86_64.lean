import VerifiedGarbage.TCB.X86_64.Isa

/-!
# A scratch buffer on the stack (x86-64)

`withStackScratch bytes r c` runs code `c`, written for a function whose last
argument is a scratch buffer, passed in `r`, without that argument: it
allocates a frame of `bytes` bytes on the stack, passes the address of its
ninth byte in `r`, and runs `c` there. The frame's first eight bytes, at
`rsp`, stand for the return address that `c`'s contract keeps out of its
buffers; the buffer is the rest of the frame, which is below the stack
pointer on entry, where no Rust object lies.

`withStackScratchWiped bytes r words c` is the same, but zeroes the first
`words` quadwords of the buffer after its code (`wipe`), for a function whose
working space may hold secrets that its caller would otherwise wipe.

`withStackArgScratch bytes m c` is for a function whose scratch buffer
argument is passed on the stack, after `m` other arguments there (its six
argument registers all taken): as x86's `withStackScratch`, it allocates a
frame of `bytes` bytes and lays out in it what `c` expects to find at and
above `rsp` on entry: a quadword standing for the return address, a copy of
the `m` stack arguments, and the address of the buffer, which is the rest of
the frame. It passes them through `rax`, which no argument is in.
`withStackArgScratchWiped bytes m words c` is the same, zeroing the first
`words` quadwords of the buffer after the code (`wipeAt`).

`withTagScratch bytes m a c` is for a function one of whose arguments (at
`a`: a register, or a stack argument) is a buffer of working space that
also carries a 16-byte tag, in or out, in its first 16 bytes: it runs `c` as
a function whose argument there is a pointer to the 16-byte tag alone. As
`withStackArgScratch`, it allocates a frame of `bytes` bytes and lays out in
it a quadword standing for the return address and a copy of the `m` stack
arguments; then the tag pointer (`tagSlot`), and the buffer, which is the
rest of the frame. It copies the tag's 16 bytes into the buffer and passes
the buffer at `a` before the code (`tagSetup`), and copies the buffer's first
16 bytes back to the tag after it (`tagOut`), through `r10` and `r11`, which
hold no result.
-/

namespace VG.Impl.StackScratch.X86_64

open VG.X86_64

/-- `c`, with its scratch buffer (passed in `r`) in a frame of `bytes` bytes
on the stack, at `rsp + 8`. -/
def withStackScratch (bytes : Nat) (r : Reg) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block [.mov r (.reg .rsp), .alu .add r (.imm 8)]) c) (.free bytes)

/-- `mov qword [rsp + 8 + 8k], r11` for each `k < words`. -/
def wipeStores (words : Nat) : List Instr :=
  (List.range words).map fun k => .store { base := .rsp, disp := ((8 + 8 * k : Nat) : Int) } .r11

/-- Zeroes the `words` quadwords at `rsp + 8`, through `r11`. -/
def wipe (words : Nat) : List Instr := .mov32 .r11 (.imm 0) :: wipeStores words

/-- `withStackScratch`, zeroing the first `words` quadwords of the buffer
after the code. -/
def withStackScratchWiped (bytes : Nat) (r : Reg) (words : Nat) (c : Prog isa) : Prog isa :=
  withStackScratch bytes r (.seq c (.block (wipe words)))

/-- `mov rax, [rsp + bytes + 8 + 8j]; mov [rsp + 8 + 8j], rax`: copy stack
argument `j` from the caller's frame into this one. -/
def copyArg (bytes j : Nat) : List Instr :=
  [.mov .rax (.mem { base := .rsp, disp := ((bytes + 8 + 8 * j : Nat) : Int) }),
    .store { base := .rsp, disp := ((8 + 8 * j : Nat) : Int) } .rax]

/-- Copy the `m` stack arguments, and pass the buffer, at `rsp + 16 + 8m`, as
the next one. -/
def setArgs (bytes m : Nat) : List Instr :=
  (List.range m).flatMap (copyArg bytes) ++
    [.mov .rax (.reg .rsp), .alu .add .rax (.imm (BitVec.ofNat 32 (16 + 8 * m))),
      .store { base := .rsp, disp := ((8 + 8 * m : Nat) : Int) } .rax]

/-- `c`, whose scratch buffer is passed on the stack after `m` other stack
arguments, with the buffer in a frame of `bytes` bytes on the stack. -/
def withStackArgScratch (bytes m : Nat) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block (setArgs bytes m)) c) (.free bytes)

/-- `mov qword [rsp + off + 8k], r11` for each `k < words`. -/
def wipeStoresAt (off words : Nat) : List Instr :=
  (List.range words).map fun k => .store { base := .rsp, disp := ((off + 8 * k : Nat) : Int) } .r11

/-- Zeroes the `words` quadwords at `rsp + off`, through `r11`. -/
def wipeAt (off words : Nat) : List Instr := .mov32 .r11 (.imm 0) :: wipeStoresAt off words

/-- `withStackArgScratch`, zeroing the first `words` quadwords of the buffer
(at `rsp + 16 + 8m`) after the code. -/
def withStackArgScratchWiped (bytes m words : Nat) (c : Prog isa) : Prog isa :=
  withStackArgScratch bytes m (.seq c (.block (wipeAt (16 + 8 * m) words)))

/-- Where a function's tag pointer is: in a register, or in stack argument
`j`. -/
inductive TagArg where
  | reg (r : Reg)
  | stack (j : Nat)
  deriving DecidableEq

/-- `rsp + d`. -/
abbrev atSp (d : Nat) : MemOp := { base := .rsp, disp := ((d : Nat) : Int) }

/-- `r11 :=` the tag pointer, from its register or the caller's stack
argument. -/
def loadTagPtr (bytes : Nat) : TagArg → List Instr
  | .reg r => [.mov .r11 (.reg r)]
  | .stack j => [.mov .r11 (.mem (atSp (bytes + 8 + 8 * j)))]

/-- Save the tag pointer (in `r11`) at `rsp + 8 + 8m`, and copy the tag's 16
bytes to the buffer at `rsp + 16 + 8m`, through `r10`. -/
def tagIn (m : Nat) : List Instr :=
  [.store (atSp (8 + 8 * m)) .r11,
    .mov .r10 (.mem { base := .r11, disp := 0 }), .store (atSp (16 + 8 * m)) .r10,
    .mov .r10 (.mem { base := .r11, disp := 8 }), .store (atSp (24 + 8 * m)) .r10]

/-- Pass the buffer, at `rsp + 16 + 8m`, in place of the tag pointer: in its
register, or in the copy of its stack argument. -/
def pointTag (m : Nat) : TagArg → List Instr
  | .reg r => [.mov .rax (.reg .rsp), .alu .add .rax (.imm (BitVec.ofNat 32 (16 + 8 * m))),
      .mov r (.reg .rax)]
  | .stack j => [.mov .rax (.reg .rsp), .alu .add .rax (.imm (BitVec.ofNat 32 (16 + 8 * m))),
      .store (atSp (8 + 8 * j)) .rax]

/-- Copy the `m` stack arguments, save the tag pointer, copy the tag into the
buffer and pass the buffer in the tag pointer's place. -/
def tagSetup (bytes m : Nat) (a : TagArg) : List Instr :=
  (List.range m).flatMap (copyArg bytes) ++ loadTagPtr bytes a ++ tagIn m ++ pointTag m a

/-- Copy the buffer's first 16 bytes back to the tag, whose pointer is at
`rsp + 8 + 8m`, through `r10` and `r11`. -/
def tagOut (m : Nat) : List Instr :=
  [.mov .r11 (.mem (atSp (8 + 8 * m))),
    .mov .r10 (.mem (atSp (16 + 8 * m))), .store { base := .r11, disp := 0 } .r10,
    .mov .r10 (.mem (atSp (24 + 8 * m))), .store { base := .r11, disp := 8 } .r10]

/-- `c`, whose working space at `a` also carries a 16-byte tag, run with a
pointer to the tag alone at `a`, the working space in a frame of `bytes`
bytes on the stack, after a copy of the `m` stack arguments and the tag
pointer. -/
def withTagScratch (bytes m : Nat) (a : TagArg) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block (tagSetup bytes m a)) (.seq c (.block (tagOut m))))
    (.free bytes)

end VG.Impl.StackScratch.X86_64
