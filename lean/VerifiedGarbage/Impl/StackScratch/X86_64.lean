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

end VG.Impl.StackScratch.X86_64
