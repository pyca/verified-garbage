import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# A scratch buffer on the stack (PPC64LE)

`withStackScratch bytes r c` runs code `c`, written for a function whose last
argument is a scratch buffer, passed in `r`, without that argument: it
allocates a frame of `bytes` bytes on the stack (`stdu r1, -bytes(r1)`) and
passes the address of its local variable space, above the frame's 32-byte
header, in `r`. The buffer is below the stack pointer on entry, where no Rust
object lies.
-/

namespace VG.Impl.StackScratch.PPC64LE

open VG.PPC64LE

/-- `c`, with its scratch buffer (passed in `r`) in a frame of `bytes` bytes
on the stack, at `r1 + 32`. -/
def withStackScratch (bytes : Nat) (r : Reg) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block [.addSp r 32]) c) (.free bytes)

end VG.Impl.StackScratch.PPC64LE
