module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Stack frames of any size (RISC-V)

`bigFrame n body`: `body` in a frame of `n` bytes below the stack pointer
(`n` a multiple of 16), allocated as one frame of the rest around frames of
2032 bytes, since one `addi` allocates at most 2047: the frame's lowest
2032 bytes (or all of it) are one allocation. The body runs with the stack
pointer at the frame's base.
-/

@[expose] public section

namespace VG.Impl.Words.RISCV64

open VG.RISCV64

/-- `body` in `q` frames of 2032 bytes. -/
def chunks : Nat → Prog isa → Prog isa
  | 0, body => body
  | q + 1, body => .frame (.alloc 2032) (chunks q body) (.free 2032)

/-- `body` in a frame of `n` bytes: one of the rest (none if it is zero)
around frames of 2032 bytes. -/
def bigFrame (n : Nat) (body : Prog isa) : Prog isa :=
  if n % 2032 = 0 then chunks (n / 2032) body
  else .frame (.alloc (n % 2032)) (chunks (n / 2032) body) (.free (n % 2032))

end VG.Impl.Words.RISCV64
