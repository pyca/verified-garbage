module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Stack frames of any size (RISC-V)

`bigFrame n body`: `body` in a frame of `n` bytes below the stack pointer
(`n` a multiple of 16): one allocation up to 4064 bytes (the most `alloc`
takes), else one frame of the rest around frames of 2032 bytes, of which
the lowest is the frame's lowest 2032 bytes. The body runs with the stack
pointer at the frame's base.
-/

@[expose] public section

namespace VG.Impl.Words.RISCV64

open VG.RISCV64

/-- `body` in `q` frames of 2032 bytes. -/
def chunks : Nat → Prog isa → Prog isa
  | 0, body => body
  | q + 1, body => .frame (.alloc 2032) (chunks q body) (.free 2032)

/-- `body` in a frame of `n` bytes: one allocation if `n` is at most 4064,
else one of the rest (none if it is zero) around frames of 2032 bytes. -/
def bigFrame (n : Nat) (body : Prog isa) : Prog isa :=
  if 2032 < n ∧ n ≤ 4064 then .frame (.alloc n) body (.free n)
  else if n % 2032 = 0 then chunks (n / 2032) body
  else .frame (.alloc (n % 2032)) (chunks (n / 2032) body) (.free (n % 2032))

end VG.Impl.Words.RISCV64
