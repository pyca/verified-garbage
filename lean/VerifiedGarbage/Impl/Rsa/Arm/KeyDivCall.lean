module

public import VerifiedGarbage.Impl.Rsa.Arm.KeyDiv

/-! # `divW`'s steps on ARMv7 as a function of its own

`tail r m t nm u qo` is `divW`'s steps, the loop and its last step, after
its preparation. `tailFn` is them with the return address kept in the header
word `sT`, which they do not write: it uses no stack. `divWC name …` is
`divW` with its steps a call of `name` (`tailFn`), so that a caller dividing
into the same arrays several times emits the steps once.
-/

@[expose] public section

namespace VG.Impl.Rsa.Arm.KeyDiv
open VG VG.Arm VG.Impl.Rsa.Arm.Keys

/-- `divW`'s steps: the loop and its last step. -/
def tail (r m t nm u : Nat) (qo : Option Nat := none) : Prog isa :=
  .seq (.loop (.seq (step r m t nm u qo) (.block [.ldr .r0 .r8 sJ, .cmp .r0 (.imm 0)])) .ne) (step r m t nm u qo)

/-- `tail`, keeping `lr` in the header word `sT`. -/
def tailFn (r m t nm u : Nat) (qo : Option Nat := none) : Prog isa :=
  .seq (.block [.str .lr .r8 sT]) (.seq (tail r m t nm u qo) (.block [.ldr .lr .r8 sT]))

/-- `divW` with its steps a call of `name` (`tailFn`). -/
def divWC (name : String) (a r m t nm u : Nat) (top : Option Nat := none) (qo : Option Nat := none) :
    Prog isa :=
  .seq (prep a r m nm top) (.call name (tailFn r m t nm u qo))

end VG.Impl.Rsa.Arm.KeyDiv
