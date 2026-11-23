module

public import VerifiedGarbage.Impl.Rsa.Arm.Inverse

/-! # `inverse` on ARMv7 as a function of its own

`inverseFn um` is `inverse um` with its return address kept in the header
word `sT`, which `inverse` does not write: it uses no stack, so a caller
calls it (`inverseCall um`) where it would run `inverse um`, with the same
working space and registers, and `r12`, `lr` and the flags lost.
-/

@[expose] public section

namespace VG.Impl.Rsa.Arm.Keys
open VG VG.Arm

/-- `inverse um`, keeping `lr` in the header word `sT`. -/
def inverseFn (um : Bool := false) : Prog isa :=
  .seq (.block [.str .lr .r8 sT]) (.seq (inverse um) (.block [.ldr .lr .r8 sT]))

/-- The name of `inverseFn um`. -/
def inverseName (um : Bool := false) : String := if um then "vg_rsa_inverse_umaal" else "vg_rsa_inverse"

/-- A call of `inverseFn um`. -/
def inverseCall (um : Bool := false) : Prog isa := .call (inverseName um) (inverseFn um)

end VG.Impl.Rsa.Arm.Keys
