module

public import VerifiedGarbage.Impl.Bignum.AArch64.BlockedRedc

/-! Shared fixed-slot RSA squares. The separately reviewed helper contracts cover both
fixed slots; the arithmetic and its width guards are unchanged. -/

@[expose] public section

namespace VG.Impl.Bignum.AArch64.SquareCall
open VG VG.AArch64

/-- Preserve the caller's return address in a caller-saved vector register
that the integer-only arithmetic does not touch. -/
def save : List Instr := [.vop (.ins .d2 .v31 0 .x30)]
def restore : List Instr := [.umov .x .x30 .v31 0]

def call (name : String) (body : Prog isa) : Prog isa :=
  .seq (.block save) (.seq (.call name body) (.block restore))

/-- Only the two fixed in-place squares are outlined. -/
def mm (o a b : Nat) : Prog isa :=
  if o = a ∧ a = b ∧ (o = 4 ∨ o = 6) then
    call s!"vg_rsa_square_{o}_{o}" (BlockedRedc.mm o o o)
  else BlockedRedc.mm o a b

end VG.Impl.Bignum.AArch64.SquareCall
