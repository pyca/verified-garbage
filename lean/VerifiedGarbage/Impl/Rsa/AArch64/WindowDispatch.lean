module

public import VerifiedGarbage.Impl.Rsa.AArch64.WindowPhases

@[expose] public section
namespace VG.Impl.Rsa.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

def lengthGuard : List Instr := [ldh .x9 Public.sK, .lsr .x .x9 .x9 7]

/-- Retain the existing workspace layout below 1024-bit moduli. -/
def dispatch (window : Prog isa) (select : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block lengthGuard) (.ite (.zero .x .x9) (Crt.main mul) (main window select mul))

def code (window : Prog isa) (select : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block (Crt.entry ++ invalid))
    (.ite (.zero .x .x9) Precomputed.fail (dispatch window select mul))

end VG.Impl.Rsa.AArch64.WindowFive
