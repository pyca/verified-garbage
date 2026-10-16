module

public import VerifiedGarbage.Impl.Rsa.AArch64.WindowPhases

@[expose] public section
namespace VG.Impl.Rsa.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

/-- Five-bit windows are profitable when both primes have complete 64-byte blocks.
The lengths are public; other shapes retain the four-bit implementation. -/
def lengthGuard : List Instr :=
  [ldh .x9 Public.sK, .lsr .x .x9 .x9 7,
    ldh .x10 VG.Impl.Bignum.Crt.sPlen, ldh .x11 VG.Impl.Bignum.Crt.sQlen,
    .logic .orr .x .x10 .x10 .x11, movi .x11 63, .tst .x .x10 .x11,
    movi .x11 0, .cselc .x .x9 .x9 .x11 .eq]

/-- Retain the existing workspace layout below 1024-bit moduli. -/
def dispatch (window : Prog isa) (select : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block lengthGuard) (.ite (.zero .x .x9) (Crt.main mul) (main window select mul))

def code (window : Prog isa) (select : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block (Crt.entry ++ invalid))
    (.ite (.zero .x .x9) Precomputed.fail (dispatch window select mul))

end VG.Impl.Rsa.AArch64.WindowFive
