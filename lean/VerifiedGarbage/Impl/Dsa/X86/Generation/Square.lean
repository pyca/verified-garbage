module
public import VerifiedGarbage.Impl.Mont.X86.Context

/-! # Squaring a primality-test residue with the prepared Montgomery context

The ordinary residue stays in slot six. Slot seven encodes it, then the
second multiplication squares and decodes together. The modulus inverse
and R squared survive every round, avoiding repeated context setup.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def ordinarySquare (n : Nat) : Prog isa :=
  .seq (mul (contextMod n) 0 (slot n 2) (slot n 7) (slot n 6) (slot n 4))
    (mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 6) (slot n 7))
end VG.Impl.Dsa.X86.Generation
