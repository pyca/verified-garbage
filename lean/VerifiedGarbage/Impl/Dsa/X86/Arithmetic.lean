module
public import VerifiedGarbage.Impl.Mont.X86.Context


/-! # Ordinary-residue arithmetic using the runtime Montgomery context -/

@[expose] public section
namespace VG.Impl.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

/-- Multiply ordinary integers in slots five and eight, producing slot six.
The first multiplication encodes one operand, the second removes that factor
of R while multiplying. Either input may fill its entire padded width. -/
def ordinaryMul (n : Nat) : Prog isa :=
  .seq (mul (contextMod n) 0 (slot n 2) (slot n 7) (slot n 5) (slot n 4))
    (mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 8) (slot n 7))

/-- Add reduced ordinary integers in slots five and eight. -/
def ordinaryAdd (n : Nat) : Prog isa :=
  addW (contextMod n) (slot n 2) (slot n 6) (slot n 5) (slot n 8)

end VG.Impl.Dsa.X86
