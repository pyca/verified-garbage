module

public import VerifiedGarbage.Impl.Bignum.X86.CopyArray

/-! # Preserve a factor residue in a double-width zero-extended buffer -/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

def copyPadded (n src dst : Nat) : Prog isa :=
  .seq (zerosW dst (4 * n)) (copyArray n src dst)

end VG.Impl.Bignum.X86
