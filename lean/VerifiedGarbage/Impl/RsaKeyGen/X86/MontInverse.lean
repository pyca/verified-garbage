module

public import VerifiedGarbage.Impl.Mont.X86.Inverse
public import VerifiedGarbage.Impl.RsaKeyGen.X86.InverseLift

/-! # Prepare the full negative Montgomery inverse with native 32-bit products -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.MontInverse
open VG VG.X86

def code (modulus inverse : Nat) : Prog isa :=
  .seq (.block (VG.Impl.Mont.X86.Dynamic.setupInverse modulus inverse))
    (.block (InverseLift.setup modulus inverse))

end VG.Impl.RsaKeyGen.X86.MontInverse
