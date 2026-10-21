module

public import VerifiedGarbage.Impl.Rsa.X86.Div
public import VerifiedGarbage.Impl.RsaKeyGen.X86.LowWord

/-! # Preserve candidate minus one outside the native GCD scratch banks -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.CandidateSave
open VG VG.X86 VG.Impl.Rsa.X86.Div VG.Impl.RsaKeyGen.X86.LowWord

def save (n src dst : Nat) : Prog isa :=
  .seq (copyWords n src dst) (.block (decrement dst))

def restore (n src dst : Nat) : Prog isa :=
  .seq (copyWords n src dst) (.block (increment dst))

end VG.Impl.RsaKeyGen.X86.CandidateSave
