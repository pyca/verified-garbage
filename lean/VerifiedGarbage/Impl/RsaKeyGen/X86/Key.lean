module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateArgs
public import VerifiedGarbage.Impl.Mont.X86.Compact

/-! # RSA key assembly on the native 32-bit cdecl ABI

Each supported width instantiates native paired-word products, a prime-width
LCM GCD and CRT inverse, and the public-width inverse for an odd exponent.
Only the public width, the public exponent and the released retry status
select different control paths. The working bank is initialized before use.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Key
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.Keys

def enter : Prog isa :=
  .seq (.block [.mov .edi (.mem (CandidateArgs.arg 16))]) (CandidateArgs.copies 18)

end VG.Impl.RsaKeyGen.X86.Key
