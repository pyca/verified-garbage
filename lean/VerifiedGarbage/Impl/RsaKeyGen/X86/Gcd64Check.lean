module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Setup
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Result

/-! # Check coprimality of the paired remainder and public exponent -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Gcd64
open VG VG.X86

def check (offset : Nat) : Prog isa := .seq (.block (setup offset)) (.seq code (.block result))

end VG.Impl.RsaKeyGen.X86.Gcd64
