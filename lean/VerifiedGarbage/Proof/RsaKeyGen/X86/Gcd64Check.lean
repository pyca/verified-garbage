module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Body
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Setup
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Result
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Result
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Setup

/-! # Complete native 64-bit coprimality check, including precise scratch writes -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Gcd64

def checkRanges : List (Nat × Nat) := [(160, 24)] ++ ranges 2 arrays slots

end VG.Proof.RsaKeyGen.X86.Gcd64
