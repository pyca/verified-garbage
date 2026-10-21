module

public import VerifiedGarbage.Impl.Mont.X86

/-! # Transfer the modular remainder and public exponent into the native GCD banks -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Impl.Mont.X86

def remainderInput : List Instr :=
  [.mov .eax (.reg .ecx), .mov .edx (.reg .ebx), .store (sc 160) .eax, .store (sc 164) .edx]

def exponentInput (offset : Nat) : List Instr :=
  [.mov .eax (.mem (sc offset)), .mov .edx (.mem (sc (offset + 4))),
    .store (sc 176) .eax, .store (sc 180) .edx]

def setup (offset : Nat) : List Instr := remainderInput ++ exponentInput offset

end VG.Impl.RsaKeyGen.X86.Gcd64
