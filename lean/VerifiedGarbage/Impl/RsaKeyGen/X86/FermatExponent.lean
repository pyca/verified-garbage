module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Trial

/-! # Coprimality with the usual RSA public exponent

The caller supplies c-1 at EDI and its public end in the trial frame.
65535 is -65537⁻¹ modulo 2³². The whole-word trial kernel returns its
divisibility bit, which is inverted to return the coprimality bit.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.FermatExponent
open VG VG.X86

def init : List Instr := [.mov .ebx (.imm 65537), .mov .esi (.imm 65535), .mov .ebp (.imm 0)]

def code (endOffset : Nat) : Prog isa :=
  .seq (.block init) (.seq (Trial.divisor endOffset) (.block [.alu .xor .eax (.imm 1)]))

end VG.Impl.RsaKeyGen.X86.FermatExponent
