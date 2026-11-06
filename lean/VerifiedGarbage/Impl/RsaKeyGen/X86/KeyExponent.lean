module

public import VerifiedGarbage.Impl.Bignum.X86.LoadBE
public import VerifiedGarbage.Impl.Rsa.X86.Inverse
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace

/-! # The native RSA private exponent

For an odd public exponent, divide `L = e*Q + R`, invert `R` in a two-word
bank, and form `d = Q*(e-x) + (R*(e-x)+1)/e`. Only the small correction
uses 128-bit division; the expensive inverse stays at 64 bits. All division
uses the fixed native bit schedule, never the processor's divide instruction.
Even exponents use a modulus-width inverse with a safe odd fallback.

The private exponent is array `aD`. `kOk` records whether its inverse
exists; the final key checks and small-exponent retry follow separately.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Key
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Rsa.X86 VG.Impl.Rsa.X86.Keys

def borrowMask : List Instr :=
  [.mov .eax (.imm 1), .alu .sub .eax (.reg .ebx),
    .alu .and .eax (.mem (sc kFlag)), .store (sc kOk) .eax]

def dZero : Prog isa := .block [.mov .eax (.imm 0), .store (sc kOk) .eax]

def notSlot (out input : Nat) : List Instr :=
  [.mov .eax (.imm 1), .alu .sub .eax (.mem (sc input)), .store (sc out) .eax]

/-- Compare the entire public exponent to a native constant. -/
def equalExponent (value : BitVec 32) : List Instr :=
  [.mov .eax (.mem (sc kEv)), .alu .xor .eax (.imm value),
    .alu .or .eax (.mem (sc kEvHi)), .alu .cmp .eax (.imm 0)]

/-- Test the parity of the public exponent. -/
def parityExponent : List Instr :=
  [.mov .eax (.mem (sc kEv)), .alu .and .eax (.imm 1), .alu .cmp .eax (.imm 0)]

end VG.Impl.RsaKeyGen.X86.Key
