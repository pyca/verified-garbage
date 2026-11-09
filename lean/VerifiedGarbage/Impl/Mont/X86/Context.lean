module

public import VerifiedGarbage.Impl.Mont.X86.Exponent
public import VerifiedGarbage.Impl.Mont.X86.Inverse
public import VerifiedGarbage.Impl.Mont.X86.Dynamic
public import VerifiedGarbage.Impl.Mont.X86.Power

/-! # Runtime Montgomery workspace and exponentiation on 32-bit x86 -/

@[expose] public section
namespace VG.Impl.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86

/-- Each slot accommodates even the double-width accumulator. -/
def stride (n : Nat) : Nat := 16 * n + 8

def slot (n i : Nat) : Nat := 64 + i * stride n

def contextBytes (n : Nat) : Nat := slot n 9

def contextMod (n : Nat) : Mod := { n, mo := slot n 0, tmp := slot n 1, minv := 0 }

/-- Slots: modulus, subtraction temporary, accumulator, one, R², base,
result, conditional product, mutable exponent. The header stores the inverse
and selection mask. All offsets depend only on public widths. -/
def contextStart (n : Nat) : Prog isa :=
  .seq (.block (setupInverse (slot n 0) 0)) (one n (slot n 3))

/-- Initialize the shared prefix and a publicly chosen power of two. -/
def contextSeed (n bits : Nat) : Prog isa :=
  .seq (contextStart n) (powerTwo (contextMod n) (slot n 2) (slot n 4) bits)

/-- Ordinary power setup retains its original fixed schedule. Public-modulus
callers may reuse the seed construction with a shorter exponent. -/
def contextSetup (n : Nat) : Prog isa := contextSeed n (128 * n)

/-- Encode ordinary one and the input base using the shared R-squared. -/
def encodeBase (n : Nat) : Prog isa :=
  .seq (mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 4) (slot n 3))
    (mul (contextMod n) 0 (slot n 2) (slot n 5) (slot n 5) (slot n 4))

end VG.Impl.Mont.X86.Dynamic
