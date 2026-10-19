module

public import VerifiedGarbage.Impl.Bignum.Layout
public import VerifiedGarbage.Impl.Mont.X86.Inverse
public import VerifiedGarbage.Impl.Mont.X86.Power

/-! # Compact Montgomery workspace for public RSA on i686

The existing public RSA contract provides eight arrays of `n + 2` 64-bit
words after a 256-byte header. The multiplication accumulator occupies
arrays two and three together; all other operands occupy one array.
Array five holds R² during setup and the masked multiplication candidate
during exponentiation. Reusing it keeps all temporary values within the
existing public RSA scratch-space contract.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86

def stride (n : Nat) : Nat := 8 * n + 16
def slot (n i : Nat) : Nat := hdrBytes + i * stride n
def size (n : Nat) : Nat := slot n 8
def modulus (n : Nat) : Mod := { n, mo := slot n 0, tmp := slot n 1, minv := 0 }
def inverseOffset : Nat := 8 * sMinv

/-- Arrays two and three are reserved for the double-width accumulator. -/
def operand (i : Nat) : Prop := i < 8 ∧ i ≠ 2 ∧ i ≠ 3

def multiply (n o a b : Nat) : Prog isa :=
  Dynamic.mul (modulus n) inverseOffset (slot n 2) (slot n o) (slot n a) (slot n b)

/-- Set up the low-word Montgomery inverse, one, and R² modulo the modulus. -/
def setup (n : Nat) : Prog isa :=
  .seq (.block (Dynamic.setupInverse (slot n 0) inverseOffset))
    (.seq (Dynamic.one n (slot n 4))
      (Dynamic.powerTwo (modulus n) (slot n 2) (slot n 5) (128 * n)))

end VG.Impl.Bignum.X86.PublicContext
