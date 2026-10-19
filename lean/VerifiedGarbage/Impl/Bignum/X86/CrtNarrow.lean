module

public import VerifiedGarbage.Impl.Bignum.X86.CrtLayout
public import VerifiedGarbage.Impl.Bignum.X86.CopyArray
public import VerifiedGarbage.Impl.Bignum.X86.CopyPadded
public import VerifiedGarbage.Impl.Bignum.X86.CheckedPrimePower
public import VerifiedGarbage.Impl.Bignum.X86.CheckedPreparePrime
public import VerifiedGarbage.Impl.Bignum.X86.ReduceOperand
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Impl.Mont.X86.Window

/-! # A factor's exponentiation at half the modulus's width

The factors of a balanced key have half the modulus's words. When a factor's
public length fits `half n` words, the input is reduced modulo the factor at
the modulus's width, and the exponentiation runs in a context of `half n`
words, laid out within the modulus-width context's slots (whose contents are
dead between the phases), for a quarter of the work per multiplication and
half the exponent's bits. A longer factor takes the modulus-width code.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

/-- The words of a balanced key's factors. -/
def half (n : Nat) : Nat := (n + 1) / 2

/-- The input modulo the (sanitized) factor, at the modulus's width, into `output`. -/
def reduceInput (n prime output : Nat) : Prog isa :=
  .seq (copyArray n (slot n prime) (slot n 0)) <|
  .seq (copyArray n (slot n inputSlot) (slot n 5)) <|
  .seq (checkedPreparePrime n) <|
  .seq (reduceOperand n 5) (copyArray n (slot n 5) (slot n output))

/-- The factor, the reduced input and the exponent, at `half n` words, into the
narrow context. -/
def loadNarrow (n prime exponent output : Nat) : Prog isa :=
  .seq (copyArray (half n) (slot n prime) (slot (half n) 0)) <|
  .seq (copyArray (half n) (slot n output) (slot (half n) 5))
    (copyArray (half n) (slot n exponent) (slot (half n) 8))

/-- The table of the narrow exponentiation's base powers: past the
modulus-width layout's slots. -/
def tableOffset (n : Nat) : Nat := slot n 20

/-- `checkedPrimePower`, by fixed 4-bit windows. -/
def checkedWindowPower (n tab : Nat) : Prog isa :=
  .seq (primeMask n) (.seq (preparePrime n) (windowExponentiate n (2 * n) tab))

def narrowPower (n prime exponent output : Nat) : Prog isa :=
  .seq (reduceInput n prime output) <|
  .seq (loadNarrow n prime exponent output) <|
  .seq (checkedWindowPower (half n) (tableOffset n)) <|
  .seq (zerosW (slot n output) (4 * n)) (copyArray (half n) (slot (half n) 6) (slot n output))

/-- CF is set when the factor's length (the argument `lenArg`) fits `half n` words. -/
def lengthFits (n lenArg : Nat) : List Instr :=
  [.mov .eax (.mem (PublicFn.argument lenArg)),
   .alu .cmp .eax (.imm (BitVec.ofNat 32 (8 * half n + 1)))]

end VG.Impl.Bignum.X86.Crt
