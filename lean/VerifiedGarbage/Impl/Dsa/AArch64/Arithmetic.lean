module

public import VerifiedGarbage.Impl.Rsa.AArch64.Crt

/-!
# DSA multiword arithmetic on AArch64

Internal routines on RSA's Montgomery workspaces, as x86-64's
(`Impl/Dsa/X86_64/Arithmetic.lean`): `mul` is the chosen Montgomery
implementation, and the workspace has eight arrays and the sixteen-entry
exponentiation table of RSA's CRT operation (`Impl/Rsa/AArch64/Crt.lean`).

DSA uses these routines with odd moduli greater than 255 and at least two
limbs. The input buffers may have leading zeroes. Exponent bytes and input
bytes are read sequentially; the only conditional branches are on public
moduli, lengths and loop counters.
-/

@[expose] public section

namespace VG.Impl.Dsa.AArch64.Arithmetic

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64

/-- Fill an array with zero, including its two padding words. -/
def zero (a : Nat) : Prog isa := Crt.zeroArr a

/-- Load a nonempty big-endian component, zeroing the padding and unused
high limbs. The pointer and length are in the parent header's slots. -/
def load (a ptr len : Nat) : Prog isa := seqs (Crt.loadArr a ptr len)

/-- Store an array as big-endian bytes, unmasked. The pointer and the
positive length, which fits in the array, are in the parent header. -/
def store (a ptr len : Nat) : Prog isa :=
  .seq (.block [ldh .x5 Crt.sLink, Crt.ldw .x1 .x5 ptr, Crt.ldw .x9 .x5 len, .add .x .x1 .x1 .x9,
    ldh .x8 (sArr a), movi .x7 0, .subImm .x .x15 .x7 1]) storeBE

/-- Set an array to a small ordinary value, clearing the high limbs. -/
def small (a v : Nat) : Prog isa :=
  .seq (.block [ldh .x12 sW, movi .x9 v, movi .x13 0]) (setWord a)

/-- The number of doublings needed for R²: 128 times the limb width. -/
def r2Count : List Instr := [ldh .x13 sW, .lsl .x .x13 .x13 7]

/-- R² by doublings, including moduli with zero high limbs. -/
def doublingR2 : Prog isa := seqs [small aR2 1, .block r2Count, doubles aN aAcc aTmp aR2 sCnt]

/-- The modulus' top word into `x3`, which is zero only for padded moduli. -/
def topWord : List Instr :=
  [ldh .x12 sW, ldh .x8 (sArr aN), .subImm .x .x4 .x12 1, .lsl .x .x4 .x4 3, .add .x .x4 .x8 .x4, ld .x3 .x4]

/-- Initialize one and R². RSA's setup (`r2Steps`) handles nonzero high
limbs; padded moduli use the general doubling fallback. -/
def constants (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (small aOne 1) (.seq (.block topWord) (.ite (.zero .x .x3) doublingR2 (seqs (r2Steps mul))))

/-- Exponentiate an encoded base with accumulator R, then decode. -/
def encodedPower (mul : Nat → Nat → Nat → Prog isa) (exp expLen : Nat) : Prog isa :=
  .seq (seqs (Crt.expLoop mul exp expLen)) (mul aY aY aOne)

/-- Convert the loaded base and accumulator to Montgomery representation. -/
def encodePower (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (mul aY aR2 aOne) (.seq (mul aXm aX aR2) (seqs (Crt.copyArr Crt.aXc aXm)))

/-- Encode the loaded base, run the fixed-window exponentiation and decode
its result. R² and the number one have already been initialized. -/
def powerCore (mul : Nat → Nat → Nat → Prog isa) (exp expLen : Nat) : Prog isa :=
  .seq (encodePower mul) (encodedPower mul exp expLen)

/-- Exponentiation of an ordinary base. The base fits the limb width but
need not be below m. aY receives the ordinary, reduced result. Exponent
and base lengths are positive. -/
def power (mul : Nat → Nat → Nat → Prog isa) (base baseLen exp expLen : Nat) : Prog isa :=
  .seq (constants mul) (.seq (load aX base baseLen) (powerCore mul exp expLen))

/-- Four Montgomery steps: encode both operands, multiply, and decode. -/
def productCore (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  mul aX aX aR2, mul aXm aXm aR2,
  mul aY aXm aX, mul aY aY aOne]

/-- An ordinary modular product. Both input values fit the limb width;
neither must be below the modulus. -/
def product (mul : Nat → Nat → Nat → Prog isa) (a aLen b bLen : Nat) : Prog isa := seqs [
  constants mul,
  load aX a aLen, load aXm b bLen,
  productCore mul]

/-- The arithmetic part of a byte step; array 1 contains the byte and
array 5 contains 256 R mod m. -/
def reduceStep (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (mul aY aXm aY) (Crt.addMod aY aY aX)

/-- Read the next byte into array 1's low word and advance the source. -/
def reduceRead : List Instr :=
  [ldh .x1 Crt.sSrc, .ldrb .x3 .x1 0, ldh .x8 (sArr aX), st .x3 .x8, .addImm .x .x1 .x1 1, sth .x1 Crt.sSrc]

/-- Decrement the public remaining-byte count into `x3`, the loop's register. -/
def reduceCount : List Instr :=
  [ldh .x3 Crt.sRem, .subImm .x .x3 .x3 1, sth .x3 Crt.sRem]

/-- One byte of streaming reduction: Y := (256 Y + byte) mod m. Array 5
holds 256 R mod m; array 1 is zero except for the byte in its low word.
All byte values are less than the DSA modulus. -/
def reduceByte (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block reduceRead,
  reduceStep mul,
  .block reduceCount]

/-- Prepare 256R for byte reduction (in array 5, as the multiplier of an
operand tuple the Montgomery backends cover) and clear the accumulator and
byte array. -/
def reduceSetup (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  constants mul,
  mul aR2 aR2 aOne,
  .block [movi .x13 8],
  doubles aN aAcc aTmp aR2 sCnt,
  seqs (Crt.copyArr aXm aR2),
  zero aY, zero aX]

/-- Load the source pointer and public length into the child workspace;
the length into `x3`, the branch's register. -/
def reduceInit (ptr len : Nat) : List Instr :=
  [ldh .x5 Crt.sLink, Crt.ldw .x1 .x5 ptr, Crt.ldw .x3 .x5 len, sth .x1 Crt.sSrc, sth .x3 Crt.sRem]

/-- Reduce an arbitrary-length big-endian input modulo m, including an
empty input. The ordinary result is in aY; the input pointer and length are
parent slots. -/
def reduce (mul : Nat → Nat → Nat → Prog isa) (ptr len : Nat) : Prog isa :=
  .seq (reduceSetup mul) (seqs [
    .block (reduceInit ptr len),
    .ite (.zero .x .x3) (.block []) (.loop (reduceByte mul) (.nonzero .x .x3))])

end VG.Impl.Dsa.AArch64.Arithmetic
