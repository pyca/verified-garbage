module

public import VerifiedGarbage.Impl.Rsa.X86_64.Crt

/-!
# DSA multiword arithmetic on x86-64

Internal routines on the shared Montgomery workspace. `mul` is the chosen
Montgomery implementation; callers must be generic over it so the ADX
implementation propagates to DSA too. The workspace has eight arrays and
the sixteen-entry exponentiation table used by RSA's private operation.

DSA uses these routines with odd moduli greater than 255 and at least two
limbs. The input buffers may have leading zeroes. Exponent bytes and input
bytes are read sequentially; the only conditional branches are on public
lengths and loop counters. These are implementation definitions, not
registered artifacts: registration requires the complete sign/verify proofs.
-/

@[expose] public section

namespace VG.Impl.Dsa.X86_64.Arithmetic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64

/-- Fill an array with zero, including its two padding words. -/
def zero (a : Nat) : Prog isa := Crt.zeroArr a

/-- Load a nonempty big-endian component, zeroing the padding and unused
high limbs. All DSA components have positive public widths; empty digests
are handled separately by reduce. The source is in the parent header. -/
def load (a ptr len : Nat) : Prog isa := seqs (Crt.loadArr a ptr len)

/-- Store an array as big-endian bytes. The output length is positive and
fits in the array; the pointer and length are in the parent header. -/
def store (a ptr len : Nat) : Prog isa := seqs [
  .block [.mov .rax (.mem (hdr Crt.sLink)), .mov .rsi (.mem (Crt.ws .rax ptr)),
    .mov .rcx (.mem (Crt.ws .rax len)), .mov .rbx (.mem (hdr (sArr a))),
    .mov .r15 (.imm (-1))],
  storeBE]

/-- Set an array to a small ordinary value, clearing the high limbs. -/
def small (a : Nat) (v : BitVec 32) : Prog isa :=
  .seq (.block [.mov .r12 (.mem (hdr sW)), .mov32 .rdx (.imm v), .mov32 .rcx (.imm 0)])
    (setWord a .rcx)

/-- The number of doublings needed for R²: 128 times the limb width. -/
def r2Count : List Instr :=
  [.mov .rcx (.mem (hdr sW)),
    .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
    .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
    .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
    .alu .add .rcx (.reg .rcx)]

/-- Initialize the number 1 and R² mod m by a public number of doublings.
Unlike RSA's normalized-modulus shortcut this also handles zero high limbs.
The modulus is greater than 1. -/
def constants : Prog isa := seqs [
  small aOne 1, small aR2 1,
  .block r2Count,
  doubles aN aAcc aTmp aR2 sCnt]

/-- Exponentiate an encoded base with accumulator R, then decode. -/
def encodedPower (mul : Nat → Nat → Nat → Prog isa) (exp expLen : Nat) : Prog isa :=
  .seq (seqs (Crt.expLoop mul exp expLen)) (mul aY aY aOne)

/-- Convert the loaded base and accumulator to Montgomery representation. -/
def encodePower (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (mul aY aR2 aOne)
    (.seq (mul aXm aX aR2) (seqs (Crt.copyArr Crt.aXc aXm)))

/-- Encode the loaded base, run the fixed-window exponentiation and decode
its result. R² and the number one have already been initialized. -/
def powerCore (mul : Nat → Nat → Nat → Prog isa) (exp expLen : Nat) : Prog isa :=
  .seq (encodePower mul) (encodedPower mul exp expLen)

/-- Exponentiation of an ordinary base. The base fits the limb width but
need not be below m. aY receives the ordinary, reduced result. Exponent
and base lengths are positive. -/
def power (mul : Nat → Nat → Nat → Prog isa) (base baseLen exp expLen : Nat) : Prog isa :=
  .seq constants (.seq (load aX base baseLen) (powerCore mul exp expLen))

/-- Four Montgomery steps: encode both operands, multiply, and decode. -/
def productCore (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  mul aX aX aR2, mul aXm aXm aR2,
  mul aY aXm aX, mul aY aY aOne]

/-- An ordinary modular product. Both input values fit the limb width;
neither must be below the modulus. -/
def product (mul : Nat → Nat → Nat → Prog isa) (a aLen b bLen : Nat) : Prog isa := seqs [
  constants,
  load aX a aLen, load aXm b bLen,
  productCore mul]

/-- The arithmetic part of a byte step; array 1 contains the byte and
array 4 contains 256 R mod m. -/
def reduceStep (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (mul aY aR2 aY) (Crt.addMod aY aY aX)

/-- Read the next byte and advance the source pointer. -/
def reduceRead : List Instr :=
  [.mov .rsi (.mem (hdr Crt.sSrc)), .movzx8 .rax (at0 .rsi),
    .mov .rbx (.mem (hdr (sArr aX))), .store (at0 .rbx) .rax,
    .alu .add .rsi (.imm 1), .store (hdr Crt.sSrc) .rsi]

/-- Decrement the public remaining-byte count, setting the loop condition. -/
def reduceCount : List Instr :=
  [.mov .rax (.mem (hdr Crt.sRem)), .alu .sub .rax (.imm 1), .store (hdr Crt.sRem) .rax]

/-- One byte of streaming reduction: Y := (256 Y + byte) mod m. Array 4
holds 256 R mod m; array 1 is zero except for the byte in its low word.
All byte values are less than the DSA modulus. -/
def reduceByte (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block reduceRead,
  reduceStep mul,
  .block reduceCount]

/-- Prepare 256R for byte reduction and clear the accumulator and byte array. -/
def reduceSetup (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  constants,
  mul aR2 aR2 aOne,
  .block [.mov32 .rcx (.imm 8)],
  doubles aN aAcc aTmp aR2 sCnt,
  zero aY, zero aX]

/-- Load the source pointer and public length into the child workspace. -/
def reduceInit (ptr len : Nat) : List Instr :=
  [.mov .rax (.mem (hdr Crt.sLink)), .mov .rsi (.mem (Crt.ws .rax ptr)),
    .mov .rcx (.mem (Crt.ws .rax len)), .store (hdr Crt.sSrc) .rsi,
    .store (hdr Crt.sRem) .rcx, .alu .test .rcx (.reg .rcx)]

/-- Reduce an arbitrary-length big-endian input modulo m, including an
empty input. Unlike RSA CRT reduction this does not assume m divides
another modulus, which is essential for reducing a DSA p-residue modulo q.
The ordinary result is in aY; the input pointer and length are parent slots. -/
def reduce (mul : Nat → Nat → Nat → Prog isa) (ptr len : Nat) : Prog isa :=
  .seq (reduceSetup mul) (seqs [
    .block (reduceInit ptr len),
    .ite .e (.block []) (.loop (reduceByte mul) .ne)])

end VG.Impl.Dsa.X86_64.Arithmetic
