import VerifiedGarbage.Impl.Rsa.X86_64.Crt

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

namespace VG.Impl.Dsa.X86_64.Arithmetic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64

/-- Fill an array with zero, including its two padding words. -/
def zero (a : Nat) : Prog isa := Crt.zeroArr a

/-- Load a possibly empty big-endian input into an array, zeroing the
padding and any unused high limbs. The pointer and length are read from
slots of the parent workspace. -/
def load (a ptr len : Nat) : Prog isa := seqs [
  zero a,
  .block [.mov .rax (.mem (hdr Crt.sLink)), .mov .rsi (.mem (Crt.ws .rax ptr)),
    .mov .rcx (.mem (Crt.ws .rax len)), .mov .rbx (.mem (hdr (sArr a))),
    .alu .test .rcx (.reg .rcx)],
  .ite .e (.block []) loadBE]

/-- Store an array as big-endian bytes. The output length is positive and
fits in the array; the pointer and length are in the parent header. -/
def store (a ptr len : Nat) : Prog isa := seqs [
  .block [.mov .rax (.mem (hdr Crt.sLink)), .mov .rsi (.mem (Crt.ws .rax ptr)),
    .mov .rcx (.mem (Crt.ws .rax len)), .mov .rbx (.mem (hdr (sArr a))),
    .mov .r15 (.imm (-1))],
  storeBE]

/-- Initialize the number 1 and R² mod m. This is repeated before operations
that reuse the R² array as the exponentiation base. -/
def constants (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block [.mov .r12 (.mem (hdr sW)), .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)],
  setWord aOne .rcx,
  R2Words.choice mul]

/-- Exponentiation of an ordinary base. The base fits the limb width but
need not be below m. `aY` receives the ordinary, reduced result. Exponent
length is positive; base length may be zero. -/
def power (mul : Nat → Nat → Nat → Prog isa) (base baseLen exp expLen : Nat) : Prog isa :=
  seqs ([constants mul, load aX base baseLen,
    mul aY aR2 aOne, mul Crt.aXc aX aR2] ++
    Crt.expLoop mul exp expLen ++ [mul aY aY aOne])

/-- An ordinary modular product. Both input values fit the limb width;
neither must be below the modulus. -/
def product (mul : Nat → Nat → Nat → Prog isa) (a aLen b bLen : Nat) : Prog isa := seqs [
  constants mul,
  load aX a aLen, load aXm b bLen,
  mul aX aX aR2, mul aXm aXm aR2,
  mul aY aX aXm, mul aY aY aOne]

/-- The arithmetic part of a byte step; array 1 contains the byte and
array 4 contains 256 R mod m. -/
def reduceStep (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (mul aY aY aR2) (Crt.addMod aY aY aX)

/-- One byte of streaming reduction: Y := (256 Y + byte) mod m. Array 4
holds 256 R mod m; array 1 is zero except for the byte in its low word.
All byte values are less than the DSA modulus. -/
def reduceByte (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block [.mov .rsi (.mem (hdr Crt.sSrc)), .movzx8 .rax (at0 .rsi),
    .mov .rbx (.mem (hdr (sArr aX))), .store (at0 .rbx) .rax,
    .alu .add .rsi (.imm 1), .store (hdr Crt.sSrc) .rsi],
  reduceStep mul,
  .block [.mov .rax (.mem (hdr Crt.sRem)), .alu .sub .rax (.imm 1),
    .store (hdr Crt.sRem) .rax]]

/-- Reduce an arbitrary-length big-endian input modulo m, including an
empty input. Unlike RSA CRT reduction this does not assume m divides
another modulus, which is essential for reducing a DSA p-residue modulo q.
The ordinary result is in aY; the input pointer and length are parent slots. -/
def reduce (mul : Nat → Nat → Nat → Prog isa) (ptr len : Nat) : Prog isa := seqs [
  constants mul,
  mul aR2 aR2 aOne,
  .block [.mov32 .rcx (.imm 8)],
  doubles aN aAcc aTmp aR2 Crt.sBit,
  zero aY, zero aX,
  .block [.mov .rax (.mem (hdr Crt.sLink)), .mov .rsi (.mem (Crt.ws .rax ptr)),
    .mov .rcx (.mem (Crt.ws .rax len)), .store (hdr Crt.sSrc) .rsi,
    .store (hdr Crt.sRem) .rcx, .alu .test .rcx (.reg .rcx)],
  .ite .e (.block []) (.loop (reduceByte mul) .ne)]

end VG.Impl.Dsa.X86_64.Arithmetic
