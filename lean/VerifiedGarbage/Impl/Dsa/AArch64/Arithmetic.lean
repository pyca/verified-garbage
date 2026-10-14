module

public import VerifiedGarbage.Impl.Rsa.AArch64.Crt

/-! # DSA arithmetic on the AArch64 Montgomery workspace

These internal programs are registered only through the complete DSA contracts.
All input bytes are visited sequentially, with public loop bounds.
-/

@[expose] public section

namespace VG.Impl.Dsa.AArch64.Arithmetic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64

def zero (a : Nat) : Prog isa := Crt.zeroArr a

def load (a ptr len : Nat) : Prog isa := seqs (Crt.loadArr a ptr len)

def store (a ptr len : Nat) : Prog isa := seqs [
  .block [ldh .x5 Crt.sLink, Crt.ldw .x1 .x5 ptr, Crt.ldw .x9 .x5 len,
    .add .x .x1 .x1 .x9, ldh .x8 (sArr a), movi .x15 0, .subImm .x .x15 .x15 1],
  storeBE]

def small (a : Nat) (v : Nat) : Prog isa :=
  .seq (.block [ldh .x12 sW, movi .x9 v, movi .x13 0]) (setWord a)

def r2Count : List Instr := [ldh .x13 sW, .lsl .x .x13 .x13 7]

/-- Doubling works even when the modulus has leading zero limbs. -/
def doublingR2 : Prog isa := seqs [
  small aR2 1, .block r2Count, doubles aN aAcc aTmp aR2 sCnt]

/-- The modulus' top word into `x3`, which is zero only for padded moduli. -/
def topWord : List Instr :=
  [ldh .x12 sW, ldh .x8 (sArr aN), .subImm .x .x4 .x12 1, .lsl .x .x4 .x4 3, .add .x .x4 .x8 .x4, ld .x3 .x4]

/-- One and R². RSA's setup (`r2Steps`: at most `64 + w` doublings and six
squares) when the modulus' top word is nonzero; padded moduli use the
general doubling fallback. -/
def constants (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (small aOne 1) (.seq (.block topWord) (.ite (.zero .x .x3) doublingR2 (seqs (r2Steps mul))))

def encodedPower (mul : Nat → Nat → Nat → Prog isa) (exp expLen : Nat) : Prog isa :=
  .seq (seqs (Crt.expLoop mul exp expLen)) (mul aY aY aOne)

def encodePower (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (mul aY aR2 aOne)
    (.seq (mul aXm aX aR2) (seqs (Crt.copyArr Crt.aXc aXm)))

def powerCore (mul : Nat → Nat → Nat → Prog isa) (exp expLen : Nat) : Prog isa :=
  .seq (encodePower mul) (encodedPower mul exp expLen)

def power (mul : Nat → Nat → Nat → Prog isa) (base baseLen exp expLen : Nat) : Prog isa :=
  .seq (constants mul) (.seq (load aX base baseLen) (powerCore mul exp expLen))

def productCore (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  mul aX aX aR2, mul aXm aXm aR2, mul aY aXm aX, mul aY aY aOne]

def product (mul : Nat → Nat → Nat → Prog isa) (a aLen b bLen : Nat) : Prog isa := seqs [
  constants mul, load aX a aLen, load aXm b bLen, productCore mul]

/-- Array Xm holds 256R, X the next input byte, and Y the ordinary residue. -/
def reduceStep (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (mul aY aXm aY) (Crt.addMod aY aY aX)

def reduceRead : List Instr :=
  [ldh .x1 Crt.sSrc, .ldrb .x3 .x1 0, ldh .x8 (sArr aX), st .x3 .x8,
    .addImm .x .x1 .x1 1, sth .x1 Crt.sSrc]

def reduceCount : List Instr :=
  [ldh .x3 Crt.sRem, .subImm .x .x3 .x3 1, sth .x3 Crt.sRem]

def reduceByte (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block reduceRead, reduceStep mul, .block reduceCount]

def reduceSetup (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  constants mul, small aX 256, mul aXm aX aR2, zero aY, zero aX]

def reduceInit (ptr len : Nat) : List Instr :=
  [ldh .x5 Crt.sLink, Crt.ldw .x1 .x5 ptr, Crt.ldw .x3 .x5 len,
    sth .x1 Crt.sSrc, sth .x3 Crt.sRem]

def reduce (mul : Nat → Nat → Nat → Prog isa) (ptr len : Nat) : Prog isa :=
  .seq (reduceSetup mul) (seqs [
    .block (reduceInit ptr len),
    .ite (.zero .x .x3) (.block []) (.loop (reduceByte mul) (.nonzero .x .x3))])

end VG.Impl.Dsa.AArch64.Arithmetic
