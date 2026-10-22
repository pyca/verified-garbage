module

public import VerifiedGarbage.Impl.Rsa.AArch64

/-! The public exponent 65537 needs sixteen squares and one ordinary-input
multiply. That last product also converts out of Montgomery form. The input
and the result go a word at a time when their length is a multiple of eight
(`loadW`, `storeW`). -/

@[expose] public section
namespace VG.Impl.Rsa.AArch64.Folded
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Precomputed
open VG.Impl.Bignum.Public
def next : List Instr := [ldh .x3 sI, .subImm .x .x3 .x3 1, sth .x3 sI]
def squareStep (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
 .seq (mul aY aY aY) (.block next)
def exp65536 (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
 seqs [start, .block [movi .x3 16, sth .x3 sI],
   .loop (squareStep mul) (.nonzero .x .x3)]
def fixedLoop (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
 VG.Impl.Bignum.AArch64.seqs [start, .block [movi .x3 16, sth .x3 sI],
  .loop (squareStep mul)
   (.nonzero .x .x3), mul aY aX aY, .block [movi .x3 2, sth .x3 sStarted]]
def lengthTest : List Instr := [ldh .x3 sElen, .subImm .x .x3 .x3 3]
def bytesTest : List Instr :=
 [ldh .x8 sE, .ldrb .x3 .x8 0, .subImm .x .x3 .x3 1,
  .ldrb .x4 .x8 1, .logic .orr .x .x3 .x3 .x4, .ldrb .x4 .x8 2,
  .subImm .x .x4 .x4 1, .logic .orr .x .x3 .x3 .x4]
def fastLoop (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
 .seq (.block lengthTest)
  (.ite (.zero .x .x3)
   (.seq (.block bytesTest)
    (.ite (.zero .x .x3) (fixedLoop mul) (expLoop mul))) (expLoop mul))
def finishFused (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
 .seq (.block [ldh .x3 sStarted, .subImm .x .x3 .x3 2])
  (.ite (.zero .x .x3) (.block []) (finish mul))
def rest (mul : Nat → Nat → Nat → Prog isa) : Prog isa := VG.Impl.Bignum.AArch64.seqs [
  .block [ldh .x1 sIn, ldh .x2 sK, ldh .x8 (sArr aX)],
  loadW,
  -- The mask of `input < m`: all ones on a borrow.
  .block [ldh .x12 sW, ldh .x16 (sArr aX), ldh .x17 (sArr aN), movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7],
  cmpLoop,
  -- `-m⁻¹`, and the number 1.
  .block (([.subImm .x .x4 .x7 1, .csel .x .x15 .x7 .x4, sth .x15 sMask, ldh .x8 (sArr aN), ld .x3 .x8] : List Instr) ++ minv ++
    [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0]),
  setWord aOne,
  -- `X = input R mod m`, the exponentiation, and the result.
  mul aXm aX aR2, fastLoop mul, finishFused mul,
  .block [ldh .x8 (sArr aY), ldh .x1 sOut, ldh .x9 sK, .add .x .x1 .x1 .x9, ldh .x15 sMask],
  storeW,
  .block [ldh .x0 sMask, movi .x3 1, .logic .and .x .x0 .x0 .x3]]
def code (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
 .seq (.block (entry false)) (.seq (VG.Impl.Bignum.AArch64.seqs load)
  (.ite (.zero .x .x9) fail (rest mul)))
def checked (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
 Checked.guarded (code mul)
end VG.Impl.Rsa.AArch64.Folded
