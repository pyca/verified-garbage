import VerifiedGarbage.Impl.Bignum.AArch64.Square
import VerifiedGarbage.Impl.Rsa.AArch64.Crt
import VerifiedGarbage.Impl.Rsa.AArch64.PrivChecked
import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.TCB.Rust

/-! Private unproved experiment, printed by the ISA printer. No Artifact claims. -/
namespace RsaExperiment
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

-- Four accumulator limbs, four modulus limbs and four products stay in registers.
def acc : List Reg := [.x19, .x20, .x21, .x22]
def ns : List Reg := [.x3, .x4, .x5, .x6]
def prod : List Reg := [.x23, .x24, .x25, .x26]
def saved : List Reg := acc ++ prod ++ [.x27]
def saveAll (o : Nat) : List Instr := [ldh .x16 (sArr o)] ++
  (saved.zipIdx.map fun (r,i) => st r .x16 (8*i))
def restoreAll (o : Nat) : List Instr := [ldh .x16 (sArr o)] ++
  (saved.zipIdx.map fun (r,i) => ld r .x16 (8*i))
def load4 (rs : List Reg) (p : Reg) : List Instr :=
  rs.zipIdx.map fun (r,i) => ld r p (8*i)
def store4 (rs : List Reg) (p : Reg) : List Instr :=
  rs.zipIdx.map fun (r,i) => st r p (8*i)
def lows : List Instr := List.zipWith (fun t n => Instr.mul .x t .x1 n) prod ns
def highs : List Instr := List.zipWith (fun t n => Instr.umulh t .x1 n) prod ns

def lowAdd : List Instr :=
  [.adds .x .x19 .x19 .x23, .adcs .x .x20 .x20 .x24,
   .adcs .x .x21 .x21 .x25, .adcs .x .x22 .x22 .x26]
def highShift : List Instr :=
  [.adds .x .x19 .x20 .x23, .adcs .x .x20 .x21 .x24,
   .adcs .x .x21 .x22 .x25, .adcs .x .x22 .x2 .x26]

def cancelStep (i : Nat) : List Instr :=
  [.mul .x .x1 .x19 .x15, st .x1 .x8 (8*i)] ++ lows ++ lowAdd ++
  [.adc .x .x2 .x7 .x7] ++ highs ++ highShift

def tailStep (i : Nat) : List Instr :=
  [.adc .x .x2 .x7 .x7, ld .x1 .x8 (8*i)] ++ lows ++ lowAdd ++
  [.adc .x .x2 .x2 .x7, st .x19 .x16, next .x16] ++ highs ++ highShift

def addMemory (incoming : Bool) : List Instr :=
  load4 prod .x16 ++
  (if incoming then [movi .x2 1, .subs .x .x2 .x11 .x2,
     .adcs .x .x19 .x19 .x23] else [.adds .x .x19 .x19 .x23]) ++
  [.adcs .x .x20 .x20 .x24, .adcs .x .x21 .x21 .x25,
   .adcs .x .x22 .x22 .x26]

def blockRedc : Prog isa :=
  .seq (.block [.lsr .x .x13 .x12 2, movi .x11 0])
  (.seq (.loop
    (.seq (.block (load4 acc .x8 ++ load4 ns .x10 ++
       (List.range 4).flatMap cancelStep ++
       [.addImm .x .x16 .x8 32, .addImm .x .x17 .x10 32,
        .lsr .x .x14 .x12 2, .subImm .x .x14 .x14 1]))
     (.seq (countLoop .x14 (addMemory false ++ load4 ns .x17 ++
       (List.range 4).flatMap tailStep ++ [.addImm .x .x17 .x17 32]))
      (.block (addMemory true ++ [.adc .x .x11 .x7 .x7] ++ store4 acc .x16 ++
        [.addImm .x .x8 .x8 32, .subImm .x .x13 .x13 1]))))
    (.nonzero .x .x13))
    (.block [.lsl .x .x16 .x12 3, .add .x .x16 .x8 .x16,
      st .x11 .x16, st .x7 .x16 8]))

def blockSquare (o a : Nat) : Prog isa :=
  .seq (Square.rawSquare a)
   (.seq (.block (saveAll o))
    (.seq blockRedc
     (.seq (.block (restoreAll o ++ Square.finishBases o))
      (.seq subMod selectAcc))))

def blockMm (o a b : Nat) : Prog isa :=
  if a = b ∧ o ≠ Public.aN then
    .seq (.block [ldh .x12 sW, .lsr .x .x3 .x12 3, movi .x4 3,
      .logic .and .x .x4 .x12 .x4])
      (.ite (.nonzero .x .x3)
        (.ite (.zero .x .x4) (blockSquare o a) (Public.mm o a b))
        (Public.mm o a b))
  else Public.mm o a b


namespace Eight
-- N[0] is loaded on demand so x1 can retain the extra carry bit.
def aa : List Reg := [.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26]
def nn : List Reg := [.x2,.x3,.x4,.x5,.x6,.x9,.x11]
def tt : List Reg := [.x13,.x14,.x28,.x30]
def saved : List Reg := aa ++ [.x27,.x28,.x30]
def saves (o : Nat) : List Instr := [ldh .x16 (sArr o)] ++
  (saved.zipIdx.map fun (r,i) => st r .x16 (8*i))
def restores (o : Nat) : List Instr := [ldh .x16 (sArr o)] ++
  (saved.zipIdx.map fun (r,i) => ld r .x16 (8*i))
def nsLoad : List Instr := nn.zipIdx.map fun (r,i) => ld r .x17 (8*(i+1))
def asLoad : List Instr := aa.zipIdx.map fun (r,i) => ld r .x8 (8*i)
def asStore : List Instr := aa.zipIdx.map fun (r,i) => st r .x16 (8*i)
def product (hi : Bool) (j : Nat) (t : Reg) : List Instr :=
  let ins (n : Reg) := if hi then Instr.umulh t .x27 n else Instr.mul .x t .x27 n
  if j = 0 then [ld t .x17, ins t] else [ins nn[j-1]!]
def lowChain : List Instr :=
  (List.range 4).flatMap (fun j => product false j tt[j]!) ++
  (List.range 8).flatMap (fun j =>
    [(if j = 0 then Instr.adds else Instr.adcs) .x aa[j]! aa[j]! tt[j%4]!] ++
    (if j < 4 then product false (j+4) tt[j%4]! else product true (j-4) tt[j%4]!))
def highChain : List Instr :=
  (List.range 8).flatMap (fun j =>
    [(if j = 0 then Instr.adds else Instr.adcs) .x aa[j]!
      (if j < 7 then aa[j+1]! else .x1) tt[j%4]!] ++
    (if j < 4 then product true (j+4) tt[j%4]! else []))
def cancel (i : Nat) : List Instr :=
  [.mul .x .x27 .x19 .x15, st .x27 .x8 (8*i), movi .x1 0] ++
  lowChain ++ [.adc .x .x1 .x1 .x7] ++ highChain

def tail (i : Nat) : List Instr :=
  [.adc .x .x1 .x7 .x7, ld .x27 .x8 (8*i)] ++ lowChain ++
  [.adc .x .x1 .x1 .x7, st .x19 .x16, next .x16] ++ highChain

def addMemory (pending : Bool) : List Instr :=
  (if pending then [movi .x1 1, .subs .x .x1 .x10 .x1] else []) ++
  (List.range 8).flatMap (fun i => [ld .x13 .x16 (8*i),
    (if i = 0 ∧ !pending then Instr.adds else Instr.adcs) .x aa[i]! aa[i]! .x13])

def redc : Prog isa :=
  .seq (.block [.lsr .x .x12 .x12 3, movi .x10 0])
  (.seq (.loop
    (.seq (.block (asLoad ++ [ldh .x17 (sArr Public.aN), ldh .x15 sMinv] ++ nsLoad ++
       (List.range 8).flatMap cancel ++
       [.addImm .x .x16 .x8 64, .addImm .x .x17 .x17 64,
        ldh .x15 sW, .lsr .x .x15 .x15 3, .subImm .x .x15 .x15 1]))
     (.seq (countLoop .x15 (addMemory false ++ nsLoad ++
        (List.range 8).flatMap tail ++ [.addImm .x .x17 .x17 64]))
      (.block (addMemory true ++ [.adc .x .x10 .x7 .x7] ++ asStore ++
        [.addImm .x .x8 .x8 64, .subImm .x .x12 .x12 1]))))
    (.nonzero .x .x12))
    (.block [ldh .x12 sW, .lsl .x .x16 .x12 3, .add .x .x16 .x8 .x16,
      st .x10 .x16, st .x7 .x16 8, ldh .x10 (sArr Public.aN)]))

def square (o a : Nat) : Prog isa :=
  .seq (Square.rawSquare a) (.seq (.block (saves o))
    (.seq redc (.seq (.block (restores o ++ Square.finishBases o))
      (.seq subMod selectAcc))))

def mm (o a b : Nat) : Prog isa :=
  if a = b ∧ o ≠ Public.aN then
    .seq (.block [ldh .x12 sW, .lsr .x .x3 .x12 4, movi .x4 7,
      .logic .and .x .x4 .x12 .x4])
      (.ite (.nonzero .x .x3)
        (.ite (.zero .x .x4) (square o a) (blockMm o a b))
        (blockMm o a b))
  else Public.mm o a b
end Eight


namespace CrossFour
-- Five saved registers fit in the two unused leading words and the three
-- words above the triangular product. They are restored before doubling.
def scratchHigh : List Instr := [ldh .x16 (sArr Public.aAcc), ldh .x14 sW,
  .lsl .x .x14 .x14 4, .addImm .x .x14 .x14 8, .add .x .x16 .x16 .x14]
def saves : List Instr := [ldh .x16 (sArr Public.aAcc), st .x19 .x16, st .x20 .x16 8] ++
  scratchHigh ++ [st .x21 .x16, st .x22 .x16 8, st .x23 .x16 16]
def restores : List Instr := scratchHigh ++
  [ld .x21 .x16, ld .x22 .x16 8, ld .x23 .x16 16,
   st .x9 .x16, st .x9 .x16 8, st .x9 .x16 16,
   ldh .x16 (sArr Public.aAcc), ld .x19 .x16, ld .x20 .x16 8,
   st .x9 .x16, st .x9 .x16 8]

def pairs (k : Nat) : List (Nat × Nat) :=
  ((List.range 4).flatMap fun i => (List.range 4).map fun j => (i,j)).filter
    fun (i,j) => i < j && i+j == k

def internal : List Instr := [movi .x19 0, movi .x20 0, movi .x21 0] ++
  (List.range 5).flatMap (fun k =>
    (pairs (k+1)).flatMap (fun (i,j) =>
      [ld .x1 .x11 (8*i), ld .x2 .x11 (8*j), .mul .x .x14 .x1 .x2,
       .umulh .x15 .x1 .x2, .adds .x .x19 .x19 .x14,
       .adcs .x .x20 .x20 .x15, .adc .x .x21 .x21 .x9]) ++
    [st .x19 .x8 (8*(k+1)), mov .x19 .x20, mov .x20 .x21, movi .x21 0]) ++
  [st .x19 .x8 48]

def lowProducts : List Instr :=
  [.mul .x .x1 .x23 .x3, .mul .x .x2 .x23 .x4,
   .mul .x .x14 .x23 .x5, .mul .x .x15 .x23 .x6]
def highProducts : List Instr :=
  [.umulh .x1 .x23 .x3, .umulh .x2 .x23 .x4,
   .umulh .x14 .x23 .x5, .umulh .x15 .x23 .x6]
def step (k : Nat) : List Instr :=
  [.adc .x .x7 .x9 .x9, ld .x23 .x11 (8*k)] ++ lowProducts ++
  [.adds .x .x19 .x19 .x1, .adcs .x .x20 .x20 .x2,
   .adcs .x .x21 .x21 .x14, .adcs .x .x22 .x22 .x15,
   .adc .x .x7 .x7 .x9, st .x19 .x16, next .x16] ++ highProducts ++
  [.adds .x .x19 .x20 .x1, .adcs .x .x20 .x21 .x2,
   .adcs .x .x21 .x22 .x14, .adcs .x .x22 .x7 .x15]

def offBlock : List Instr :=
  load4 acc .x16 ++ load4 ns .x17 ++ [.adds .x .x7 .x9 .x9] ++
  (List.range 4).flatMap step ++
  [ld .x1 .x16, ld .x2 .x16 8, ld .x14 .x16 16, ld .x15 .x16 24,
   movi .x7 1, .subs .x .x7 .x10 .x7,
   .adcs .x .x19 .x19 .x1, .adcs .x .x20 .x20 .x2,
   .adcs .x .x21 .x21 .x14, .adcs .x .x22 .x22 .x15,
   .adc .x .x10 .x9 .x9] ++ store4 acc .x16 ++ [.addImm .x .x17 .x17 32]

def finishCarry : List Instr :=
  [ld .x1 .x8 32, ld .x2 .x8 40, ld .x14 .x8 48,
   .adds .x .x1 .x1 .x10, .adcs .x .x2 .x2 .x9,
   .adc .x .x14 .x14 .x9, st .x1 .x8 32, st .x2 .x8 40, st .x14 .x8 48]

def cross (a : Nat) : Prog isa :=
  .seq Square.zeroWide
  (.seq (.block (saves ++ [movi .x9 0, ldh .x11 (sArr a), .lsr .x .x12 .x12 2]))
  (.seq (.loop
    (.seq (.block (internal ++ [movi .x10 0, ldh .x17 (sArr a),
      .sub .x .x16 .x11 .x17, ldh .x13 (sArr Public.aAcc),
      .addImm .x .x13 .x13 16, .add .x .x16 .x16 .x13,
      ldh .x13 sW, .lsr .x .x13 .x13 2, .sub .x .x13 .x13 .x12]))
     (.seq (.ite (.nonzero .x .x13) (countLoop .x13 offBlock) (.block []))
      (.block (finishCarry ++ [.addImm .x .x11 .x11 32,
        .addImm .x .x8 .x8 64, .subImm .x .x12 .x12 1]))))
    (.nonzero .x .x12))
    (.block (restores ++ Square.squareSetup a))))

def raw (a : Nat) : Prog isa :=
  .seq (.block (Square.squareSetup a)) (.seq (cross a) Square.diagonal)

def square (o a : Nat) : Prog isa :=
  .seq (raw a) (.seq (.block (Eight.saves o))
    (.seq Eight.redc (.seq (.block (Eight.restores o ++ Square.finishBases o))
      (.seq subMod selectAcc))))

def mm (o a b : Nat) : Prog isa :=
  if a = b ∧ o ≠ Public.aN then
    .seq (.block [ldh .x12 sW, .lsr .x .x3 .x12 4, movi .x4 7,
      .logic .and .x .x4 .x12 .x4])
      (.ite (.nonzero .x .x3)
        (.ite (.zero .x .x4) (square o a) (Eight.mm o a b))
        (Eight.mm o a b))
  else Public.mm o a b
end CrossFour


namespace MultiplyFour
-- A full product leaves two leading and two trailing scratch words unused.
def highPtr : List Instr := [ldh .x16 (sArr Public.aAcc), ldh .x14 sW,
  .lsl .x .x14 .x14 4, .addImm .x .x14 .x14 16, .add .x .x16 .x16 .x14]
def saves : List Instr := [ldh .x16 (sArr Public.aAcc), st .x19 .x16, st .x20 .x16 8] ++
  highPtr ++ [st .x21 .x16, st .x22 .x16 8]
def restores : List Instr := highPtr ++
  [ld .x21 .x16, ld .x22 .x16 8, st .x9 .x16, st .x9 .x16 8,
   ldh .x16 (sArr Public.aAcc), ld .x19 .x16, ld .x20 .x16 8,
   st .x9 .x16, st .x9 .x16 8]
def lows : List Instr :=
  [.mul .x .x2 .x1 .x3, .mul .x .x7 .x1 .x4,
   .mul .x .x14 .x1 .x5, .mul .x .x15 .x1 .x6]
def highs : List Instr :=
  [.umulh .x2 .x1 .x3, .umulh .x7 .x1 .x4,
   .umulh .x14 .x1 .x5, .umulh .x15 .x1 .x6]
def step (k : Nat) : List Instr :=
  [.adc .x .x8 .x9 .x9, ld .x1 .x11 (8*k)] ++ lows ++
  [.adds .x .x19 .x19 .x2, .adcs .x .x20 .x20 .x7,
   .adcs .x .x21 .x21 .x14, .adcs .x .x22 .x22 .x15,
   .adc .x .x8 .x8 .x9, st .x19 .x16, next .x16] ++ highs ++
  [.adds .x .x19 .x20 .x2, .adcs .x .x20 .x21 .x7,
   .adcs .x .x21 .x22 .x14, .adcs .x .x22 .x8 .x15]
def block : List Instr := load4 acc .x16 ++ load4 ns .x17 ++
  [.adds .x .x8 .x9 .x9] ++ (List.range 4).flatMap step ++
  [ld .x2 .x16, ld .x7 .x16 8, ld .x14 .x16 16, ld .x15 .x16 24,
   movi .x8 1, .subs .x .x8 .x10 .x8,
   .adcs .x .x19 .x19 .x2, .adcs .x .x20 .x20 .x7,
   .adcs .x .x21 .x21 .x14, .adcs .x .x22 .x22 .x15,
   .adc .x .x10 .x9 .x9] ++ store4 acc .x16 ++ [.addImm .x .x17 .x17 32]
def raw (a b : Nat) : Prog isa :=
  .seq (.block (Square.squareSetup a))
  (.seq Square.zeroWide
  (.seq (.block (saves ++ [movi .x9 0, ldh .x11 (sArr a), .lsr .x .x12 .x12 2]))
  (.seq (.loop
    (.seq (.block [ldh .x14 (sArr a), .sub .x .x16 .x11 .x14,
      ldh .x14 (sArr Public.aAcc), .addImm .x .x14 .x14 16,
      .add .x .x16 .x16 .x14, ldh .x17 (sArr b),
      ldh .x13 sW, .lsr .x .x13 .x13 2, movi .x10 0])
     (.seq (countLoop .x13 block)
      (.block [.addImm .x .x11 .x11 32, .subImm .x .x12 .x12 1])))
    (.nonzero .x .x12))
    (.block (restores ++ Square.squareSetup a)))))
def mul (o a b : Nat) : Prog isa :=
  .seq (raw a b) (.seq (.block (Eight.saves o))
    (.seq Eight.redc (.seq (.block (Eight.restores o ++ Square.finishBases o))
      (.seq subMod selectAcc))))
def mm (o a b : Nat) : Prog isa :=
  if a = b then CrossFour.mm o a b else if o ≠ Public.aN then
    .seq (.block [ldh .x12 sW, .lsr .x .x3 .x12 4, movi .x4 7,
      .logic .and .x .x4 .x12 .x4])
      (.ite (.nonzero .x .x3)
        (.ite (.zero .x .x4) (mul o a b) (Public.mm o a b))
        (Public.mm o a b))
  else Public.mm o a b
end MultiplyFour


namespace SelectFour
open VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Impl.Bignum.Public hiding sI sBit sV
open VG.Impl.Rsa.AArch64

def accs : List Reg := [.x8, .x9, .x10, .x11]
def inner : List Instr :=
  [.logic .eor .x .x3 .x2 .x5, movi .x4 1, .subs .x .x3 .x3 .x4] ++
  borrowMask ++
  (accs.zipIdx.flatMap fun (r,i) =>
    [ld .x1 .x16 (8*i), .logic .and .x .x1 .x1 .x15, .logic .orr .x r r .x1]) ++
  [.add .x .x16 .x16 .x6, .addImm .x .x2 .x2 1]

def blocked : Prog isa :=
  .seq (.block [ldh .x12 sW, .addImm .x .x6 .x12 2, .lsl .x .x6 .x6 3,
    .lsr .x .x13 .x12 2, ldh .x5 sNib, ldh .x17 (sArr aT), movi .x7 0])
  (.seq (.loop
    (.seq (.block ([ldh .x16 (sArr aT), .sub .x .x16 .x17 .x16,
      ldh .x3 sTab, .add .x .x16 .x16 .x3, movi .x2 0, movi .x14 16] ++
      accs.map fun r => movi r 0))
     (.seq (countLoop .x14 inner)
      (.block (store4 accs .x17 ++ [.addImm .x .x17 .x17 32,
        .subImm .x .x13 .x13 1])))) (.nonzero .x .x13))
    (.block [ldh .x3 sTab, .lsl .x .x4 .x6 4, .add .x .x3 .x3 .x4,
      sth .x3 sEnt, movi .x3 16, sth .x3 sJ]))

def select : Prog isa :=
  .seq (.block [ldh .x12 sW, .lsr .x .x3 .x12 2, movi .x4 3,
    .logic .and .x .x4 .x12 .x4])
    (.ite (.nonzero .x .x3)
      (.ite (.zero .x .x4) blocked (seqs tabSelect))
      (seqs tabSelect))
def expWin (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [mul aY aY aY, mul aY aY aY, mul aY aY aY, mul aY aY aY,
    .block [ldh .x3 sV, .lsl .x .x4 .x3 4, sth .x4 sV, .lsr .x .x3 .x3 4, movi .x4 15, .logic .and .x .x3 .x3 .x4,
      sth .x3 sNib]] ++
  [select] ++
  [mul aY aY aT,
    .block [ldh .x3 sBit, .subImm .x .x3 .x3 1, sth .x3 sBit]]

/-- `Y := Y^d` (`Y` 1 and `[aXc]` in Montgomery form) for the exponent whose
pointer and length are in `n`'s header slots `slotPtr` and `slotLen`, its
bytes most significant first, two windows a byte. -/
def expLoop (mul : Nat → Nat → Nat → Prog isa) (slotPtr slotLen : Nat) : List (Prog isa) := [
  .block [ldh .x5 sLink, ldw .x3 .x5 slotPtr, sth .x3 sExp, ldw .x3 .x5 slotLen, sth .x3 sExpLen, movi .x3 0,
    sth .x3 sI]] ++
  tabBuild mul ++ [
  .loop (seqs [
    .block [ldh .x3 sExp, ldh .x4 sI, .add .x .x3 .x3 .x4, .ldrb .x3 .x3 0, sth .x3 sV, movi .x3 2, sth .x3 sBit],
    .loop (seqs (expWin mul)) (.nonzero .x .x3),
    .block [ldh .x3 sI, .addImm .x .x3 .x3 1, sth .x3 sI, ldh .x4 sExpLen, .sub .x .x3 .x4 .x3]]) (.nonzero .x .x3)]

/-! ## The primes -/

/-- `q`: `m_q = c^dQ mod q` into `q`'s `aY`. -/
def qPhase (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  gPow mul sWsQ ++ [.block [enterQ]] ++ redc mul aY ++ copyArr aY aXc ++ [.block [leave], mul aY aXm aY,
    .block [enterQ]] ++ redc mul aY ++ expLoop mul sDq sQlen ++ [mul aY aY aOne, .block [leave]]

/-- `p`: `m_p R_p` into `p`'s `aY`, `m_q R_p` into its `aXc`, their
difference into `aT`, `qInv` again (masked) into its chunk array, and
`h = (m_p - m_q) qInv mod p` into its `aY`. -/
def pPhase (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  gPow mul sWsP ++ [.block [enterP]] ++ redc mul aY ++ copyArr aY aXc ++ [.block [leave], zeroArr aX,
    .block [ldh .x5 sWsQ, ldw .x16 .x5 (sArr aY), ldw .x12 .x5 sW, ldh .x17 (sArr aX)],
    copyWords, mul aX aX aR2, mul aX aX aY, mul aY aXm aY, .block [enterP]] ++
  redc mul aY ++ expLoop mul sDp sPlen ++ [.block [leave]] ++ [.block [enterP]] ++ redc mul aX ++
  subModArr aT aY aXc ++ loadArr aChunk sQinv sPlen ++ maskArr aChunk ++ [mul aY aT aChunk, .block [leave]]

def main (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs (nSetup mul ++ primesSetup ++ checks ++ qPhase mul ++ pPhase mul ++ finish)

/-- `vg_rsa_private_crt`: `n` checked as the public-key operation checks it
(`invalid`, on `x2` and `x3`, still `n` and `n_len`). -/
def code (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block (entry ++ invalid)) (.ite (.zero .x .x9) Precomputed.fail (main mul))


end SelectFour

def render (name sig : String) (body : Prog isa) : String :=
  let lines := printer.function body ++ printer.funcAlign.map Line.text
  let callees := VG.Rust.dedup (lines.filterMap fun | .call n => some n | _ => none)
  "#[unsafe(naked)]\n" ++ s!"pub(crate) unsafe extern \"C\" fn {name}{sig} " ++ "{\n" ++
    "    core::arch::naked_asm!(\n" ++ String.join (lines.map (VG.Rust.line printer.call)) ++
    String.join (callees.map fun n => s!"        {n} = sym {n},\n") ++ "    )\n}\n"

-- The complete existing public/private work, with only the arithmetic parameter changed.
def rsaFunctions (mul : Nat → Nat → Nat → Prog isa) : List (String × String × Prog isa) :=
  let pc := VG.Impl.Rsa.AArch64.Precompute.code mul
  let pd := VG.Impl.Rsa.AArch64.Checked.precomputedChecked mul
  let crt := SelectFour.code mul
  [("vg_rsa_public_precompute", Spec.Rsa.publicPrecomputeApi.sig.rust, pc),
   ("vg_rsa_public_precomputed_checked", Spec.Rsa.publicPrecomputedCheckedApi.sig.rust, pd),
   ("vg_rsa_private_crt", Spec.Rsa.privateCrtApi.sig.rust, crt),
   ("vg_rsa_private_checked", Spec.Rsa.privateCheckedApi.sig.rust,
    VG.Impl.Rsa.AArch64.PrivChecked.code "vg_rsa_private_crt" crt
      "vg_rsa_public_precompute" pc "vg_rsa_public_precomputed_checked" pd)]

end RsaExperiment
open RsaExperiment

/-- Diagnostic emission only: these programs have no correctness proof or Artifact.
Run from lean/: lake env lean --run RsaBlockExperiment.lean ../src/asm/aarch64/rsa.rs
This file and its output must not be merged as a verified implementation. -/
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "Expected the diagnostic RSA output path")
  let fns := rsaFunctions MultiplyFour.mm
  let original ← IO.FS.readFile path
  let mut output := original
  for (name, sig, code) in fns do
    let marker := "#[unsafe(naked)]\n" ++ s!"pub(crate) unsafe extern \"C\" fn {name}("
    let parts := output.splitOn marker
    if parts.length != 2 then throw (IO.userError s!"Expected exactly one {name}")
    let tail := parts[1]!.splitOn "\n}"
    let rest := "\n}".intercalate tail.tail!
    output := parts[0]! ++ render name sig code ++ rest
  IO.FS.writeFile path output
