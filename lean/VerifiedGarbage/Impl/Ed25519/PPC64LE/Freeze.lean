module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Power
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Layout

/-!
# Ed25519 on PPC64LE: full reduction, zero tests and equality

`freeze a` leaves the element of slot `a` reduced fully modulo `p` at `FR`,
as X25519's final reduction does (`Impl/X25519/PPC64LE.lean`), with `FY`
for `x + 19` and the selection back into `FR`. The tests leave in `r5` a
value that is zero exactly when they hold.
-/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE
open VG.PPC64LE

def freezeCopy (a : Slot) : List Instr :=
  (List.range 8).flatMap fun k =>
    [.load .w .r7 .r6 (offset a + 4 * k), .store .w .r7 .r6 (FR + 4 * k)]

abbrev freezeA : List Instr := Impl.X25519.PPC64LE.freezeAAt FR

abbrev freezeB : List Instr := Impl.X25519.PPC64LE.freezeBAt FY

def selectSrc (k : Nat) : List Instr :=
  [.load .w .r7 .r6 (FR + 4 * k), .load .w .r5 .r6 (FY + 4 * k), .logic .xor .r5 .r5 .r7,
    .logic .and .r5 .r5 .r11, .logic .xor .r7 .r7 .r5]

def freezeSelect : List Instr :=
  (List.range 8).flatMap fun k => selectSrc k ++ [.store .w .r7 .r6 (FR + 4 * k)]

def freezeCore : List Instr :=
  freezeA ++ pass .r6 FR (ldSrc FR) ++ [.li .r8 19] ++
    pass .r6 FY (ldSrc FR) ++ freezeB ++ freezeSelect

def freeze (a : Slot) : List Instr := freezeCopy a ++ freezeCore

/-- `r5` is the sum of the words at `o`: zero exactly when they all are. -/
def sumLimb (o k : Nat) : List Instr := [.load .w .r7 .r6 (o + 4 * k), .add .r5 .r5 .r7]
def wordsZero (o : Nat) : List Instr := [.li .r5 0] ++ (List.range 8).flatMap (sumLimb o)

def fieldZero (a : Slot) : Prog isa := .seq (.block (freeze a)) (.block (wordsZero FR))
def fieldEqual (a b : Slot) : Prog isa := .seq (fieldCode [.sub 21 a b]) (fieldZero 21)

/-- `r5` is the OR of the words' differences at `a` and `b`. -/
def equalLimb (a b k : Nat) : List Instr :=
  [.load .w .r7 .r6 (a + 4 * k), .load .w .r8 .r6 (b + 4 * k),
    .logic .xor .r7 .r7 .r8, .logic .or .r5 .r5 .r7]

def wordsEqual (a b : Nat) : List Instr := [.li .r5 0] ++ (List.range 8).flatMap (equalLimb a b)

/-! ## Encoding -/

def affineOps : List FieldOp := [.mulc 0 0 15, .mulc 1 1 15]

def pointAffine : Prog isa := .seq invert (fieldCode affineOps)

/-- The sign of `x` (bit 0 of the reduced element at `FR`) at bit 31 of `r17`. -/
def pointSign : List Instr := [.load .w .r7 .r6 FR, .lsl .r17 .r7 63, .lsr .d .r17 .r17 32]

def encodeSign : List Instr :=
  [.load .w .r7 .r6 (FR + 28), .add .r7 .r7 .r17, .store .w .r7 .r6 (FR + 28)]

def pointEncode : Prog isa :=
  .seq pointAffine (.block (freeze 0 ++ pointSign ++ freeze 1 ++ encodeSign))

end VG.Impl.Ed25519.PPC64LE
