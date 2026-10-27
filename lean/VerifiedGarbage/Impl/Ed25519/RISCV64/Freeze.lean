module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.Power

/-!
# Ed25519 on RISC-V: full reduction, zero tests and equality

As on PPC64LE (`Impl/Ed25519/PPC64LE/Freeze.lean`): `freeze a` leaves the
element of slot `a` reduced fully modulo `p` at `FR`, as X25519's final
reduction does (`Impl/X25519/RISCV64.lean`), with `FY` for `x + 19` and the
selection back into `FR`. The tests leave in `a2` a value that is zero
exactly when they hold. The sign of an encoding is in `t6` between the
freezes of its coordinates, which do not write it.
-/

@[expose] public section

namespace VG.Impl.Ed25519.RISCV64
open VG.RISCV64
open VG.Impl.X25519.RISCV64 (pass ldSrc)

/-- The freeze's result and temporary. -/
def FR : Nat := ACC
def FY : Nat := ACC + 32

def freezeCopy (a : Slot) : List Instr :=
  (List.range 8).flatMap fun k =>
    [.load .w .a4 .a3 (offset a + 4 * k), .store .w .a4 .a3 (FR + 4 * k)]

abbrev freezeA : List Instr := Impl.X25519.RISCV64.freezeAAt FR

abbrev freezeB : List Instr := Impl.X25519.RISCV64.freezeBAt FY

def selectSrc (k : Nat) : List Instr :=
  [.load .w .a4 .a3 (FR + 4 * k), .load .w .a2 .a3 (FY + 4 * k), .logic .xor .a2 .a2 .a4,
    .logic .and .a2 .a2 .t0, .logic .xor .a4 .a4 .a2]

def freezeSelect : List Instr :=
  (List.range 8).flatMap fun k => selectSrc k ++ [.store .w .a4 .a3 (FR + 4 * k)]

def freezeCore : List Instr :=
  freezeA ++ pass .a3 FR (ldSrc FR) ++ [.li .a5 19] ++
    pass .a3 FY (ldSrc FR) ++ freezeB ++ freezeSelect

def freeze (a : Slot) : List Instr := freezeCopy a ++ freezeCore

/-- `a2` is the sum of the words at `o`: zero exactly when they all are. -/
def sumLimb (o k : Nat) : List Instr := [.load .w .a4 .a3 (o + 4 * k), .add .a2 .a2 .a4]
def wordsZero (o : Nat) : List Instr := [.li .a2 0] ++ (List.range 8).flatMap (sumLimb o)

def fieldZero (a : Slot) : Prog isa := .seq (.block (freeze a)) (.block (wordsZero FR))
def fieldEqual (a b : Slot) : Prog isa := .seq (fieldCode [.sub 21 a b]) (fieldZero 21)

/-- `a2` is the OR of the words' differences at `a` and `b`. -/
def equalLimb (a b k : Nat) : List Instr :=
  [.load .w .a4 .a3 (a + 4 * k), .load .w .a5 .a3 (b + 4 * k),
    .logic .xor .a4 .a4 .a5, .logic .or .a2 .a2 .a4]

def wordsEqual (a b : Nat) : List Instr := [.li .a2 0] ++ (List.range 8).flatMap (equalLimb a b)

/-! ## Encoding -/

def affineOps : List FieldOp := [.mulc 0 0 15, .mulc 1 1 15]

def pointAffine : Prog isa := .seq invert (fieldCode affineOps)

/-- The sign of `x` (bit 0 of the reduced element at `FR`) at bit 31 of `t6`. -/
def pointSign : List Instr :=
  [.load .w .a4 .a3 FR, .shift .sll .d .t6 .a4 63, .shift .srl .d .t6 .t6 32]

def encodeSign : List Instr :=
  [.load .w .a4 .a3 (FR + 28), .add .a4 .a4 .t6, .store .w .a4 .a3 (FR + 28)]

def pointEncode : Prog isa :=
  .seq pointAffine (.block (freeze 0 ++ pointSign ++ freeze 1 ++ encodeSign))

end VG.Impl.Ed25519.RISCV64
