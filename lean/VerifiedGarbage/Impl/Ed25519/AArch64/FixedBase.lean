module

public import VerifiedGarbage.Impl.Ed25519.AArch64.Pairs
public import VerifiedGarbage.Impl.Ed25519.AArch64.FieldMemory
public import VerifiedGarbage.Impl.Ed25519.AArch64.PointEncode
public import VerifiedGarbage.Impl.Ed25519.AArch64.Scalar
public import VerifiedGarbage.Impl.Ed25519.CombTable16

/-!
# Ed25519 on AArch64: base-point multiplication

`vg_ed25519_scalar_base(out = x0, scalar = x1, scratch = x2)`, an internal function: `[s]B`,
encoded. The scalar's 64 nibbles `n_i` give `[s]B = Σ d_i [16^i]B + [17 G]B` for the digits
`d_i = n_i - 8`, from `-8` to `7`, and `G = 8 Σ_{j < 32} 256^j`, as on RISC-V
(`Impl/Ed25519/RISCV64/Comb.lean`). Table `i` of the static `combSym` holds `[k]([16^i]B)` for
`k = 1 … 8` (`combCached64`), each as the twelve words of `[Y - X, Y + X, 2dT]` with `Z = 1`: 768
bytes a table. The accumulator (slots 0–3) starts at `[17 G]B`, and step `i` adds digit `i`'s entry.

* The digits are secret. A step loads every word of its table into registers and keeps, by
  conditional selects on a counter from the digit's magnitude down, the words of the one entry
  (`select`); the identity's `[1, 1, 0]` stays for the magnitude 0. A negative digit's entry is
  negated under the sign (`negate`): `Y - X` and `Y + X` exchanged, and `p - 2dT` for `2dT`. The
  addresses depend on the working space's, the static's and the step alone.
* The addition (`addEntry`) is the unified one for an affine second point, with seven products;
  those that share an operand follow each other, and leave it in registers.
* The scalar's nibbles are first spread over the 64 bytes at `NIB` of the working space.

`x1` is the address in the static and `x19` the step, both public; `x10` is zero.
-/

@[expose] public section

namespace VG.Impl.Ed25519.AArch64

open VG.AArch64
open VG.Impl.Ed25519.AArch64.Pairs

/-! ## The tables -/

/-- The static holding the tables. -/
def combSym : String := "VG_ED25519_COMB"

/-- Coordinate `c` of a cached entry: `Y - X` (`c = 0`), `Y + X` (`c = 1`), `2dT` (`c = 2`). -/
def combCoord (p : Spec.Ed25519.Point) (c : Nat) : Spec.X25519.Fe :=
  if c = 0 then p.X else if c = 1 then p.Y else p.Z

/-- Word `j < 4` of coordinate `c` of entry `m + 1` of table `i`. -/
def combPart (i m c j : Nat) : Nat := (combCoord (combCached64 i (m + 1)) c).val / 2 ^ (64 * j) % 2 ^ 64

/-- Word `q` of the tables: table `i = q / 96` takes 96, entry `m + 1` of it 12
(`m = q % 96 / 12`), coordinate `c` 4 (`c = q % 12 / 4`). -/
def combWord (q : Nat) : BitVec 64 := BitVec.ofNat 64 (combPart (q / 96) (q % 96 / 12) (q % 12 / 4) (q % 4))

/-- The words of the 64 tables, as the static `combSym` holds them. -/
def combWords : List (BitVec 64) := (List.range (64 * 96)).map combWord

/-- The static the comb reads. -/
def combConsts : List (String × List (BitVec 64)) := [(combSym, combWords)]

/-! ## The digits -/

/-- Byte of the working space from which on the 64 nibbles of the scalar are, one to a byte. -/
def NIB : Nat := 768

/-- The nibbles of byte `k` of the scalar, with 15 in `x11`. -/
def nibbleByte (k : Nat) : List Instr :=
  [.ldrb .x8 .x1 k, .lsr .x .x9 .x8 4, .logic .and .x .x8 .x8 .x11,
    .strb .x8 .x0 (NIB + 2 * k), .strb .x9 .x0 (NIB + (2 * k + 1))]

/-- The scalar's nibbles. -/
def scalarNibbles : List Instr := ([.movz .x .x11 15 0] : List Instr) ++ (List.range 32).flatMap nibbleByte

/-- The magnitude of digit `x19` into `x8`, and its sign's mask (all ones for a negative digit)
into `x9`; with zero in `x10`. -/
def digit : List Instr :=
  [.add .x .x8 .x0 .x19, .ldrb .x8 .x8 NIB, .subImm .x .x8 .x8 8, .lsr .x .x9 .x8 63,
    .sub .x .x9 .x10 .x9, .logic .eor .x .x8 .x8 .x9, .sub .x .x8 .x8 .x9]

/-! ## The entry -/

/-- The registers of the entry's twelve words. -/
def entryReg (q : Nat) : Reg :=
  [Reg.x4, .x5, .x6, .x7, .x12, .x13, .x14, .x15, .x21, .x22, .x23, .x24].getD q .x24

/-- The identity's entry, `[1, 1, 0]`. -/
def selectInit : List Instr :=
  (List.range 12).map fun q => .movz .w (entryReg q) (if q = 0 ∨ q = 4 then 1 else 0) 0

/-- Words `2 j` and `2 j + 1` of the candidate at `x1`, kept if the condition is `eq`. -/
def selectPair (j : Nat) : List Instr :=
  [.ldp .x2 .x3 .x1 (16 * j), .cselc .x (entryReg (2 * j)) .x2 (entryReg (2 * j)) .eq,
    .cselc .x (entryReg (2 * j + 1)) .x3 (entryReg (2 * j + 1)) .eq]

/-- The next candidate: kept if the count in `x8` comes to 0 at it. -/
def selectEntry : List Instr :=
  ([.subImm .x .x8 .x8 1, .tst .x .x8 .x8] : List Instr) ++ (List.range 6).flatMap selectPair ++
    ([.addImm .x .x1 .x1 96] : List Instr)

/-- The entry of the magnitude in `x8` of the table at `x1`, which it moves on to the next table. -/
def select : List Instr := selectInit ++ (List.range 8).flatMap fun _ => selectEntry

/-- `p - 2dT` into `x2, x17, x20, x8`, with zero in `x10`. -/
def negT : List Instr :=
  [.subImm .x .x2 .x10 19, .subImm .x .x3 .x10 1, .lsr .x .x8 .x3 1,
    .subs .x .x2 .x2 .x21, .sbcs .x .x17 .x3 .x22, .sbcs .x .x20 .x3 .x23, .sbc .x .x8 .x8 .x24]

/-- The entry, negated for a negative digit: `Y - X` in `x16, x4, x5, x6`, `Y + X` in `x12`–`x15`,
`2dT` in `x21`–`x24`. -/
def negateRegs : List Instr :=
  ([.tst .x .x9 .x9] : List Instr) ++
    swapWord .x16 .x4 .x12 ++ swapWord .x4 .x5 .x13 ++ swapWord .x5 .x6 .x14 ++
    swapWord .x6 .x7 .x15 ++
    ([.cselc .x .x21 .x2 .x21 .ne, .cselc .x .x22 .x17 .x22 .ne, .cselc .x .x23 .x20 .x23 .ne,
      .cselc .x .x24 .x8 .x24 .ne] : List Instr)

/-- The entry into slots 4–6. -/
def entryStore : List Instr :=
  storePairs (offset 4) .x16 .x4 .x5 .x6 ++ storePairs (offset 5) .x12 .x13 .x14 .x15 ++
    storePairs (offset 6) .x21 .x22 .x23 .x24

/-- Digit `x19`'s entry of the table at `x1` into slots 4–6. -/
def entry : List Instr := digit ++ (select ++ (negT ++ (negateRegs ++ entryStore)))

/-! ## The addition -/

/-- `(Y - X) (Y₂ - X₂)` into slot 8. -/
def addA : List Instr :=
  loadPairs (offset 1) .x4 .x5 .x6 .x7 ++ loadPairs (offset 0) .x21 .x22 .x23 .x24 ++
    diff4 .x12 .x13 .x14 .x15 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x24 .x2 .x3 ++ mulInto 8 4

/-- `(Y + X) (Y₂ + X₂)` into slot 9. -/
def addB : List Instr :=
  loadPairs (offset 1) .x4 .x5 .x6 .x7 ++ loadPairs (offset 0) .x21 .x22 .x23 .x24 ++
    sum3 .x12 .x13 .x14 .x15 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x24 .x2 .x3 ++ mulInto 9 5

/-- `e = b - a` into slot 7 and `h = b + a` into slot 11, for `a` in slot 8 and `b` in slot 9. -/
def addEH : List Instr :=
  loadPairs (offset 9) .x4 .x5 .x6 .x7 ++ loadPairs (offset 8) .x21 .x22 .x23 .x24 ++
    diff4 .x12 .x13 .x14 .x15 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x24 .x2 .x3 ++
    storePairs (offset 7) .x12 .x13 .x14 .x15 ++
    sum3 .x4 .x5 .x6 .x7 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x24 .x2 .x3 ++
    storePairs (offset 11) .x4 .x5 .x6 .x7

/-- `g = 2 Z + c` into slot 13 and `f = 2 Z - c` into `x12`–`x15`, for `c` in slot 10. -/
def addFG : List Instr :=
  loadPairs (offset 2) .x4 .x5 .x6 .x7 ++
    sum3 .x4 .x5 .x6 .x7 .x4 .x5 .x6 .x7 .x4 .x5 .x6 .x7 .x2 .x3 ++
    loadPairs (offset 10) .x21 .x22 .x23 .x24 ++
    diff4 .x12 .x13 .x14 .x15 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x24 .x2 .x3 ++
    sum4 .x4 .x5 .x6 .x7 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x24 .x2 .x3 ++
    storePairs (offset 13) .x4 .x5 .x6 .x7

/-- The point in slots 0–3 plus the entry in slots 4–6, in place. -/
def addEntry : List (List Instr) := [
  addA, addB, mulSlots 10 3 6, addEH, addFG,
  mulInto 2 13, mulInto 0 7,
  mulSlots 1 13 11, mulInto 3 7]

/-! ## The loop -/

/-- Step `x19`; `x8` nonzero while another follows. -/
def combStep : List Instr :=
  entry ++ (addEntry.flatten ++ ([.addImm .x .x19 .x19 1, .subImm .x .x8 .x19 64] : List Instr))

/-- `(x, y)` of `[17 G]B`. -/
def combStartAff : Spec.X25519.Fe × Spec.X25519.Fe :=
  (4650268310714759443145295274883477433952106455267492499975084996511359585556,
    4189685876054382644851338298926788466640410231895644581786650308218358658796)

/-- `[17 G]B`, with `Z = 1`: where the accumulator starts. -/
def combStart : Spec.Ed25519.Point :=
  ⟨combStartAff.1, combStartAff.2, 1, combStartAff.1 * combStartAff.2⟩

/-- The accumulator at its start, the zero, the tables' address and the step. -/
def combInit : List Instr :=
  constPoint combStart ++ ([.movz .w .x10 0 0, .adrSym .x1 combSym, .movz .w .x19 0 0] : List Instr)

/-- `[s]B` into slots 0–3, from the scalar's nibbles. -/
def combMultiply : Prog isa := .seq (.block combInit) (.loop (.block combStep) (.nonzero .x .x8))

/-! ## The function -/

def scalarBaseSetup : List Instr := [.str .x .x0 .x2 48, mov .x0 .x2]

def scalarBaseEngine : Prog isa := .seq (.block scalarNibbles) (.seq combMultiply pointEncode)

def scalarBaseFinishArgs : List Instr := [mov .x2 .x0, .ldr .x .x0 .x0 48]

def scalarBaseFinish : Prog isa := .seq (.block scalarBaseFinishArgs) (.block scalarFinish)

/-- `(out, scalar, scratch) = (x0, x1, x2)`. -/
def scalarBase : Prog isa :=
  .seq (.block (scalarSave ++ scalarBaseSetup)) (.seq scalarBaseEngine scalarBaseFinish)

end VG.Impl.Ed25519.AArch64
