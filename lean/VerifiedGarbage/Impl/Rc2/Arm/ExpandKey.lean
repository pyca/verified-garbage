module

public import VerifiedGarbage.Impl.Rc2.Arm.Lookup
public import VerifiedGarbage.Impl.Rc2.Table

/-! # RC2 key expansion on ARMv7

Public lengths control the loops. `lr` holds public addresses; all
callee-saved registers are saved in the scratch buffer supplied on the stack.

Each PITABLE lookup visits the whole static `VG_RC2_PITABLE`
(`Impl/Rc2/Table.lean`), its 64 words of four entries each, as 32 rows of
two words, at addresses that depend on nothing. Each row has a bit that is
1 exactly when the (secret) index is one of its eight entries; each of its
two words times that bit is added to the register of its column (`mla`),
and then the index's word of the two, and its byte of that word, are chosen
with multiplications by bits of the index. The lookups never branch on key
bytes or use them as addresses or shift amounts.
-/

@[expose] public section

namespace VG.Impl.Rc2.Arm

open VG.Arm

def saved : List Reg := [.r8, .r4, .r5, .r6, .r7, .r9, .r10, .r11, .lr]

def save (base : Reg) (offset : Nat) : List Instr :=
  saved.zipIdx |>.map fun (r, i) => .str r base (offset + 4 * i)

def restore (base : Reg) (offset : Nat) : List Instr :=
  saved.zipIdx |>.map fun (r, i) => .ldr r base (offset + 4 * i)

/-- Row `r` of PITABLE, its entries `8 r … 8 r + 7`: `r3` is 1 iff the index
in `r12` (below 256) is one of them (`(r12 ^ 8 r) - 8` is negative exactly
then), and each of the row's two words, at `lr + 8 r` and `lr + 8 r + 4`,
times that bit, is added to its column's register, `r9` and `r10`. -/
def piRow (r : Nat) : List Instr :=
  [.dp .eor .r3 .r12 (.imm (BitVec.ofNat 32 (8 * r))), .dp .sub .r3 .r3 (.imm 8),
   .mov .r3 (.shifted .r3 .lsr 31),
   .ldr .r11 .lr (8 * r), .mla .r9 .r11 .r3 .r9, .ldr .r11 .lr (8 * r + 4), .mla .r10 .r11 .r3 .r10]

/-- The index's word of the two of its row, by bit 2 of the index, then
byte `r12 & 3` of that word, shifted right by 8 if bit 0 is set and by 16 if
bit 1 is, into `r12`: each choice between `a` and `b` by a bit is
`(b - a) * bit + a`. -/
def piSelect : List Instr :=
  [.mov .r3 (.shifted .r12 .lsl 29), .mov .r3 (.shifted .r3 .lsr 31),
   .dp .sub .r10 .r10 (.reg .r9), .mla .r9 .r10 .r3 .r9,
   .dp .and .r3 .r12 (.imm 1), .mov .r10 (.shifted .r9 .lsr 8),
   .dp .sub .r10 .r10 (.reg .r9), .mla .r9 .r10 .r3 .r9,
   .mov .r3 (.shifted .r12 .lsl 30), .mov .r3 (.shifted .r3 .lsr 31), .mov .r10 (.shifted .r9 .lsr 16),
   .dp .sub .r10 .r10 (.reg .r9), .mla .r9 .r10 .r3 .r9,
   .dp .and .r12 .r9 (.imm 255)]

/-- `r12 := PITABLE[r12 & 255]`, by a visit of the whole table, the table's
address in `lr`, then a choice of the byte among the eight of the index's
row. Clobbers `r3`, `r9`–`r11` and `lr`. -/
def piLookup : Prog isa :=
  .block (mask .r12 8 ++ ([.adrSym .lr piSym, imm .r9 0, imm .r10 0] : List Instr) ++
    (List.range 32).flatMap piRow ++ piSelect)

def copyKey : List Instr :=
  [.dp .add .lr .r4 (.reg .r0), .ldrb .r12 .lr 0,
   .dp .add .lr .r6 (.reg .r0), .strb .r12 .lr 0,
   .dp .add .r0 .r0 (.imm 1), .cmp .r0 (.reg .r5)]

def fillInput : List Instr :=
  [.dp .add .lr .r6 (.reg .r0), .dp .sub .lr .lr (.imm 1), .ldrb .r12 .lr 0,
   .dp .sub .r9 .r0 (.reg .r5), .dp .add .lr .r6 (.reg .r9), .ldrb .r3 .lr 0,
   .dp .add .r12 .r12 (.reg .r3)]

def storeKey : List Instr := [.dp .add .lr .r6 (.reg .r0), .strb .r12 .lr 0]

def fillFinish : List Instr :=
  storeKey ++ ([.dp .add .r0 .r0 (.imm 1), .cmp .r0 (.imm 128)] : List Instr)

def fillKey : Prog isa := .seq (.block fillInput) (.seq piLookup (.block fillFinish))

def maskCode : Prog isa :=
  .seq (.block ([rr .r9 .r7] ++ mask .r9 3 ++ [imm .r2 255]))
    ((List.range 7).foldr (fun i rest =>
      .seq (.block [.cmp .r9 (.imm (BitVec.ofNat 32 (i + 1)))])
        (.seq (.ite .eq (.block [imm .r2 (2 ^ (i + 1) - 1)]) (.block [])) rest)) (.block []))

def reduceInput : List Instr :=
  [.dp .add .lr .r6 (.reg .r0), .ldrb .r12 .lr 0, .dp .and .r12 .r12 (.reg .r2)]

def reduceKey : Prog isa := .seq (.block reduceInput) (.seq piLookup (.block storeKey))

def descendInput : List Instr :=
  [.dp .sub .r0 .r0 (.imm 1), .dp .add .lr .r6 (.reg .r0), .dp .add .lr .lr (.imm 1),
   .ldrb .r12 .lr 0, .dp .add .r9 .r0 (.reg .r1),
   .dp .add .lr .r6 (.reg .r9), .ldrb .r3 .lr 0, .dp .eor .r12 .r12 (.reg .r3)]

def descendKey : Prog isa :=
  .seq (.block descendInput) (.seq piLookup (.block (storeKey ++ ([.cmp .r0 (.imm 0)] : List Instr))))

def expandCopyFill : Prog isa :=
  .seq (.loop (.block copyKey) .ne)
    (.seq (.block [.cmp .r0 (.imm 128)])
      (.ite .ne (.loop fillKey .ne) (.block [])))

def reduceSetup : List Instr :=
  [.dp .add .r1 .r7 (.imm 7), .mov .r1 (.shifted .r1 .lsr 3), imm .r0 128,
   .dp .sub .r0 .r0 (.reg .r1)]

def expandReduce : Prog isa :=
  .seq (.block reduceSetup)
    (.seq maskCode
      (.seq reduceKey
        (.seq (.block [.cmp .r0 (.imm 0)])
          (.ite .ne (.loop descendKey .ne) (.block [])))))

def expandKey : Prog isa :=
  .seq (.block [.ldrSp .r12 0])
    (.seq (.block (save .r12 0 ++
        [rr .r8 .r12, rr .r4 .r0, rr .r5 .r1, rr .r6 .r3, rr .r7 .r2, imm .r0 0]))
      (.seq expandCopyFill (.seq expandReduce (.block ([rr .r12 .r8] ++ restore .r12 0)))))

end VG.Impl.Rc2.Arm
