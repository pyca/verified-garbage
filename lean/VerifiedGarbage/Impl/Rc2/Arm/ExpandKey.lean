module

public import VerifiedGarbage.Impl.Rc2.Arm.Lookup
public import VerifiedGarbage.Impl.Rc2.Table

/-! # RC2 key expansion on ARMv7

Public lengths control the loops. `lr` holds public addresses; all
callee-saved registers are saved in the scratch buffer supplied on the stack.

Each PITABLE lookup scans the whole static `VG_RC2_PITABLE`
(`Impl/Rc2/Table.lean`): a loop over its 256 bytes in order, a word of four
entries at a time, at addresses that depend only on the entries' numbers,
keeping the word under a mask that is all ones exactly when the (secret)
index is one of its entries, then selects the index's byte of that word with
masks. The scans never branch on key bytes or use them as addresses or shift
amounts.
-/

@[expose] public section

namespace VG.Impl.Rc2.Arm

open VG.Arm

def saved : List Reg := [.r8, .r4, .r5, .r6, .r7, .r9, .r10, .r11, .lr]

def save (base : Reg) (offset : Nat) : List Instr :=
  saved.zipIdx |>.map fun (r, i) => .str r base (offset + 4 * i)

def restore (base : Reg) (offset : Nat) : List Instr :=
  saved.zipIdx |>.map fun (r, i) => .ldr r base (offset + 4 * i)

/-- Four entries of the scan of PITABLE: their word, at `lr`, is kept iff
the index in `r12` is in the entries `r9 … r9 + 3` (both below 256 and `r9`
a multiple of 4, so `(r12 ^ r9) - 4` is negative exactly then, and the mask
`((r12 ^ r9) - 4) >> 8`, widened by `orr` with itself shifted left by 8, is
all ones exactly then, and 0 otherwise), ORed into `r3`; then on to the next
four (Z set after the last, 252). -/
def piBody : List Instr :=
  [.ldr .r10 .lr 0, .dp .eor .r11 .r12 (.reg .r9), .dp .sub .r11 .r11 (.imm 4),
   .mov .r11 (.shifted .r11 .lsr 8), .dp .orr .r11 .r11 (.shifted .r11 .lsl 8),
   .dp .and .r10 .r10 (.reg .r11), .dp .orr .r3 .r3 (.reg .r10),
   .dp .add .lr .lr (.imm 4), .cmp .r9 (.imm 252), .dp .add .r9 .r9 (.imm 4)]

/-- Byte `r12 & 3` of the word in `r3`, into `r12`: for each `k < 4`, byte
`k` (`r3 >> 8k`) under a mask that is `0x00ffffff` exactly when `r12 & 3` (in
`lr`) is `k` (`((lr ^ k) - 1) >> 8`), ORed together, then the low byte. -/
def piSelect : List Instr :=
  [.dp .and .lr .r12 (.imm 3),
   .dp .sub .r10 .lr (.imm 1), .mov .r10 (.shifted .r10 .lsr 8), .dp .and .r12 .r10 (.reg .r3),
   .dp .eor .r10 .lr (.imm 1), .dp .sub .r10 .r10 (.imm 1), .mov .r10 (.shifted .r10 .lsr 8),
   .dp .and .r10 .r10 (.shifted .r3 .lsr 8), .dp .orr .r12 .r12 (.reg .r10),
   .dp .eor .r10 .lr (.imm 2), .dp .sub .r10 .r10 (.imm 1), .mov .r10 (.shifted .r10 .lsr 8),
   .dp .and .r10 .r10 (.shifted .r3 .lsr 16), .dp .orr .r12 .r12 (.reg .r10),
   .dp .eor .r10 .lr (.imm 3), .dp .sub .r10 .r10 (.imm 1), .mov .r10 (.shifted .r10 .lsr 8),
   .dp .and .r10 .r10 (.shifted .r3 .lsr 24), .dp .orr .r12 .r12 (.reg .r10),
   .dp .and .r12 .r12 (.imm 255)]

/-- `r12 := PITABLE[r12 & 255]`, by a scan of the whole table, four entries
(one word) at a time, the first entry's number in `r9` and its address in
`lr`, then a selection of the byte among the four. Clobbers `r3`, `r9`–`r11`
and `lr`. -/
def piLookup : Prog isa :=
  .seq (.block (mask .r12 8 ++ ([imm .r3 0, .adrSym .lr piSym, .mov .r9 (.imm 0)] : List Instr)))
    (.seq (.loop (.block piBody) .ne) (.block piSelect))

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
