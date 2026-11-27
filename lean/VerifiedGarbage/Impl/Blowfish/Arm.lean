module

public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Impl.Blowfish.Table
public import VerifiedGarbage.Impl.Scan.Arm

/-!
# Blowfish on ARMv7

One block at a time in core registers. An S-box lookup never uses the index
as an address: it reads the S-box's four byte planes whole, a word of four
entries of a plane at a time, as 32 rows of eight words, a row the words of
eight entries of each plane (`Impl/Scan/Arm.lean`: a one-hot word of the
row's number, the index's high five bits, a mask for each row from its bit,
and each word kept under it in the register of its column, `r4`–`r11`).
The index's next bit then chooses, for each plane, between the row's two
words of it, and its low two bits the word's byte, which a multiplication by
a power of two brings to the top (`extract`): the entry is the four planes'
bytes. Every address and branch is a public counter or pointer.

The rows use every register, so F keeps the schedule, the halves and the
pointer into the P-array in the working space (`fOff`), with its own state:
xL shifted so that the next index is its top byte, 1024 times the number of
lookups made, the count of a lookup's groups of rows, and F so far. F is a
loop of four lookups, each S-box's entry added to F so far, or XORed for
the third (a branch on the number of lookups).

Registers: the schedule at `r0` (`sch`), the halves in `r1` (xL) and `r2`
(xR), F in `lr`; `r12` points into the P-array, and `r3` holds the working
space, where the functions keep our caller's `r4`–`r11` and `lr` and their
own pointer and counter (during F, `r12` holds it).

`cipher` is the block function: the halves in `r1` and `r2`, the schedule
at `r0`, and the result in `r1` and `r2`, changing only `r4`–`r12`, `lr`,
the flags and F's words of the working space besides.

The pointer and counter go through the working space, at offsets of its
base `r3`, so that they stay public for the taint analysis that proves
constant time; it forgets them at a store of a secret through another
register (the data, the schedule's entries), so they are read before such
stores and written after.
-/

@[expose] public section

namespace VG.Impl.Blowfish.Arm

open VG.Arm VG.Impl.Scan.Arm

def sch : Reg := .r0
def xL : Reg := .r1
def xR : Reg := .r2
def fReg : Reg := .lr
def tmp : Reg := .r9
def pPtr : Reg := .r12

/-- An immediate. -/
def imm (n : Nat) : Op2 := .imm (BitVec.ofNat 32 n)

/-- The P-array's offset in the schedule. -/
def pOff : Nat := 4096

/-! ## F

F's eight words of the working space, from `fOff`: the schedule, xL, xR and
the pointer into the P-array, which it restores; xL shifted left by eight
bits for each lookup made (`fOff + 16`); 1024 times the number of lookups
made, the offset of the next S-box (`fOff + 20`); the groups of rows left
of a lookup (`fOff + 24`); and F so far (`fOff + 28`). -/

/-- Where F's words are in the working space. -/
def fOff : Nat := 48

/-- The offset from a group's pointer of column `c` of its row `r`: the word
of plane `c / 2` that holds entries `4 (2 r + c % 2)` and the next three. -/
def wordOff (r c : Nat) : Nat := 256 * (c / 2) + 8 * r + 4 * (c % 2)

/-- The schedule, the halves and the pointer into the P-array to their
words, xL to the indices' too; the working space in `r12`; no lookup made,
and F zero. -/
def fStart : List Instr :=
  [.str .r0 .r3 fOff, .str .r1 .r3 (fOff + 4), .str .r2 .r3 (fOff + 8), .str .r12 .r3 (fOff + 12),
   .str .r1 .r3 (fOff + 16), .mov .r12 (.reg .r3), .mov .r0 (imm 0), .str .r0 .r12 (fOff + 20),
   .str .r0 .r12 (fOff + 28)]

/-- The next index into `r0`, its row's one-hot word and the columns
cleared (`start`), and `lr` at the next S-box. -/
def lookStart : List Instr :=
  ([.ldr .r0 .r12 (fOff + 16), .mov .r0 (.shifted .r0 .lsr 24)] : List Instr) ++ start ++
    ([.ldr .lr .r12 fOff, .ldr .r0 .r12 (fOff + 20), .dp .add .lr .lr (.reg .r0)] : List Instr)

/-- The entry into `r0`, from the eight words of the index's row in the
columns: the index into `r2`; for each plane, the word that the index's bit
2 chooses of its two, into `r4`, `r6`, `r8` and `r10` (the columns `r6`,
`r7`, `r10` and `r11` hold their words' negations, and take the selectors'
negations); `2 ^ (24 - 8 L)` into `r1`, for the index's low two bits `L`;
and the top byte of each plane's word times that. -/
def extract : List Instr :=
  [.ldr .r2 .r12 (fOff + 16), .mov .r2 (.shifted .r2 .lsr 24),
   .dp .bic .r0 .r3 (.shifted .r2 .lsr 2), .dp .and .r1 .r3 (.shifted .r2 .lsr 2),
   .mul .r4 .r4 .r0, .mla .r4 .r5 .r1 .r4, .mul .r8 .r8 .r0, .mla .r8 .r9 .r1 .r8,
   .dp .sub .r5 .r1 (imm 1), .dp .sub .r9 .r0 (imm 1),
   .mul .r6 .r6 .r5, .mla .r6 .r7 .r9 .r6, .mul .r10 .r10 .r5, .mla .r10 .r11 .r9 .r10,
   .dp .bic .r0 .r3 (.reg .r2), .dp .add .r1 .r3 (.shifted .r0 .lsl 8), .dp .sub .r1 .r1 (.reg .r0),
   .dp .bic .r0 .r3 (.shifted .r2 .lsr 1), .dp .add .lr .r3 (.shifted .r0 .lsl 16), .dp .sub .lr .lr (.reg .r0),
   .mul .r1 .r1 .lr,
   .mul .r0 .r4 .r1, .mov .r0 (.shifted .r0 .lsr 24),
   .mul .r5 .r6 .r1, .mov .r5 (.shifted .r5 .lsr 24), .dp .orr .r0 .r0 (.shifted .r5 .lsl 8),
   .mul .r5 .r8 .r1, .mov .r5 (.shifted .r5 .lsr 24), .dp .orr .r0 .r0 (.shifted .r5 .lsl 16),
   .mul .r5 .r10 .r1, .mov .r5 (.shifted .r5 .lsr 24), .dp .orr .r0 .r0 (.shifted .r5 .lsl 24)]

/-- The indices left; F so far into `r1`, and whether this is the third lookup. -/
def combineHead : List Instr :=
  [.ldr .r2 .r12 (fOff + 16), .mov .r2 (.shifted .r2 .lsl 8), .str .r2 .r12 (fOff + 16),
   .ldr .r1 .r12 (fOff + 28), .ldr .r2 .r12 (fOff + 20), .cmp .r2 (imm 2048)]

/-- F so far to its word, and the next S-box's offset (Z set after the fourth). -/
def combineTail : List Instr :=
  [.str .r1 .r12 (fOff + 28), .dp .add .r2 .r2 (imm 1024), .str .r2 .r12 (fOff + 20), .cmp .r2 (imm 4096)]

/-- A lookup: the next S-box's entry at xL's next byte, into F so far: S₁,
then + S₂, XOR S₃, + S₄. -/
def look : Prog isa :=
  .seq (.block lookStart) (.seq (rows wordOff 64 (fOff + 24))
    (.seq (.block (extract ++ combineHead))
      (.seq (.ite .eq (.block [.dp .eor .r1 .r1 (.reg .r0)]) (.block [.dp .add .r1 .r1 (.reg .r0)]))
        (.block combineTail))))

/-- F into `lr`, and the schedule, the halves, the working space and the
pointer into the P-array back. -/
def fEnd : List Instr :=
  [.ldr .lr .r12 (fOff + 28), .ldr .r0 .r12 fOff, .ldr .r1 .r12 (fOff + 4), .ldr .r2 .r12 (fOff + 8),
   .mov .r3 (.reg .r12), .ldr .r12 .r3 (fOff + 12)]

/-- F of xL into `fReg`. Clobbers `r4`–`r11` and F's words of the working
space at `r3`. -/
def f : Prog isa := .seq (.block fStart) (.seq (.loop look .ne) (.block fEnd))

/-! ## Rounds

`pPtr` is at the P-array entry of the round (`up`, encrypting), or four
bytes below it (decrypting): at `sch + 4096 + 4i`, or at
`sch + 4096 + 64 - 4i`, for round `i`. -/

/-- The offset from `pPtr` of the round's entry. -/
def pAt (up : Bool) : Nat := if up then 0 else 4

/-- `xL ^= P`, `xR ^= F(xL)`, the halves swapped, and `pPtr` to the next
entry; the flags say whether it is the end. -/
def round (up : Bool) : Prog isa :=
  .seq (.block [.ldr tmp pPtr (pAt up), .dp .eor xL xL (.reg tmp)])
    (.seq f
      (.block [.dp .eor xR xR (.reg fReg), .mov tmp (.reg xL), .mov xL (.reg xR), .mov xR (.reg tmp),
        .dp (if up then .add else .sub) pPtr pPtr (imm 4), .dp .sub tmp pPtr (.reg sch),
        .cmp tmp (imm (if up then pOff + 64 else pOff))]))

/-- The block function: the sixteen rounds, then the last swap
undone, xL (in `xR`) ^= P₁₈ and xR (in `xL`) ^= P₁₇ when encrypting, P₁ and
P₂ when decrypting, into `xL` and `xR`. -/
def cipher (up : Bool) : Prog isa :=
  .seq (.block [.dp .add pPtr sch (imm (if up then pOff else pOff + 64))])
    (.seq (.loop (round up) .ne)
      (.block [.ldr tmp pPtr (pAt up), .dp .eor tmp xL (.reg tmp),
        .ldr xL pPtr (4 - pAt up), .dp .eor xL xL (.reg xR), .mov xR (.reg tmp)]))

/-! ## Our caller's registers, in the working space at `r3` -/

def saved : List (Reg × Nat) :=
  [(.r4, 0), (.r5, 4), (.r6, 8), (.r7, 12), (.r8, 16), (.r9, 20), (.r10, 24), (.r11, 28),
   (.lr, 32)]

/-- Save them, through `r3`, the working space. -/
def save : List Instr := saved.map fun p => .str p.1 .r3 p.2

/-- Restore them, through `r3`. -/
def restore : List Instr := saved.map fun p => .ldr p.1 .r3 p.2

/-- The working space's pointer (`ptrOff`) and counter (`cntOff`). -/
def ptrOff : Nat := 36
def cntOff : Nat := 40

/-- The counter (read into `r11` earlier) less one, written back; the flags
say whether it is zero. -/
def countDown : List Instr := [.subs .r11 .r11 (imm 1), .str .r11 .r3 cntOff]

/-! ## ECB

`vg_blowfish_ecb_{en,de}crypt(schedule = r0, data = r1, n = r2, scratch = r3)`:
the data pointer and the blocks left are kept in the working space. -/

/-- The block at the data pointer into the halves, as big-endian words. -/
def loadBlock : List Instr :=
  [.ldr pPtr .r3 ptrOff, .ldr xL pPtr 0, .rev xL xL, .ldr xR pPtr 4, .rev xR xR]

/-- The halves to the block, and the next block. -/
def storeBlock : List Instr :=
  [.ldr pPtr .r3 ptrOff, .ldr .r11 .r3 cntOff, .rev xL xL, .str xL pPtr 0, .rev xR xR, .str xR pPtr 4,
   .dp .add pPtr pPtr (imm 8), .str pPtr .r3 ptrOff] ++ countDown

def ecb (up : Bool) : Prog isa :=
  .seq (.block (save ++ [.str .r1 .r3 ptrOff, .str .r2 .r3 cntOff, .cmp .r2 (imm 0)]))
    (.seq (.ite .eq (.block [])
        (.loop (.seq (.block loadBlock) (.seq (cipher up) (.block storeBlock))) .ne))
      (.block restore))

def encrypt : Prog isa := ecb true
def decrypt : Prog isa := ecb false

/-! ## Key expansion

`vg_blowfish_expand_key(key = r0, key_len = r1, schedule = r2, scratch = r3)`. -/

/-- The name of the static holding the initial schedule (`Impl.Blowfish.initWords`). -/
def initSym : String := "VG_BLOWFISH_INIT"

def initConsts : List (String × List (BitVec 64)) := [(initSym, Impl.Blowfish.initWords)]

/-- The registers a step of the copy holds its words in. -/
def copyRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r10, .lr]

def copyReg (i : Nat) : Reg := copyRegs.getD i .r4

/-- `k` words (`k ≤ 7`) from the table at `r9` to the schedule at `r11`: the
loads, then the stores. -/
def copyWords (k : Nat) : List Instr :=
  (List.range k).map (fun i => .ldr (copyReg i) .r9 (4 * i)) ++
    (List.range k).map (fun i => .str (copyReg i) .r11 (4 * i))

/-- Seven words, the pointers past them, and the steps left in `r12`. -/
def copyStep : List Instr :=
  copyWords 7 ++ [.dp .add .r9 .r9 (imm 28), .dp .add .r11 .r11 (imm 28), .subs .r12 .r12 (imm 1)]

/-- The initial schedule, 1042 words, copied from the static `initSym`: 148
steps of seven words, then six. The schedule is written through `r11`, at
`r2 + 0`, which the taint analysis does not take for the schedule's base. -/
def initSchedule : Prog isa :=
  .seq (.block [.adrSym .r9 initSym, .dp .add .r11 .r2 (imm 0), .mov .r12 (imm 148)])
    (.seq (.loop (.block copyStep) .ne) (.block (copyWords 6)))

/-- The next key byte into the low byte of `r5` (shifted up), cycling: the
byte at `r0 + r4`, then `r4 := r4 + 1`, or 0 at `key_len` (`r1`). -/
def keyByte : Prog isa :=
  .seq (.block [.dp .add .r7 .r0 (.reg .r4), .ldrb .r6 .r7 0, .mov .r5 (.shifted .r5 .lsl 8),
      .dp .orr .r5 .r5 (.reg .r6), .dp .add .r4 .r4 (imm 1), .cmp .r4 (.reg .r1)])
    (.ite .eq (.block [.mov .r4 (imm 0)]) (.block []))

/-- The P-array entry at `r12` XORed with the next 32 bits of the key; the
next entry, and the entries left in `r8`. -/
def keyWord : Prog isa :=
  .seq (.block [.mov .r5 (imm 0)])
    (.seq keyByte (.seq keyByte (.seq keyByte (.seq keyByte
      (.block [.ldr .r6 .r12 0, .dp .eor .r6 .r6 (.reg .r5), .str .r6 .r12 0,
        .dp .add .r12 .r12 (imm 4), .subs .r8 .r8 (imm 1)])))))

/-- Pᵢ ^= the next 32 bits of the key, for the 18 entries. -/
def keyP : Prog isa :=
  .seq (.block [.mov .r4 (imm 0), .dp .add .r12 .r2 (imm pOff), .mov .r8 (imm 18)])
    (.loop keyWord .ne)

/-- The output's two words into the P-array entries at the pointer, and the
next pair. -/
def storeP : List Instr :=
  [.ldr pPtr .r3 ptrOff, .ldr .r11 .r3 cntOff, .str xL pPtr 0, .str xR pPtr 4,
   .dp .add pPtr pPtr (imm 8), .str pPtr .r3 ptrOff] ++ countDown

/-- The first nine encryptions replace the P-array, a pair of entries each. -/
def encryptP : Prog isa :=
  .seq (.block [.dp .add pPtr sch (imm pOff), .str pPtr .r3 ptrOff, .mov .r11 (imm 9),
      .str .r11 .r3 cntOff])
    (.loop (.seq (cipher true) (.block storeP)) .ne)

/-- The bytes of the word in `x` into the planes of the S-box entry at
`pPtr + e`. -/
def storeEntry (x : Reg) (e : Nat) : List Instr :=
  [.strb x pPtr e, .mov tmp (.shifted x .lsr 8), .strb tmp pPtr (256 + e),
   .mov tmp (.shifted x .lsr 16), .strb tmp pPtr (512 + e),
   .mov tmp (.shifted x .lsr 24), .strb tmp pPtr (768 + e)]

/-- The output's two words into the S-box entries at the pointer, and the
next pair: past the other planes after an S-box's last entry. -/
def storeS : Prog isa :=
  .seq (.block ([.ldr pPtr .r3 ptrOff, .ldr .r11 .r3 cntOff] ++ storeEntry xL 0 ++ storeEntry xR 1 ++
      [.dp .add pPtr pPtr (imm 2), .dp .sub tmp pPtr (.reg sch), .dp .and tmp tmp (imm 255),
       .cmp tmp (imm 0)]))
    (.seq (.ite .eq (.block [.dp .add pPtr pPtr (imm 768)]) (.block []))
      (.block ([.str pPtr .r3 ptrOff] ++ countDown)))

/-- The other 512 replace the S-boxes. -/
def encryptS : Prog isa :=
  .seq (.block [.str sch .r3 ptrOff, .movw .r11 512, .str .r11 .r3 cntOff])
    (.loop (.seq (cipher true) storeS) .ne)

def expandKey : Prog isa :=
  .seq (.block save) (.seq initSchedule
    (.seq keyP
      (.seq (.block [.mov sch (.reg .r2), .mov xL (imm 0), .mov xR (imm 0)])
        (.seq encryptP (.seq encryptS (.block restore))))))

end VG.Impl.Blowfish.Arm
