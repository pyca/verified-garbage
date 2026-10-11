import VerifiedGarbage.Spec.Blowfish
import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Impl.Blowfish.Table

/-!
# Blowfish on ARMv7

One block at a time in core registers. An S-box lookup reads every entry of
the S-box's four byte planes, a row of four entries of each plane (a word)
at a time: a mask is all ones in the byte lane of the index's entry if the
row holds it (`q - 4k < 4` for the index `q`), else zero, by a comparison
and `adc` (as RC4's lookups, `Impl/Rc4/Arm.lean`), and the masked words are
ORed into one accumulator, plane `b`'s rotated left by `8b`. Every address
and branch is a public counter or pointer; the index is only ever an operand
of the masks' arithmetic. The accumulator then holds byte `b` of the entry in
lane `L + b` (mod 4), for the index's lane `L`, and rotating it right by
`8L`, by two rotations selected by masks of `L`'s bits, gives the entry.

Registers: the schedule at `r0` (`sch`), the halves in `r1` (xL) and `r2`
(xR), F in `lr`; during a lookup, the index less four times the rows read
so far in `r4` (`q`), the accumulator in `r5`, the row's mask in `r6`, the
index's lane mask in `r7`, all ones in `r8`, a temporary in `r9`, the row
pointer in `r10` and the rows left in `r11`. `r12` points into the P-array.
`r3` holds the working space, where the functions keep our caller's
`r4`–`r11` and `lr` and their own pointer and counter.

`cipher` is the block function: the halves in `r1` and `r2`, the schedule
at `r0`, and the result in `r1` and `r2`, changing only `r4`–`r12`, `lr`
and the flags besides.

The pointer and counter go through the working space, at offsets of its
base `r3`, so that they stay public for the taint analysis that proves
constant time; it forgets them at a store of a secret through another
register (the data, the schedule's entries), so they are read before such
stores and written after.
-/

namespace VG.Impl.Blowfish.Arm

open VG.Arm

def sch : Reg := .r0
def xL : Reg := .r1
def xR : Reg := .r2
def fReg : Reg := .lr
def qReg : Reg := .r4
def acc : Reg := .r5
def mReg : Reg := .r6
def lane : Reg := .r7
def ones : Reg := .r8
def tmp : Reg := .r9
def rowPtr : Reg := .r10
def rows : Reg := .r11
def pPtr : Reg := .r12

/-- An immediate. -/
def imm (n : Nat) : Op2 := .imm (BitVec.ofNat 32 n)

/-- The offset of byte plane `b` of S-box `j` in the schedule. -/
def planeOff (j b : Nat) : Nat := 1024 * j + 256 * b

/-- The P-array's offset in the schedule. -/
def pOff : Nat := 4096

/-- `ones` := all ones. -/
def setOnes : List Instr := [.movw ones 0xFFFF, .movt ones 0xFFFF]

/-! ## Lookups -/

/-- `q` := the byte of xL that indexes S-box `j`: byte `3 - j`. -/
def index (j : Nat) : List Instr :=
  if j = 0 then [.mov qReg (.shifted xL .lsr 24)]
  else if j = 3 then [.dp .and qReg xL (imm 255)]
  else [.mov qReg (.shifted xL .lsl (8 * j)), .mov qReg (.shifted qReg .lsr 24)]

/-- `x` rotated right by `a` if bit `c` (1 or 2) of `q` is set: `m` is all
ones if it is clear, and `x := ((x XOR r) AND m) XOR r` for the rotation
`r`. -/
def condRot (x : Reg) (c a : Nat) : List Instr :=
  [.dp .and mReg qReg (imm c), .cmp mReg (imm 1), .adc mReg ones (imm 0),
   .mov tmp (.shifted x .ror a), .dp .eor x x (.reg tmp), .dp .and x x (.reg mReg),
   .dp .eor x x (.reg tmp)]

/-- The lane mask `0xFF <<< 8L` for the index's lane `L`, the accumulator,
the row pointer and the rows left. -/
def lookupStart : List Instr :=
  [.mov lane (imm 255)] ++ condRot lane 1 24 ++ condRot lane 2 16 ++
    [.mov acc (imm 0), .mov rowPtr (.reg sch), .mov rows (imm 64)]

/-- Plane `b`'s word of the row, masked, into the accumulator, rotated left
by `8b`. -/
def plane (j b : Nat) : List Instr :=
  [.ldr tmp rowPtr (planeOff j b), .dp .and tmp tmp (.reg mReg),
   .dp .orr acc acc (if b = 0 then .reg tmp else .shifted tmp .ror (32 - 8 * b))]

/-- One row of S-box `j`: the mask (all ones in the index's lane if
`q < 4`), the four planes, and the next row. -/
def row (j : Nat) : List Instr :=
  [.cmp qReg (imm 4), .adc mReg ones (imm 0), .dp .and mReg mReg (.reg lane),
   .dp .sub qReg qReg (imm 4)] ++
    plane j 0 ++ plane j 1 ++ plane j 2 ++ plane j 3 ++
    [.dp .add rowPtr rowPtr (imm 4), .subs rows rows (imm 1)]

/-- The accumulator rotated right by `8L`. -/
def lookupEnd : List Instr := condRot acc 1 8 ++ condRot acc 2 16

/-- S-box `j` of xL's byte `3 - j`, into the accumulator. -/
def lookup (j : Nat) : Prog isa :=
  .seq (.block (index j ++ lookupStart)) (.seq (.loop (.block (row j)) .ne) (.block lookupEnd))

/-- F's accumulation of S-box `j`: S₁, then + S₂, XOR S₃, + S₄. -/
def combine (j : Nat) : Instr :=
  if j = 0 then .mov fReg (.reg acc)
  else if j = 2 then .dp .eor fReg fReg (.reg acc)
  else .dp .add fReg fReg (.reg acc)

/-- F of xL into `fReg`. -/
def f : Prog isa :=
  .seq (lookup 0) (.seq (.block [combine 0]) (.seq (lookup 1) (.seq (.block [combine 1])
    (.seq (lookup 2) (.seq (.block [combine 2]) (.seq (lookup 3) (.block [combine 3])))))))

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

/-- The block function: all ones, the sixteen rounds, then the last swap
undone, xL (in `xR`) ^= P₁₈ and xR (in `xL`) ^= P₁₇ when encrypting, P₁ and
P₂ when decrypting, into `xL` and `xR`. -/
def cipher (up : Bool) : Prog isa :=
  .seq (.block (setOnes ++ [.dp .add pPtr sch (imm (if up then pOff else pOff + 64))]))
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

/-- Word `i` of the initial schedule's image, little-endian. -/
def initWord32 (i : Nat) : BitVec 32 :=
  (initWord (i / 2)).extractLsb' (32 * (i % 2)) 32

/-- Word `i` of the initial schedule, through `r9`, at `r11` (the S-boxes,
`i < 1024`) or `r12` (the P-array): both at `r2 + 0` and `r2 + 4096`, which
the taint analysis does not take for the schedule's base. -/
def initStore (i : Nat) : List Instr :=
  [.movw .r9 ((initWord32 i).extractLsb' 0 16), .movt .r9 ((initWord32 i).extractLsb' 16 16),
   if i < 1024 then .str .r9 .r11 (4 * i) else .str .r9 .r12 (4 * (i - 1024))]

def initSchedule : List Instr :=
  [.dp .add .r11 .r2 (imm 0), .dp .add .r12 .r2 (imm pOff)] ++ (List.range 1042).flatMap initStore

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
  .seq (.block (save ++ initSchedule))
    (.seq keyP
      (.seq (.block [.mov sch (.reg .r2), .mov xL (imm 0), .mov xR (imm 0)])
        (.seq encryptP (.seq encryptS (.block restore)))))

end VG.Impl.Blowfish.Arm
