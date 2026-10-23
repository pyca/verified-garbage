module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Impl.Blowfish.Table

/-!
# Blowfish on PPC64LE

One block at a time in general-purpose registers, as on ARMv7
(`Impl/Blowfish/Arm.lean`), whose 32-bit scan this follows: an S-box lookup
reads every entry of the S-box's four byte planes, a row of four entries of
each plane (a word, `lwz`) at a time. A row's mask is all ones in the byte
lane of the index's entry if the row holds it (`q - 4k < 4` for the index
`q`, as unsigned doublewords, so `(q - 4k) >> 2` is zero), else zero, made
without a comparison as RC4's are (`Impl/Rc4/PPC64LE.lean`): `0 - (((v - 1)
>> 63)` is all ones exactly when `v < 2 ^ 63` is zero. The masked words are
ORed into one accumulator, plane `b`'s rotated left by `8b` (`rotrwi`).
Every address and branch is a public counter or pointer; the index is only
ever an operand of the masks' arithmetic. The accumulator then holds byte
`b` of the entry in lane `L + b` (mod 4), for the index's lane `L`, and
rotating it right by `8L`, by two rotations selected by masks of `L`'s bits,
gives the entry.

The halves, F and the accumulator are 32-bit values in the low words of
their registers; their high words are whatever the arithmetic leaves, which
nothing reads: word rotations and shifts read the low word, `stw` stores it,
and the index is taken from it.

Registers: zero in `r0`, the schedule at `r3` (`sch`), the halves in `r4`
(xL) and `r5` (xR), F in `r7`, the P-array pointer in `r8`; during a lookup,
the index less four times the rows read so far in `r9` (`q`), the
accumulator in `r10`, the row's mask in `r11`, a temporary in `r12`, the
index's lane mask in `r14` and the row pointer in `r15`. ECB keeps the data
pointer in `r16` and the blocks left in `r17`; key expansion, the pointer to
the next entries in `r16` and the encryptions left in `r17`. The caller's
`r14`–`r17` are kept in the working space, at `r6`.
-/

@[expose] public section

namespace VG.Impl.Blowfish.PPC64LE

open VG.PPC64LE

def zero : Reg := .r0
def sch : Reg := .r3
def xL : Reg := .r4
def xR : Reg := .r5
def fReg : Reg := .r7
def pPtr : Reg := .r8
def qReg : Reg := .r9
def acc : Reg := .r10
def mReg : Reg := .r11
def tmp : Reg := .r12
def lane : Reg := .r14
def rowPtr : Reg := .r15
def ptr : Reg := .r16
def cnt : Reg := .r17

/-- The offset of byte plane `b` of S-box `j` in the schedule. -/
def planeOff (j b : Nat) : Nat := 1024 * j + 256 * b

/-- The P-array's offset in the schedule. -/
def pOff : Nat := 4096

/-! ## Lookups -/

/-- `q` := the byte of xL that indexes S-box `j`: byte `3 - j`, shifted to
the top of the doubleword and back. -/
def index (j : Nat) : List Instr := [.lsl qReg xL (32 + 8 * j), .lsr .d qReg qReg 56]

/-- `mReg` := all ones if bit `c` of `q` is set, else zero. -/
def bitMask (c : Nat) : List Instr := [.lsl mReg qReg (63 - c), .lsr .d mReg mReg 63, .sub mReg zero mReg]

/-- `x` rotated right by `a` (as a word) if bit `c` of `q` is set:
`x := x XOR ((rotr x a XOR x) AND m)`. -/
def condRot (x : Reg) (c a : Nat) : List Instr :=
  bitMask c ++ ([.rotr .w tmp x a, .logic .xor tmp tmp x, .logic .and tmp tmp mReg,
    .logic .xor x x tmp] : List Instr)

/-- The lane mask `0xFF <<< 8L` for the index's lane `L`, the accumulator
and the row pointer. -/
def lookupStart : List Instr :=
  [.li lane 255] ++ condRot lane 0 24 ++ condRot lane 1 16 ++
    [.li acc 0, .logic .or rowPtr sch sch]

/-- Plane `b`'s word of the row, masked, into the accumulator, rotated left
by `8b`. -/
def plane (j b : Nat) : List Instr :=
  if b = 0 then [.load .w tmp rowPtr (planeOff j b), .logic .and tmp tmp mReg, .logic .or acc acc tmp]
  else [.load .w tmp rowPtr (planeOff j b), .logic .and tmp tmp mReg, .rotr .w tmp tmp (32 - 8 * b),
    .logic .or acc acc tmp]

/-- The row's mask: all ones in the index's lane if `q >> 2` is zero. -/
def rowMask : List Instr :=
  [.lsr .d mReg qReg 2, .subi mReg mReg 1, .lsr .d mReg mReg 63, .sub mReg zero mReg,
   .logic .and mReg mReg lane, .subi qReg qReg 4]

/-- One row of S-box `j`: the mask, the four planes, and the next row;
`tmp` is zero after the last. -/
def row (j : Nat) : List Instr :=
  rowMask ++ plane j 0 ++ plane j 1 ++ plane j 2 ++ plane j 3 ++
    [.addi rowPtr rowPtr 4, .sub tmp rowPtr sch, .subi tmp tmp 256]

/-- The accumulator rotated right by `8L`. -/
def lookupEnd : List Instr := condRot acc 0 8 ++ condRot acc 1 16

/-- S-box `j` of xL's byte `3 - j`, into the accumulator's low word. -/
def lookup (j : Nat) : Prog isa :=
  .seq (.block (index j ++ lookupStart))
    (.seq (.loop (.block (row j)) (.nonzero .d tmp)) (.block lookupEnd))

/-- F's accumulation of S-box `j`: S₁, then + S₂, XOR S₃, + S₄. -/
def combine (j : Nat) : Instr :=
  if j = 0 then .logic .or fReg acc acc
  else if j = 2 then .logic .xor fReg fReg acc
  else .add fReg fReg acc

/-- F of xL into `fReg`'s low word. -/
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
entry; `tmp` is zero at the end. -/
def round (up : Bool) : Prog isa :=
  .seq (.block [.load .w tmp pPtr (pAt up), .logic .xor xL xL tmp])
    (.seq f
      (.block [.logic .xor xR xR fReg, .logic .or tmp xL xL, .logic .or xL xR xR,
        .logic .or xR tmp tmp, if up then .addi pPtr pPtr 4 else .subi pPtr pPtr 4,
        .sub tmp pPtr sch, .subi tmp tmp (if up then pOff + 64 else pOff)]))

/-- The block function: the sixteen rounds, then the last swap undone, xL
(in `xR`) ^= P₁₈ and xR (in `xL`) ^= P₁₇ when encrypting, P₁ and P₂ when
decrypting, into `xL` and `xR`. -/
def cipher (up : Bool) : Prog isa :=
  .seq (.block [.addi pPtr sch (if up then pOff else pOff + 64)])
    (.seq (.loop (round up) (.nonzero .d tmp))
      (.block [.load .w tmp pPtr (pAt up), .logic .xor tmp xL tmp,
        .load .w xL pPtr (4 - pAt up), .logic .xor xL xL xR, .logic .or xR tmp tmp]))

/-! ## Our caller's registers, in the working space at `r6` -/

def saved : List (Reg × Nat) := [(.r14, 0), (.r15, 8), (.r16, 16), (.r17, 24)]

/-- Save them, through `r6`, the working space. -/
def save : List Instr := saved.map fun p => .store .d p.1 .r6 p.2

/-- Restore them, through `r6`. -/
def restore : List Instr := saved.map fun p => .load .d p.1 .r6 p.2

/-! ## ECB

`vg_blowfish_ecb_{en,de}crypt(schedule = r3, data = r4, n = r5,
scratch = r6)`. -/

/-- The block at the data pointer into the halves, as big-endian words. -/
def loadBlock : List Instr :=
  [.loadRev .w xL ptr zero, .addi tmp ptr 4, .loadRev .w xR tmp zero]

/-- The halves to the block, and the next block. -/
def storeBlock : List Instr :=
  [.storeRev .w xL ptr zero, .addi tmp ptr 4, .storeRev .w xR tmp zero, .addi ptr ptr 8,
   .subi cnt cnt 1]

def ecb (up : Bool) : Prog isa :=
  .seq (.block (save ++ [.li zero 0, .logic .or ptr .r4 .r4, .logic .or cnt .r5 .r5]))
    (.seq (.ite (.zero .d cnt) (.block [])
        (.loop (.seq (.block loadBlock) (.seq (cipher up) (.block storeBlock))) (.nonzero .d cnt)))
      (.block restore))

def encrypt : Prog isa := ecb true
def decrypt : Prog isa := ecb false

/-! ## Key expansion

`vg_blowfish_expand_key(key = r3, key_len = r4, schedule = r5,
scratch = r6)`. -/

/-- `d := v` for a 64-bit constant: the high word with `lis` and `ori`,
shifted up by `sldi`, then the low word with `oris` and `ori`. -/
def movImm64 (d : Reg) (v : BitVec 64) : List Instr :=
  [.lis d (v.extractLsb' 48 16), .ori d d (v.extractLsb' 32 16), .lsl d d 32,
   .oris d d (v.extractLsb' 16 16), .ori d d (v.extractLsb' 0 16)]

/-- The initial schedule (`Impl.Blowfish.initWords`), a doubleword at a
time, as immediates. -/
def initSchedule : List Instr :=
  (List.range 521).flatMap fun i => movImm64 tmp (Impl.Blowfish.initWord i) ++ [.store .d tmp .r5 (8 * i)]

/-- The next key byte into the low byte of `r10` (shifted up), cycling: the
byte at `r3 + r9`, then `r9 := r9 + 1`, or 0 at `key_len` (`r4`). -/
def keyByte : Prog isa :=
  .seq (.block [.add tmp .r3 .r9, .lbz .r11 tmp 0, .lsl .r10 .r10 8, .logic .or .r10 .r10 .r11,
      .addi .r9 .r9 1, .sub tmp .r9 .r4])
    (.ite (.zero .d tmp) (.block [.li .r9 0]) (.block []))

/-- The P-array entry at `r8` XORed with the next 32 bits of the key; the
next entry, and the entries left in `r17`. -/
def keyWord : Prog isa :=
  .seq (.block [.li .r10 0])
    (.seq keyByte (.seq keyByte (.seq keyByte (.seq keyByte
      (.block [.load .w .r11 .r8 0, .logic .xor .r11 .r11 .r10, .store .w .r11 .r8 0,
        .addi .r8 .r8 4, .subi cnt cnt 1])))))

/-- Pᵢ ^= the next 32 bits of the key, for the 18 entries. -/
def keyP : Prog isa :=
  .seq (.block [.li .r9 0, .addi .r8 .r5 pOff, .li cnt 18]) (.loop keyWord (.nonzero .d cnt))

/-- The output's two words into the P-array entries at `ptr`, and the next
pair. -/
def storeP : List Instr :=
  [.store .w xL ptr 0, .store .w xR ptr 4, .addi ptr ptr 8, .subi cnt cnt 1]

/-- The first nine encryptions replace the P-array, a pair of entries each. -/
def encryptP : Prog isa :=
  .seq (.block [.addi ptr sch pOff, .li cnt 9]) (.loop (.seq (cipher true) (.block storeP)) (.nonzero .d cnt))

/-- The bytes of the word in `x` into the planes of the S-box entry at
`ptr + e`. -/
def storeEntry (x : Reg) (e : Nat) : List Instr :=
  [.stb x ptr e, .lsr .w tmp x 8, .stb tmp ptr (256 + e), .lsr .w tmp x 16, .stb tmp ptr (512 + e),
   .lsr .w tmp x 24, .stb tmp ptr (768 + e)]

/-- The output's two words into the S-box entries at `ptr`, and the next
pair: past the other planes after an S-box's last entry. -/
def storeS : Prog isa :=
  .seq (.block (storeEntry xL 0 ++ storeEntry xR 1 ++
      [.addi ptr ptr 2, .sub tmp ptr sch, .lsl tmp tmp 56]))
    (.seq (.ite (.zero .d tmp) (.block [.addi ptr ptr 768]) (.block []))
      (.block [.subi cnt cnt 1]))

/-- The other 512 replace the S-boxes. -/
def encryptS : Prog isa :=
  .seq (.block [.logic .or ptr sch sch, .li cnt 512]) (.loop (.seq (cipher true) storeS) (.nonzero .d cnt))

def expandKey : Prog isa :=
  .seq (.block (save ++ initSchedule)) (.seq keyP
    (.seq (.block [.li zero 0, .logic .or sch .r5 .r5, .li xL 0, .li xR 0])
      (.seq encryptP (.seq encryptS (.block restore)))))

end VG.Impl.Blowfish.PPC64LE
