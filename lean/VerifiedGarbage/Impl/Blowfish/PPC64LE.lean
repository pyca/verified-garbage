module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Impl.Blowfish.Table

/-!
# Blowfish on PPC64LE

One block at a time, the halves and F in general-purpose registers. An
S-box lookup reads every entry of the S-box's four byte planes
(`Spec.Blowfish.scheduleAt`), 32 entries of each (a *row*, two vectors,
`lxvd2x`) at a time, and keeps each plane's row under a mask that is all
ones exactly if the row holds the index `q` (`vsel`). The mask is byte
`q >> 5` of a one-hot vector whose one byte of ones moves on a byte each row
(`vperm`, `vsldoi`). Once every row is read, `vperm` picks byte `q mod 32`
of each plane's kept row, and the four bytes make the entry. Every address
and branch is a public counter or pointer; the index is only ever in the
masks' and `vperm`'s operands, whose time does not depend on their values.

The halves, F and the entry are 32-bit values in the low words of their
registers; their high words are whatever the arithmetic leaves, which
nothing reads: word rotations and shifts read the low word, `stw` stores it,
and the index is taken from it.

Registers: zero in `r0`, the schedule at `r3` (`sch`), the halves in `r4`
(xL) and `r5` (xR), F in `r7`, the P-array pointer in `r8`; during a lookup,
the index in `r9` (`q`), then the offset 272, the entry in `r10`, the
offsets 16 and 256 in `r11` and `r14`, a temporary in `r12` and the row
pointer in `r15`, with `v0`–`v17`. ECB keeps the data pointer in `r16` and
the blocks left in `r17`; key expansion, the pointer to the next entries in
`r16` and the encryptions left in `r17`. The caller's `r14`–`r17` are kept
in the working space, at `r6`.
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
def tmp : Reg := .r12
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

/-- The registers of a lookup's loop: the offsets 16, 256 and 272 from the
row pointer, in `r11`, `r14` and `r9` (`q`'s, once the vectors that need it
are made). -/
def o16 : Reg := .r11
def o256 : Reg := .r14
def o272 : Reg := .r9

/-- The vector registers of a lookup: zero, the index (XORed with 7) and
its chunk (`q >> 5`) in every byte, the chunk's one-hot byte, the mask, a
loaded vector, the selected chunk of each plane (two vectors each), and
the entry's bytes. -/
def vZero : VReg := .v0
def vIdx : VReg := .v1
def vChunk : VReg := .v2
def vHot : VReg := .v3
def vMask : VReg := .v4
def vLoad : VReg := .v5
def vSel (k : Nat) : VReg := [.v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13].getD k .v6
def vByte (b : Nat) : VReg := [.v14, .v15, .v16, .v17].getD b .v14

/-- `vperm d n m c`. -/
def vperm (d n m c : VReg) : Instr := .vop (.perm d n m c)

/-- `v := x` in every byte, from `x << 56` in `tmp`. -/
def splat (v : VReg) : List Instr := [.lsl tmp tmp 56, .mtvsrd v tmp, vperm v v v vZero]

/-- The lookup's vectors and registers: zero; `q XOR 7` in every byte (the
byte `vperm` takes for `q`'s byte of 32 that `lxvd2x` loaded, whose bytes it
numbers `XOR 7`); `q >> 5` in every byte; `0xFF` in byte 0 of the one-hot
vector and zero in bytes 1–7; the row pointer at the S-box; and the
offsets. -/
def lookupStart (j : Nat) : List Instr :=
  [.vop (.logic .xor vZero vZero vZero), .li tmp 7, .logic .xor tmp qReg tmp] ++ splat vIdx ++
    [.lsr .d tmp qReg 5] ++ splat vChunk ++
    [.li tmp 255, .lsl tmp tmp 56, .mtvsrd vHot tmp, .addi rowPtr sch (1024 * j), .li o16 16,
      .li o256 256, .li o272 272]

/-- The offset register of half `h` of plane `b` (planes 2 and 3 are read
512 bytes further on). -/
def offReg (b h : Nat) : Reg :=
  if b % 2 = 0 then (if h = 0 then zero else o16) else (if h = 0 then o256 else o272)

/-- Half `h` of plane `b`'s 32 bytes of the row, kept if the mask is set. -/
def selLoad (b h : Nat) : List Instr :=
  [.lxvd2x vLoad rowPtr (offReg b h), .vop (.sel (vSel (2 * b + h)) (vSel (2 * b + h)) vLoad vMask)]

/-- Row `i` of S-box `j`: 32 entries, each plane's 32 bytes of them kept
(all ones) if the row holds the index (`i = q >> 5`: byte `q >> 5` of the
one-hot vector, which then moves on a byte), and the next row; `tmp` is
zero after the last. -/
def row (j : Nat) : List Instr :=
  [vperm vMask vHot vHot vChunk, .vop (.sldoi vHot vZero vHot 15)] ++
    selLoad 0 0 ++ selLoad 0 1 ++ selLoad 1 0 ++ selLoad 1 1 ++ [.addi rowPtr rowPtr 512] ++
    selLoad 2 0 ++ selLoad 2 1 ++ selLoad 3 0 ++ selLoad 3 1 ++
    [.subi rowPtr rowPtr 480, .sub tmp rowPtr sch, .subi tmp tmp (1024 * j + 256)]

/-- Byte `b` of the entry, from plane `b`'s row, into the accumulator. -/
def entryByte (b : Nat) : List Instr :=
  if b = 0 then [.mfvsrd acc (vByte 0), .lsr .d acc acc 56]
  else [.mfvsrd tmp (vByte b), .lsr .d tmp tmp 56, .lsl tmp tmp (8 * b), .logic .or acc acc tmp]

/-- The entry: each plane's byte `q mod 32` of its row, in every byte of
`vByte b` (`vperm`), then into the accumulator. -/
def lookupEnd : List Instr :=
  (List.range 4).map (fun b => vperm (vByte b) (vSel (2 * b)) (vSel (2 * b + 1)) vIdx) ++
    entryByte 0 ++ entryByte 1 ++ entryByte 2 ++ entryByte 3

/-- S-box `j` of xL's byte `3 - j`, into the accumulator. -/
def lookup (j : Nat) : Prog isa :=
  .seq (.block (index j ++ lookupStart j))
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
