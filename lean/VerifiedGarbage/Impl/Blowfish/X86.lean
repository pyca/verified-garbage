module

public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Impl.Blowfish.Table

/-!
# Blowfish on baseline x86 (32-bit)

One block at a time, and an S-box lookup reads every entry of the S-box's
four byte planes, a row of sixteen entries (16 bytes of each plane) at a time,
in SSE2 registers: the row that holds the index is kept under a mask made by
`cmp` and `sbb` and ORed into a register for each plane, and the index's low
four bits then choose its byte of each (`lookupEnd`). Every address and branch
is a public counter or pointer; the index is only ever an operand of the
masks' arithmetic.

Every argument is on the stack (cdecl): the schedule's address is read from
it where needed (at `esp + sch`, 4 for ECB and 12 for key expansion). The
working space `scratch` is at `ebp` throughout: our caller's `ebx`, `esi`,
`edi` and `ebp` at 0–15, the halves xL and xR at 16 and 20, F at 24, the
P-array pointer at 28, and the functions' own pointer and counter at 32 and
36. During a lookup, `esi` holds the index, `edi` the index less sixteen times
the rows read so far, `edx` the row's mask, `ebx` the row's address, `ecx` is a
temporary, `xmm0`–`xmm3` hold the planes' rows found, and `xmm6` and `xmm7`
the mask and a row. F is written with xR, unchanged, below it, as no
instruction stores four bytes of an XMM register.

`cipher sch up` is the block function: the halves at `ebp + 16` and
`ebp + 20` become their encryption (`up`) or decryption under the schedule
whose address is at `esp + sch`, changing only `eax`–`edi` but `ebp`, the
XMM registers, the flags and the working space's bytes 16–31.

The pointer and counter stay public for the taint analysis that proves
constant time as long as nothing secret is stored at an address it cannot
follow (the data, the schedule's entries): they are read before such stores
and written after.
-/

@[expose] public section

namespace VG.Impl.Blowfish.X86

open VG.X86

/-- `[base + offset]`. -/
def at_ (base : Reg) (offset : Nat) : MemOp := { base, disp := offset }

/-- An immediate. -/
def imm (n : Nat) : Src := .imm (BitVec.ofNat 32 n)

/-- The offset of byte plane `b` of S-box `j` in the schedule. -/
def planeOff (j b : Nat) : Nat := 1024 * j + 256 * b

/-- The P-array's offset in the schedule. -/
def pOff : Nat := 4096

/-- The working space's slots. -/
def xlOff : Nat := 16
def xrOff : Nat := 20
def fOff : Nat := 24
def ppOff : Nat := 28
def ptrOff : Nat := 32
def cntOff : Nat := 36

/-! ## Lookups -/

/-- `esi` := the byte of xL that indexes S-box `j`: byte `3 - j`. -/
def index (j : Nat) : List Instr :=
  [.mov .esi (.mem (at_ .ebp xlOff))] ++
    (if j < 3 then [.shift .shr .esi (8 * (3 - j))] else []) ++ [.alu .and .esi (imm 255)]

/-- An XMM operation `d := d op r`. -/
def xb (op : XBinOp) (d r : XReg) : Instr := .xop (.bin op d r)

/-- `xmm6 := ` all ones if the bit `c` of `esi` is clear, nothing if it is set. -/
def bitMask (c : Nat) : List Instr :=
  [.mov .edx (.reg .esi), .alu .and .edx (imm c), .alu .cmp .edx (imm 1), .alu .sbb .edx (.reg .edx),
   .xop (.movd .xmm6 .edx), .xop (.pshufd .xmm6 .xmm6 0)]

/-- `x := y` where `xmm6` is nothing; `x` where it is all ones. -/
def orElse (x y : XReg) : List Instr := [xb .pxor x y, xb .pand x .xmm6, xb .pxor x y]

/-- The index's row count, the planes' registers and the row pointer. -/
def lookupStart (sch : Nat) : List Instr :=
  [.mov .edi (.reg .esi), xb .pxor .xmm0 .xmm0, xb .pxor .xmm1 .xmm1, xb .pxor .xmm2 .xmm2,
   xb .pxor .xmm3 .xmm3, .mov .ebx (.mem (at_ .esp sch))]

/-- Plane `b`'s 16 bytes of the row, masked, into its register. -/
def plane (j b : Nat) (x : XReg) : List Instr :=
  [.movdquLoad .xmm7 (at_ .ebx (planeOff j b)), xb .pand .xmm7 .xmm6, xb .por x .xmm7]

/-- One row of S-box `j`: the mask (all ones if `edi < 16`), the four planes,
and the next row; the flags say whether it was the last (the schedule's
address less the row's is `-256`). -/
def row (sch j : Nat) : List Instr :=
  [.alu .cmp .edi (imm 16), .alu .sbb .edx (.reg .edx), .xop (.movd .xmm6 .edx),
   .xop (.pshufd .xmm6 .xmm6 0), .alu .sub .edi (imm 16)] ++
    plane j 0 .xmm0 ++ plane j 1 .xmm1 ++ plane j 2 .xmm2 ++ plane j 3 .xmm3 ++
    [.alu .add .ebx (imm 16), .mov .ecx (.mem (at_ .esp sch)), .alu .sub .ecx (.reg .ebx),
     .alu .cmp .ecx (imm (2 ^ 32 - 256))]

/-- The planes' rows in `xmm0`–`xmm3` transposed by doublewords: those of
doublewords 0 and 1 in `xmm4` and `xmm5` (planes 0 and 1, planes 2 and 3), of
2 and 3 in `xmm0` and `xmm2`. -/
def pairs : List Instr :=
  [xb .movdqa .xmm4 .xmm0, xb .punpckldq .xmm4 .xmm1, xb .punpckhdq .xmm0 .xmm1,
   xb .movdqa .xmm5 .xmm2, xb .punpckldq .xmm5 .xmm3, xb .punpckhdq .xmm2 .xmm3]

/-- The first doubleword of each of the four planes' pairs in `xmm4`, the
second in `xmm1`. -/
def quads : List Instr :=
  [xb .movdqa .xmm1 .xmm4, xb .punpcklqdq .xmm4 .xmm5, xb .punpckhqdq .xmm1 .xmm5]

/-- `xmm4`'s doublewords shifted right by `n` if the bit `c` of `esi` is set. -/
def shiftIf (c n : Nat) : List Instr :=
  bitMask c ++ ([xb .movdqa .xmm0 .xmm4, .xop (.shift .psrld .xmm0 (BitVec.ofNat 8 n))] : List Instr) ++
    orElse .xmm4 .xmm0

/-- The low bytes of `xmm4`'s doublewords 0 to 3 as bytes 0 to 3 of its
doubleword 0. -/
def joinBytes : List Instr :=
  [.xop (.shift .pslld .xmm4 24), .xop (.shift .psrld .xmm4 24),
   .xop (.pshufd .xmm0 .xmm4 0xF5), .xop (.shift .pslld .xmm0 8), xb .por .xmm4 .xmm0,
   .xop (.pshufd .xmm0 .xmm4 0x02), .xop (.shift .pslld .xmm0 16), xb .por .xmm4 .xmm0]

/-- The byte of each plane's row at the index's low four bits, plane `b`'s in
byte `b` of `xmm4`. -/
def lookupEnd : List Instr :=
  pairs ++ (bitMask 8 ++ (orElse .xmm4 .xmm0 ++ (orElse .xmm5 .xmm2 ++ (quads ++ (bitMask 4 ++
    (orElse .xmm4 .xmm1 ++ (shiftIf 2 16 ++ (shiftIf 1 8 ++ joinBytes))))))))

/-- S-box `j` of xL's byte `3 - j`, into `xmm4`'s low doubleword. -/
def lookup (sch j : Nat) : Prog isa :=
  .seq (.block (index j ++ lookupStart sch)) (.seq (.loop (.block (row sch j)) .ne) (.block lookupEnd))

/-- F's accumulation of S-box `j`: S₁, then + S₂, XOR S₃, + S₄; xR, below it,
is stored with it. -/
def combine (j : Nat) : List Instr :=
  (if j = 0 then [] else [.mov .ecx (.mem (at_ .ebp fOff)), .xop (.movd .xmm0 .ecx),
    xb (if j = 2 then .pxor else .paddd) .xmm4 .xmm0]) ++
  [.mov .ecx (.mem (at_ .ebp xrOff)), .xop (.movd .xmm0 .ecx), xb .punpckldq .xmm0 .xmm4,
   .movqStore (at_ .ebp xrOff) .xmm0]

/-- F of xL into `ebp + 24`. -/
def f (sch : Nat) : Prog isa :=
  .seq (lookup sch 0) (.seq (.block (combine 0)) (.seq (lookup sch 1) (.seq (.block (combine 1))
    (.seq (lookup sch 2) (.seq (.block (combine 2)) (.seq (lookup sch 3) (.block (combine 3))))))))

/-! ## Rounds

The P-array pointer is at the P-array entry of the round (`up`, encrypting),
or four bytes below it (decrypting). -/

/-- The offset from the P-array pointer of the round's entry. -/
def pAt (up : Bool) : Nat := if up then 0 else 4

/-- `xL ^= P`, `xR ^= F(xL)`, the halves swapped, and the pointer to the
next entry; the flags say whether it is the end. -/
def round (sch : Nat) (up : Bool) : Prog isa :=
  .seq (.block [.mov .ebx (.mem (at_ .ebp ppOff)), .mov .ecx (.mem (at_ .ebx (pAt up))),
      .mov .eax (.mem (at_ .ebp xlOff)), .alu .xor .eax (.reg .ecx), .store (at_ .ebp xlOff) .eax])
    (.seq (f sch)
      (.block [.mov .eax (.mem (at_ .ebp xrOff)), .alu .xor .eax (.mem (at_ .ebp fOff)),
        .mov .ecx (.mem (at_ .ebp xlOff)), .store (at_ .ebp xrOff) .ecx, .store (at_ .ebp xlOff) .eax,
        .mov .ebx (.mem (at_ .ebp ppOff)), .alu (if up then .add else .sub) .ebx (imm 4),
        .store (at_ .ebp ppOff) .ebx, .mov .ecx (.mem (at_ .esp sch)), .alu .sub .ecx (.reg .ebx),
        .alu .cmp .ecx (imm (2 ^ 32 - if up then pOff + 64 else pOff))]))

/-- The block function: the sixteen rounds, then the last swap undone, xL
(at 20) ^= P₁₈ and xR (at 16) ^= P₁₇ when encrypting, P₁ and P₂ when
decrypting, into xL and xR. -/
def cipher (sch : Nat) (up : Bool) : Prog isa :=
  .seq (.block [.mov .ebx (.mem (at_ .esp sch)), .alu .add .ebx (imm (if up then pOff else pOff + 64)),
      .store (at_ .ebp ppOff) .ebx])
    (.seq (.loop (round sch up) .ne)
      (.block [.mov .ebx (.mem (at_ .ebp ppOff)), .mov .ecx (.mem (at_ .ebx (pAt up))),
        .alu .xor .ecx (.mem (at_ .ebp xlOff)), .mov .eax (.mem (at_ .ebx (4 - pAt up))),
        .alu .xor .eax (.mem (at_ .ebp xrOff)), .store (at_ .ebp xlOff) .eax,
        .store (at_ .ebp xrOff) .ecx]))

/-! ## Our caller's registers, in the working space -/

/-- The working space (the fourth argument) into `ebp`, our caller's `ebx`,
`esi`, `edi` and `ebp` saved in it first, through `eax`. -/
def save : List Instr :=
  [.mov .eax (.mem (at_ .esp 16)), .store (at_ .eax 0) .ebx, .store (at_ .eax 4) .esi,
   .store (at_ .eax 8) .edi, .store (at_ .eax 12) .ebp, .mov .ebp (.reg .eax)]

/-- Restore them, `ebp` last. -/
def restore : List Instr :=
  [.mov .ebx (.mem (at_ .ebp 0)), .mov .esi (.mem (at_ .ebp 4)), .mov .edi (.mem (at_ .ebp 8)),
   .mov .ebp (.mem (at_ .ebp 12))]

/-! ## ECB

`vg_blowfish_ecb_{en,de}crypt(schedule, data, n, scratch)`, all on the
stack: the data pointer and the blocks left are kept in the working space. -/

/-- The block at the data pointer into the halves, as big-endian words. -/
def loadBlock : List Instr :=
  [.mov .ebx (.mem (at_ .ebp ptrOff)), .mov .eax (.mem (at_ .ebx 0)), .bswap .eax,
   .store (at_ .ebp xlOff) .eax, .mov .eax (.mem (at_ .ebx 4)), .bswap .eax, .store (at_ .ebp xrOff) .eax]

/-- The halves to the block, the next block, and the blocks left less one;
the flags say whether none are. -/
def storeBlock : List Instr :=
  [.mov .ebx (.mem (at_ .ebp ptrOff)), .mov .edx (.mem (at_ .ebp cntOff)),
   .mov .eax (.mem (at_ .ebp xlOff)), .bswap .eax, .store (at_ .ebx 0) .eax,
   .mov .eax (.mem (at_ .ebp xrOff)), .bswap .eax, .store (at_ .ebx 4) .eax,
   .alu .add .ebx (imm 8), .store (at_ .ebp ptrOff) .ebx, .alu .sub .edx (imm 1),
   .store (at_ .ebp cntOff) .edx]

def ecb (up : Bool) : Prog isa :=
  .seq (.block (save ++ [.mov .ecx (.mem (at_ .esp 8)), .store (at_ .ebp ptrOff) .ecx,
      .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp cntOff) .ecx, .alu .test .ecx (.reg .ecx)]))
    (.seq (.ite .e (.block [])
        (.loop (.seq (.block loadBlock) (.seq (cipher 4 up) (.block storeBlock))) .ne))
      (.block restore))

def encrypt : Prog isa := ecb true
def decrypt : Prog isa := ecb false

/-! ## Key expansion

`vg_blowfish_expand_key(key, key_len, schedule, scratch)`, all on the stack. -/

/-- Word `i` of the initial schedule's image, little-endian. -/
def initWord32 (i : Nat) : BitVec 32 :=
  (initWord (i / 2)).extractLsb' (32 * (i % 2)) 32

/-- Word `i` of the initial schedule, through `ecx`, at `ebx`. -/
def initStore (i : Nat) : List Instr :=
  [.mov .ecx (.imm (initWord32 i)), .store (at_ .ebx (4 * i)) .ecx]

def initSchedule : List Instr :=
  [.mov .ebx (.mem (at_ .esp 12)), .alu .add .ebx (imm 0)] ++ (List.range 1042).flatMap initStore

/-- The next key byte into the low byte of `edx` (rotated up a byte, which
moves only zeros while the word has three bytes or fewer), cycling: the
byte at `key + esi`, then `esi := esi + 1`, or 0 at `key_len`. -/
def keyByte : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .esp 4)), .alu .add .eax (.reg .esi), .movzx8 .ecx (at_ .eax 0),
      .shift .ror .edx 24, .alu .or .edx (.reg .ecx), .alu .add .esi (imm 1), .mov .eax (.mem (at_ .esp 8)),
      .alu .cmp .esi (.reg .eax)])
    (.ite .e (.block [.mov .esi (imm 0)]) (.block []))

/-- The P-array entry at `ebx + 4096` XORed with the next 32 bits of the
key; the next entry, and the entries left in `edi`. -/
def keyWord : Prog isa :=
  .seq (.block [.mov .edx (imm 0)])
    (.seq keyByte (.seq keyByte (.seq keyByte (.seq keyByte
      (.block [.mov .eax (.mem (at_ .ebx pOff)), .alu .xor .eax (.reg .edx), .store (at_ .ebx pOff) .eax,
        .alu .add .ebx (imm 4), .alu .sub .edi (imm 1)])))))

/-- Pᵢ ^= the next 32 bits of the key, for the 18 entries. -/
def keyP : Prog isa :=
  .seq (.block [.mov .esi (imm 0), .mov .ebx (.mem (at_ .esp 12)), .alu .add .ebx (imm 0),
      .mov .edi (imm 18)])
    (.loop keyWord .ne)

/-- The output's two words into the P-array entries at the pointer, the
next pair, and the encryptions left less one. -/
def storeP : List Instr :=
  [.mov .ebx (.mem (at_ .ebp ptrOff)), .mov .edx (.mem (at_ .ebp cntOff)),
   .mov .eax (.mem (at_ .ebp xlOff)), .store (at_ .ebx 0) .eax,
   .mov .eax (.mem (at_ .ebp xrOff)), .store (at_ .ebx 4) .eax,
   .alu .add .ebx (imm 8), .store (at_ .ebp ptrOff) .ebx, .alu .sub .edx (imm 1),
   .store (at_ .ebp cntOff) .edx]

/-- The first nine encryptions, by the block function `blk` (the halves at
`ebp + 16` and `ebp + 20` encrypted under the schedule whose address is at
`esp + 12`), replace the P-array, a pair of entries each. -/
def encryptPWith (blk : Prog isa) : Prog isa :=
  .seq (.block [.mov .ebx (.mem (at_ .esp 12)), .alu .add .ebx (imm pOff), .store (at_ .ebp ptrOff) .ebx,
      .mov .ecx (imm 9), .store (at_ .ebp cntOff) .ecx])
    (.loop (.seq blk (.block storeP)) .ne)

def encryptP : Prog isa := encryptPWith (cipher 12 true)

/-- The bytes of the word in `eax` into the planes of the S-box entry at
`ebx + e`. -/
def storeEntry (e : Nat) : List Instr :=
  [.store8 (at_ .ebx e) .al, .shift .shr .eax 8, .store8 (at_ .ebx (256 + e)) .al, .shift .shr .eax 8,
   .store8 (at_ .ebx (512 + e)) .al, .shift .shr .eax 8, .store8 (at_ .ebx (768 + e)) .al]

/-- The output's two words into the S-box entries at the pointer, and the
next pair: past the other planes after an S-box's last entry. -/
def storeS : Prog isa :=
  .seq (.block ([.mov .ebx (.mem (at_ .ebp ptrOff)), .mov .edx (.mem (at_ .ebp cntOff)),
      .mov .eax (.mem (at_ .ebp xlOff))] ++ storeEntry 0 ++ [.mov .eax (.mem (at_ .ebp xrOff))] ++
      storeEntry 1 ++ [.alu .add .ebx (imm 2), .mov .ecx (.mem (at_ .esp 12)), .alu .sub .ecx (.reg .ebx),
      .alu .test .ecx (imm 255)]))
    (.seq (.ite .e (.block [.alu .add .ebx (imm 768)]) (.block []))
      (.block [.store (at_ .ebp ptrOff) .ebx, .alu .sub .edx (imm 1), .store (at_ .ebp cntOff) .edx]))

/-- The other 512 replace the S-boxes. -/
def encryptSWith (blk : Prog isa) : Prog isa :=
  .seq (.block [.mov .ebx (.mem (at_ .esp 12)), .store (at_ .ebp ptrOff) .ebx, .mov .ecx (imm 512),
      .store (at_ .ebp cntOff) .ecx])
    (.loop (.seq blk storeS) .ne)

def encryptS : Prog isa := encryptSWith (cipher 12 true)

/-- Key expansion with the block function `blk` for its 521 encryptions. -/
def expandKeyWith (blk : Prog isa) : Prog isa :=
  .seq (.block (save ++ initSchedule))
    (.seq keyP
      (.seq (.block [.mov .eax (imm 0), .store (at_ .ebp xlOff) .eax, .store (at_ .ebp xrOff) .eax])
        (.seq (encryptPWith blk) (.seq (encryptSWith blk) (.block restore)))))

def expandKey : Prog isa := expandKeyWith (cipher 12 true)

end VG.Impl.Blowfish.X86
