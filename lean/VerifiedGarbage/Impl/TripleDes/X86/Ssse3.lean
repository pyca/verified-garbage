module

public import VerifiedGarbage.Impl.Modes.X86.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained

/-!
# Triple DES on x86 (32-bit) with its S-boxes by `pshufb`: one block

A core of the modes (`core`, `Impl.Modes.X86.Core`) for one block at a time,
for the modes that chain their blocks (CBC encryption, CFB, OFB), where the
bitsliced code of 32 blocks does not apply. It is `ssse3` code: its
functions' dispatchers run it only where the CPU has SSSE3.

A round's eight S-boxes are sixteen `pshufb`. The six input bits of an
S-box are in a byte of the index register, with `0x40` (which `pshufb`
ignores): the low four choose among sixteen bytes of a table, and the other
two, the row, are chosen by adding 16 to the index one, two and three times
(`pshufb` gives zero where the index's high bit is set, so the table read
with the index plus `16 s` counts for the rows below `4 - s`, and the
tables hold differences of rows). Two S-boxes share each table's bytes, by
their bits (`oMask`), so four tables a row. The outputs' bits are placed in
their bytes so that the permutation P after them is six rotations of the
word under masks (`oP`).

The halves are kept rotated right by one bit through the 48 rounds, so that
the S-boxes' inputs after the expansion E are the bytes of the half shifted
right by two and of the half rotated left by two; between the three DES
passes only the halves are exchanged; the initial and the final permutation
are five exchanges of bits each, in the general registers.

With the modes' scratch buffer at `sb`: its first slot holds the address of
the table of constants `VG_TRIPLE_DES_SSSE3` (taken once, by `prepare`, with
`symPush`), the block is at byte 8, two slots of 16 bytes for the halves are
at bytes 16 and 32 (`sA`, `sB`), and the 48 rounds' keys are from byte 48 on
(`keyOff`), eight bytes a round in the order of use: `prepare` makes them
from the schedule `vg_triple_des_expand_key` stores (the second key's in
reverse order, for the decryption in the middle), the six bits of the
S-boxes 6, 4, 2, 0 in the bytes of the first word and of 7, 5, 3, 1 in those
of the second, each with `0x40`.

A round (`round`) has its input half in `xmm7` (the low doubleword) and its
target in one of the two slots; it stores the input half in the other slot,
which is the next round's target, and leaves the new half in `xmm7`. One
register, `xmm6`, only ever holds constants and the round's key, and the
index register is `xmm7` itself, stepped in place: on a processor that
makes an instruction that writes a whole register wait for the register's
old value, no load then waits for a value the round computes late. The
rounds are two nested loops (`rounds`): three passes of eight double
rounds.

No address and no branch depends on a key or a block, and every store is
through `sb` at a fixed offset.
-/

@[expose] public section

namespace VG.Impl.TripleDes.X86.Ssse3

open VG.X86
open VG.Impl.Modes.X86 (sb at_ argOp Core)
open VG.Impl.Modes (Mode)

/-- The table of constants' name. -/
def tableName : String := "VG_TRIPLE_DES_SSSE3"

/-- The constants, 16 bytes each (two words): the mask of an S-box's six
bits in the low eight bytes, the index step in them, the sixteen look-up
tables, the four masks of the pairs of S-boxes, and P's six masks. -/
def table : List (BitVec 64) := [
  0x3f3f3f3f3f3f3f3f, 0x0000000000000000, 0x1010101010101010, 0x0000000000000000,
  0xf1c37bf393bbb6bd, 0x4d4dc77d3e771b71, 0x0e77423544414736, 0xa7fc3081d4c694c6,
  0xbd8eedcf7ef6fef5, 0xd54bc77b3f3ffd4d, 0xd866221b8edde750, 0x6b1295e434a97927,
  0x2bed5d3dfa5a7a6a, 0x3ff59995e766b7e6, 0xd105be2ac0b5e14d, 0xf0186a5cbbdf2c3b,
  0xedefc5dd3ffadffa, 0xe727b7b76667fec5, 0xd6990443fb50adf7, 0x3ee3198c013ee225,
  0x738d714dfffdf38f, 0x9be59df5e75beff9, 0xdae688a012872ff8, 0x62886b293aafba2f,
  0x375d275a796f5966, 0x8f73befdcc71cdf1, 0x3bdce62ac72170bf, 0xdc470ad26d8a9765,
  0xfe79bcab3ee5b76d, 0x3beff1addbd3dacb, 0x3b455334a2ba58da, 0xfd73978265ec7c25,
  0x76febedbcf6da5bc, 0xb3afcbdf2b75f1f1, 0xe6cd9d2ead625bfc, 0x7a17c74914b1a09a,
  0x00000027000000d8, 0x0000000000000000, 0x00008e0000007100, 0x0000000000000000,
  0x003c000000c30000, 0x0000000000000000, 0x17000000e8000000, 0x0000000000000000,
  0x0000000084448844, 0x0000000000000000, 0x0000000001002020, 0x0000000000000000,
  0x0000000018094082, 0x0000000000000000, 0x0000000042820108, 0x0000000000000000,
  0x0000000020100601, 0x0000000000000000, 0x0000000000201010, 0x0000000000000000
]

/-! ## The constants' offsets -/

/-- `0x3f` in the low eight bytes. -/
def oM : Nat := 0
/-- 16 in the low eight bytes. -/
def oStep : Nat := 16
/-- The table of the pair `p` of S-boxes read with the index `s` steps on. -/
def oT (p s : Nat) : Nat := 32 + 64 * p + 16 * (3 - s)
/-- The bits of the pair `p`'s two S-boxes, in their two bytes. -/
def oMask (p : Nat) : Nat := 288 + 16 * p
/-- The mask of P's rotation `i`, in the low doubleword. -/
def oP (i : Nat) : Nat := 352 + 16 * i

/-! ## The scratch buffer -/

/-- The block's byte offset. -/
def blkOff : Nat := 8
/-- The two slots of the halves. -/
def sA : Nat := 16
def sB : Nat := 32
/-- The rounds' keys. -/
def keyOff : Nat := 48

/-- The table's base register in `crypt`. -/
def tbr : Reg := .ebx
/-- The pointer to the keys of the double round at hand. -/
def kr : Reg := .ebp

/-- A constant to `d`. -/
def tb (d : XReg) (off : Nat) : Instr := .movdquTbl d (at_ tbr off) tableName table
def x (op : XBinOp) (a b : XReg) : Instr := .xop (.bin op a b)
def sh (op : XShiftOp) (a : XReg) (n : Nat) : Instr := .xop (.shift op a (BitVec.ofNat 8 n))
def ld (d : XReg) (b : Reg) (off : Nat) : Instr := .movdquLoad d (at_ b off)
def stx (b : Reg) (off : Nat) (r : XReg) : Instr := .movdquStore (at_ b off) r

/-! ## A round -/

/-- A round with its keys at `[kr + koff]`: the input half, in `xmm7`, to
the slot at `sin`, and the half at `stgt` exclusive-ored with the round
function of the input half to `xmm7`. -/
def round (sin stgt koff : Nat) : List Instr :=
  [-- the input half to its slot; its expansion in place, the key, the index step
   stx sb sin .xmm7, .xop (.pshufd .xmm0 .xmm7 0), sh .psrld .xmm7 2,
   sh .psrlq .xmm0 30, x .punpckldq .xmm7 .xmm0, tb .xmm6 (oM),
   x .pand .xmm7 .xmm6, .movqLoad .xmm6 (at_ kr koff), x .pxor .xmm7 .xmm6,
   tb .xmm6 (oStep),
   -- the sixteen look-ups, the index a step on after every four
   tb .xmm2 (oT 0 0), x .pshufb .xmm2 .xmm7, tb .xmm3 (oT 1 0),
   x .pshufb .xmm3 .xmm7, tb .xmm1 (oT 2 0), x .pshufb .xmm1 .xmm7,
   tb .xmm4 (oT 3 0), x .pshufb .xmm4 .xmm7, x .paddd .xmm7 .xmm6,
   tb .xmm5 (oT 0 1), x .pshufb .xmm5 .xmm7, x .pxor .xmm5 .xmm2,
   tb .xmm0 (oT 1 1), x .pshufb .xmm0 .xmm7, x .pxor .xmm0 .xmm3,
   tb .xmm2 (oT 2 1), x .pshufb .xmm2 .xmm7, x .pxor .xmm2 .xmm1,
   tb .xmm1 (oT 3 1), x .pshufb .xmm1 .xmm7, x .pxor .xmm1 .xmm4,
   x .paddd .xmm7 .xmm6, tb .xmm3 (oT 0 2), x .pshufb .xmm3 .xmm7,
   x .pxor .xmm5 .xmm3, tb .xmm4 (oT 1 2), x .pshufb .xmm4 .xmm7,
   x .pxor .xmm0 .xmm4, tb .xmm3 (oT 2 2), x .pshufb .xmm3 .xmm7,
   x .pxor .xmm3 .xmm2, tb .xmm4 (oT 3 2), x .pshufb .xmm4 .xmm7,
   x .pxor .xmm4 .xmm1, x .paddd .xmm7 .xmm6, tb .xmm1 (oT 0 3),
   x .pshufb .xmm1 .xmm7, x .pxor .xmm1 .xmm5, tb .xmm2 (oT 1 3),
   x .pshufb .xmm2 .xmm7, x .pxor .xmm2 .xmm0, tb .xmm0 (oT 2 3),
   x .pshufb .xmm0 .xmm7, x .pxor .xmm3 .xmm0, tb .xmm5 (oT 3 3),
   x .pshufb .xmm5 .xmm7, x .pxor .xmm4 .xmm5,
   -- the pairs' masks, the four sums, and the word of the S-boxes' outputs twice in the low quadword
   tb .xmm6 (oMask 0), x .pand .xmm1 .xmm6,
   tb .xmm6 (oMask 1), x .pand .xmm2 .xmm6,
   tb .xmm6 (oMask 2), x .pand .xmm3 .xmm6,
   tb .xmm6 (oMask 3), x .pand .xmm4 .xmm6,
   x .pxor .xmm1 .xmm2, x .pxor .xmm3 .xmm4,
   x .pxor .xmm1 .xmm3, .xop (.pshufd .xmm0 .xmm1 0xe1),
   x .pxor .xmm0 .xmm1,
   -- P: six shifts of that quadword under their masks
   x .movdqa .xmm5 .xmm0, sh .psrlq .xmm5 7, tb .xmm6 (oP 0), x .pand .xmm5 .xmm6,
   x .movdqa .xmm2 .xmm0, sh .psrlq .xmm2 15, tb .xmm6 (oP 1), x .pand .xmm2 .xmm6,
   x .pxor .xmm5 .xmm2, x .movdqa .xmm4 .xmm0, sh .psrlq .xmm4 16, tb .xmm6 (oP 2),
   x .pand .xmm4 .xmm6, x .movdqa .xmm3 .xmm0, sh .psrlq .xmm3 23, tb .xmm6 (oP 3),
   x .pand .xmm3 .xmm6, x .pxor .xmm4 .xmm3, x .pxor .xmm5 .xmm4, x .movdqa .xmm1 .xmm0,
   sh .psrlq .xmm1 27, tb .xmm6 (oP 4), x .pand .xmm1 .xmm6, sh .psrlq .xmm0 30,
   tb .xmm6 (oP 5), x .pand .xmm0 .xmm6, x .pxor .xmm1 .xmm0,
   -- the target half
   ld .xmm7 sb stgt, x .pxor .xmm7 .xmm1, x .pxor .xmm7 .xmm5]

/-- Two rounds, and on to the next two: ZF is set after the pass's last. -/
def double : List Instr :=
  round sA sB 0 ++ round sB sA 8 ++ [.alu .add kr (.imm 16), .alu .sub .ecx (.imm 1)]

/-- The halves exchanged after a pass (the half the pass's last round made
is the next pass's target, as DES's final exchange and the next initial
split make it), and one pass fewer: ZF is set after the last. -/
def exchange : List Instr :=
  [ld .xmm0 sb sB, stx sb sB .xmm7, x .movdqa .xmm7 .xmm0, .alu .sub .edx (.imm 1)]

/-- The 48 rounds: three passes of eight double rounds. -/
def rounds : Prog isa :=
  .loop (.seq (.block [.mov .ecx (.imm 8)]) (.seq (.loop (.block double) .ne) (.block exchange))) .ne

/-! ## The block -/

/-- `t = ((a >> n) ^ b) & m`, `b ^= t`, `a ^= t << n` (a rotation: `m`'s top
`n` bits are zero), through `eax`. -/
def swap (a b : Reg) (n : Nat) (m : BitVec 32) : List Instr :=
  [.mov .eax (.reg a), .shift .shr .eax n, .alu .xor .eax (.reg b), .alu .and .eax (.imm m),
   .alu .xor b (.reg .eax), .shift .ror .eax (32 - n), .alu .xor a (.reg .eax)]

/-- The initial permutation of the block's two big-endian words in `esi`
and `ecx`, and each half rotated right by one. -/
def ip : List Instr :=
  swap .esi .ecx 4 0x0f0f0f0f ++ swap .esi .ecx 16 0x0000ffff ++ swap .ecx .esi 2 0x33333333 ++
    swap .ecx .esi 8 0x00ff00ff ++ swap .esi .ecx 1 0x55555555 ++ [.shift .ror .esi 1, .shift .ror .ecx 1]

/-- The halves rotated back, and the final permutation. -/
def fp : List Instr :=
  [.shift .ror .esi 31, .shift .ror .ecx 31] ++ swap .esi .ecx 1 0x55555555 ++ swap .ecx .esi 8 0x00ff00ff ++
    swap .ecx .esi 2 0x33333333 ++ swap .esi .ecx 16 0x0000ffff ++ swap .esi .ecx 4 0x0f0f0f0f

/-- The block at byte 8 of the scratch buffer to the first round's halves
(the left one to the slot `sB`, the right one to `xmm7`), the table's
address, the keys' pointer and the count of the passes. -/
def cryptHead : List Instr :=
  [.mov tbr (.mem (at_ sb 0)), .mov .esi (.mem (at_ sb blkOff)), .mov .ecx (.mem (at_ sb (blkOff + 4))),
   .bswap .esi, .bswap .ecx] ++ ip ++
  [.xop (.movd .xmm0 .esi), stx sb sB .xmm0, .xop (.movd .xmm7 .ecx),
   .mov kr (.reg sb), .alu .add kr (.imm (BitVec.ofNat 32 keyOff)), .mov .edx (.imm 3)]

/-- The halves after the last exchange to the block. -/
def cryptTail : List Instr :=
  [stx sb sA .xmm7, .mov .esi (.mem (at_ sb sB)), .mov .ecx (.mem (at_ sb sA))] ++ fp ++
  [.bswap .esi, .bswap .ecx, .store (at_ sb blkOff) .esi, .store (at_ sb (blkOff + 4)) .ecx]

/-- The block of the core's buffer, enciphered in place. -/
def crypt : Prog isa := .seq (.block cryptHead) (.seq rounds (.block cryptTail))

/-! ## The keys -/

/-- `(x >> n) & m` (`rot = false`) or `(x ror n) & m` of the word at
`[src + off]`, to `ebp`. -/
def field (src : Reg) (off : Nat) (rot : Bool) (n : Nat) (m : BitVec 32) : List Instr :=
  [.mov .ebp (.mem (at_ src off)), .shift (if rot then .ror else .shr) .ebp n, .alu .and .ebp (.imm m)]

/-- The two words of a round's keys, at `[esi + dst]`, from the round key in
the eight bytes at `[src + off]` (48 bits, the first S-box's six the highest),
through `ebx` and `ebp`. -/
def key (src : Reg) (off dst : Nat) : List Instr :=
  field src off false 6 0x3f ++ [.mov .ebx (.reg .ebp)] ++
  field src off false 10 0x3f00 ++ [.alu .or .ebx (.reg .ebp)] ++
  field src off false 14 0x30000 ++ [.alu .or .ebx (.reg .ebp)] ++
  field src (off + 4) true 14 0x3c0000 ++ [.alu .or .ebx (.reg .ebp)] ++
  field src (off + 4) true 18 0x3f000000 ++ [.alu .or .ebx (.reg .ebp), .alu .or .ebx (.imm 0x40404040),
    .store (at_ .esi dst) .ebx] ++
  field src off false 4 0x3f00 ++ [.mov .ebx (.reg .ebp), .mov .ebp (.mem (at_ src off)),
    .alu .and .ebp (.imm 0x3f), .alu .or .ebx (.reg .ebp)] ++
  field src off false 8 0x3f0000 ++ [.alu .or .ebx (.reg .ebp)] ++
  field src (off + 4) true 12 0x3f000000 ++ [.alu .or .ebx (.reg .ebp), .alu .or .ebx (.imm 0x40404040),
    .store (at_ .esi (dst + 4)) .ebx]

/-- The table's address to the scratch buffer's first slot; the schedule's
first round key at `eax` and the second key's last at `edx`, the rounds'
keys at `esi`, and the count of the round keys of a key. -/
def prepHead : List Instr :=
  [.store (at_ sb 0) .eax, .mov .eax (.mem (argOp 0)), .mov .edx (.reg .eax), .alu .add .edx (.imm 248),
   .mov .esi (.reg sb), .alu .add .esi (.imm (BitVec.ofNat 32 keyOff)), .mov .ecx (.imm 16)]

/-- A round's keys of each of the three passes: the first key's forward, the
second's backward, the third's forward. -/
def prepBody : List Instr :=
  key .eax 0 0 ++ key .edx 0 128 ++ key .eax 256 256 ++
  [.alu .add .eax (.imm 8), .alu .sub .edx (.imm 8), .alu .add .esi (.imm 8), .alu .sub .ecx (.imm 1)]

/-- The keys the rounds read, from the schedule in the first stack
argument, and the table's address. -/
def prepare : Prog isa :=
  .seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1))
    (.seq (.block prepHead) (.loop (.block prepBody) .ne))

/-- The core's slots, as many as the core's of the block function a round
at a time (`dirCore`), so that the functions' working space is the same:
the table's address and a spare slot, the block, the two slots of the
halves, and the 96 words of the keys take 108. -/
def slots : Nat := 226

/-- The modes' core: one block at a time. -/
def core : Core :=
  { prepare := prepare, crypt := crypt, slots := slots, total := slots + 10, buf := 2, G := 1, bw := 2, stack := 16 }

/-- CBC encryption that updates the chaining value. -/
def cbcEncryptChained : Prog isa := core.seq (Mode.cbcEncChained 2)

end VG.Impl.TripleDes.X86.Ssse3
