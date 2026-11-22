module

public import VerifiedGarbage.Impl.Camellia.X86.AesNi
public import VerifiedGarbage.Impl.Camellia.X86.Crypt8
public import VerifiedGarbage.Impl.Modes.X86.Wide

/-!
# Camellia on x86 (32-bit) with its S-boxes by `aesenclast`: four blocks at a time

The block function of `AesNi.lean` on four blocks, two to a register: a
half of two blocks' data in the two quadwords of a register, each byte
where that file's round keeps it (a quadword there holds what the two
quadwords of its spread register add up to), so the keys in the scratch
buffer are that file's, a quadword of them read into both quadwords of a
register. A round's shuffles take each quadword's bytes from the eight
`aesenclast` leaves of its own block (`ShiftRows` moves half of them to the
other quadword), ten shuffles for the four maps after the S-box.

The four blocks are two pairs. The pairs' halves are in four places of the
scratch buffer (16 bytes each, at byte 512), and the code is four parts
that each read and write only those places, the keys and the blocks: the
blocks to the places (`wIn`), the six rounds of a group (`wGroup`), the FL
layer after it (`wLayer`), and the places to the blocks (`wOut`). Each part
is written out below as it runs: the instructions of both pairs in an order,
and with registers, that keep a register's whole-register writes apart from
what it last held (the half a round S-boxes stays in one register from the
round before, which stores it for the round after). Its proof
(`Proof/Camellia/X86/AesNiWideMaps.lean`) is that it computes what the same
steps do one pair after the other (`refIn`, `refGroup`, `refLayer`,
`refOut` there), which the kernel checks (`Proof/Framework/X86/SseEquiv.lean`).

`prepare d` and `crypt` are a core of the modes (`core d`) for four blocks
at a time, in the direction `d`. The scratch buffer's first slot holds the
address of this file's table of constants, bytes 24 to 504 the keys as
`AesNi.prepare` makes them, bytes 512 to 576 the places, and bytes 576 to
640 the four blocks. `prepare` copies the schedule to byte 544 of the
scratch buffer, for decryption with its subkeys in the order decryption
takes them (`Spec.Camellia.reverseSubkeys`: the first and last pairs
exchanged, the others in reverse), and makes the keys from the copy with
`AesNi.prepare`'s code and table.

The code is `aes` and `ssse3` code: its dispatcher runs it only where the
CPU has both.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86.AesNiWide

open VG.X86
open VG.Impl.Modes.X86 (sb at_ argOp Core)
open VG.Impl.Camellia.X86.AesNi (tbr kr m0 x ld stx)

/-- The table of constants' name. -/
def tableName : String := "VG_CAMELLIA_AESNI_WIDE"

/-- The constants, 16 bytes each (two words): `AesNi.table`'s masks and
nibble tables, and a round's ten shuffles. -/
def table : List (BitVec 64) := [
  0x0f0f0f0f0f0f0f0f, 0x0f0f0f0f0f0f0f0f, 0x0405060700010203, 0x0c0d0e0f08090a0b,
  0x00000f000000000f, 0x00000f000000000f, 0xa9a8b0b118190100, 0x02031b1ab3b2aaab,
  0x55f2c6613493a700, 0x8c2b1fb8ed4a7ed9, 0xaab2021ab0a81800, 0xa6be0e16bca4140c,
  0x7e4a8cb8c6f23400, 0xa69254601e2aecd8, 0xd3d2dcdd0e0f0100, 0x16171918cbcac4c5,
  0x8741ac6aed2bc600, 0x6fa9448205c32ee8, 0x3abbb23309888100, 0x1d9c95142eafa627,
  0x44e1fa5f1bbea500, 0xd87d66c38722399c, 0xf2943c5a6305adcb, 0x0066cea891f75f39,
  0xb9ff0c4af3b54600, 0x581eedab1254a7e1, 0xb88298a27d475d67, 0x003a201ac5ffe5df,
  0xc1953460a1f55400, 0x0652f3a7663293c7, 0x34263e2ce3f1e9fb, 0x00120a18d7c5ddcf,
  0x2bf71ac6ed31dc00, 0x5c806db19a46ab77, 0xd8bab6d42f4d4123, 0x00626e0cf79599fb,
  0xa99bf2c0695b3200, 0xfac8a1933a086153, 0x07010d070707070d, 0x0f09050f0f0f0f05,
  0x01040e000000040e, 0x090c060808080c06, 0x0480800101018080, 0x0c80800909098080,
  0x8080808004048080, 0x808080800c0c8080, 0x0a0a000b800a0a00, 0x0202080380020208,
  0x800b0480800b0b01, 0x80030c8080030309, 0x0e0d800e0d800d80, 0x0605800605800580,
  0x808080800e800e80, 0x8080808006800680, 0x80800b808080800a, 0x8080038080808002,
  0x808080808080800b, 0x8080808080808003
]

/-! ## The constants' offsets -/

def wM0 : Nat := 0
def wBSW : Nat := 16
def wM4 : Nat := 32
/-- The byte maps into the rounds' form and out of it, as `AesNi.oT` and
`AesNi.oI`. -/
def wT : Nat := 48
def wI : Nat := 112
/-- The four maps after the S-box, as `AesNi.oN`. -/
def wN : Nat → Nat := fun k => 176 + 32 * k
/-- Shuffle `i` of map `k`'s bytes: four of `N_0`'s, two of each other's. -/
def wS : Nat → Nat → Nat := fun k i => 304 + 16 * ([0, 4, 6, 8].getD k 0 + i)

/-- A constant to `d`. -/
def tb (d : XReg) (off : Nat) : Instr := .movdquTbl d (at_ tbr off) tableName table
/-- The eight bytes at `off` of the group's keys to `d`'s low quadword. -/
def lq (d : XReg) (off : Nat) : Instr := .movqLoad d (at_ kr off)
def sh (op : XShiftOp) (a : XReg) (n : Nat) : Instr := .xop (.shift op a n)

/-! ## The four parts, as they run -/

/-- The four blocks of the buffer to the pairs' halves in their places, in the rounds' form with the
first keys: `refIn`, scheduled. -/
def wIn : List Instr := [
  ld .xmm0 sb 592, ld .xmm1 sb 576, tb .xmm2 16, x .pshufb .xmm1 .xmm2, x .pshufb .xmm0 .xmm2, x .movdqa .xmm3 .xmm1,
  x .punpckhqdq .xmm3 .xmm0, x .punpcklqdq .xmm1 .xmm0, x .movdqa .xmm4 .xmm7, x .pand .xmm4 .xmm1,
  sh .psrld .xmm1 4, x .pand .xmm1 .xmm7, tb .xmm5 48, x .pshufb .xmm5 .xmm4, tb .xmm6 32, x .pand .xmm4 .xmm6,
  x .pand .xmm6 .xmm1, tb .xmm2 64, x .pshufb .xmm2 .xmm1, x .pxor .xmm5 .xmm2, tb .xmm0 80, x .pshufb .xmm0 .xmm4,
  x .pxor .xmm5 .xmm0, tb .xmm1 96, x .pshufb .xmm1 .xmm6, x .pxor .xmm5 .xmm1, lq .xmm4 0,
  x .punpcklqdq .xmm4 .xmm4, x .pxor .xmm5 .xmm4, stx sb 512 .xmm5, x .movdqa .xmm0 .xmm7, x .pand .xmm0 .xmm3,
  sh .psrld .xmm3 4, x .pand .xmm3 .xmm7, tb .xmm2 48, x .pshufb .xmm2 .xmm0, tb .xmm6 32, x .pand .xmm0 .xmm6,
  x .pand .xmm6 .xmm3, ld .xmm1 sb 608, ld .xmm4 sb 624, tb .xmm5 64, x .pshufb .xmm5 .xmm3, x .pxor .xmm2 .xmm5,
  tb .xmm3 16, x .pshufb .xmm1 .xmm3, x .pshufb .xmm4 .xmm3, tb .xmm3 80, x .pshufb .xmm3 .xmm0, x .pxor .xmm2 .xmm3,
  tb .xmm0 96, x .pshufb .xmm0 .xmm6, x .pxor .xmm2 .xmm0, lq .xmm6 8, x .punpcklqdq .xmm6 .xmm6,
  x .pxor .xmm2 .xmm6, stx sb 528 .xmm2, x .movdqa .xmm3 .xmm1, x .punpckhqdq .xmm3 .xmm4, x .punpcklqdq .xmm1 .xmm4,
  x .movdqa .xmm4 .xmm7, x .pand .xmm4 .xmm1, sh .psrld .xmm1 4, x .pand .xmm1 .xmm7, tb .xmm6 48,
  x .pshufb .xmm6 .xmm4, tb .xmm0 32, x .pand .xmm4 .xmm0, x .pand .xmm0 .xmm1, tb .xmm5 64, x .pshufb .xmm5 .xmm1,
  x .pxor .xmm6 .xmm5, tb .xmm1 80, x .pshufb .xmm1 .xmm4, x .pxor .xmm6 .xmm1, tb .xmm4 96, x .pshufb .xmm4 .xmm0,
  x .pxor .xmm6 .xmm4, lq .xmm0 0, x .punpcklqdq .xmm0 .xmm0, x .pxor .xmm6 .xmm0, stx sb 544 .xmm6,
  x .movdqa .xmm1 .xmm7, x .pand .xmm1 .xmm3, sh .psrld .xmm3 4, x .pand .xmm3 .xmm7, tb .xmm5 48,
  x .pshufb .xmm5 .xmm1, tb .xmm0 32, x .pand .xmm1 .xmm0, x .pand .xmm0 .xmm3, tb .xmm4 64, x .pshufb .xmm4 .xmm3,
  x .pxor .xmm5 .xmm4, tb .xmm3 80, x .pshufb .xmm3 .xmm1, x .pxor .xmm5 .xmm3, tb .xmm2 96, x .pshufb .xmm2 .xmm0,
  x .pxor .xmm5 .xmm2, lq .xmm0 8, x .punpcklqdq .xmm0 .xmm0, x .pxor .xmm5 .xmm0, stx sb 560 .xmm5]

/-- The six rounds of a group on both pairs: `refGroup`, scheduled. -/
def wGroup : List Instr := [
  ld .xmm0 sb 512, x .aesenclast .xmm0 .xmm7, ld .xmm1 sb 528, x .movdqa .xmm2 .xmm7, x .pand .xmm2 .xmm0,
  sh .psrld .xmm0 4, x .pand .xmm0 .xmm7, tb .xmm3 272, x .pshufb .xmm3 .xmm2, tb .xmm4 240, x .pshufb .xmm4 .xmm2,
  tb .xmm5 288, x .pshufb .xmm5 .xmm0, x .pxor .xmm3 .xmm5, tb .xmm6 256, x .pshufb .xmm6 .xmm0, x .pxor .xmm4 .xmm6,
  tb .xmm5 432, x .movdqa .xmm6 .xmm3, x .pshufb .xmm6 .xmm5, x .pxor .xmm1 .xmm6, tb .xmm5 448,
  x .pshufb .xmm3 .xmm5, x .pxor .xmm1 .xmm3, tb .xmm5 208, x .pshufb .xmm5 .xmm2, tb .xmm3 176,
  x .pshufb .xmm3 .xmm2, tb .xmm2 224, x .pshufb .xmm2 .xmm0, x .pxor .xmm5 .xmm2, tb .xmm2 192,
  x .pshufb .xmm2 .xmm0, x .pxor .xmm3 .xmm2, tb .xmm0 400, x .movdqa .xmm2 .xmm4, x .pshufb .xmm2 .xmm0,
  x .pxor .xmm1 .xmm2, tb .xmm0 416, x .pshufb .xmm4 .xmm0, x .pxor .xmm1 .xmm4, tb .xmm0 368, x .movdqa .xmm4 .xmm5,
  x .pshufb .xmm4 .xmm0, x .pxor .xmm1 .xmm4, tb .xmm0 384, x .pshufb .xmm5 .xmm0, x .pxor .xmm1 .xmm5,
  ld .xmm0 sb 544, tb .xmm6 304, x .movdqa .xmm2 .xmm3, x .pshufb .xmm2 .xmm6, x .pxor .xmm1 .xmm2, tb .xmm6 320,
  x .movdqa .xmm5 .xmm3, x .pshufb .xmm5 .xmm6, x .pxor .xmm1 .xmm5, tb .xmm6 336, x .movdqa .xmm4 .xmm3,
  x .pshufb .xmm4 .xmm6, x .pxor .xmm1 .xmm4, tb .xmm6 352, x .pshufb .xmm3 .xmm6, x .pxor .xmm1 .xmm3,
  x .aesenclast .xmm0 .xmm7, ld .xmm6 sb 560, x .movdqa .xmm2 .xmm7, x .pand .xmm2 .xmm0, sh .psrld .xmm0 4,
  x .pand .xmm0 .xmm7, tb .xmm3 272, x .pshufb .xmm3 .xmm2, tb .xmm5 288, x .pshufb .xmm5 .xmm0, x .pxor .xmm3 .xmm5,
  tb .xmm4 432, x .movdqa .xmm5 .xmm3, x .pshufb .xmm5 .xmm4, x .pxor .xmm6 .xmm5, tb .xmm4 448,
  x .pshufb .xmm3 .xmm4, x .pxor .xmm6 .xmm3, tb .xmm4 240, x .pshufb .xmm4 .xmm2, tb .xmm3 256,
  x .pshufb .xmm3 .xmm0, x .pxor .xmm4 .xmm3, tb .xmm5 400, x .movdqa .xmm3 .xmm4, x .pshufb .xmm3 .xmm5,
  x .pxor .xmm6 .xmm3, tb .xmm5 416, x .pshufb .xmm4 .xmm5, x .pxor .xmm6 .xmm4, tb .xmm5 208, x .pshufb .xmm5 .xmm2,
  tb .xmm4 224, x .pshufb .xmm4 .xmm0, x .pxor .xmm5 .xmm4, tb .xmm3 176, x .pshufb .xmm3 .xmm2, tb .xmm2 192,
  x .pshufb .xmm2 .xmm0, x .pxor .xmm3 .xmm2, tb .xmm0 368, x .movdqa .xmm2 .xmm5, x .pshufb .xmm2 .xmm0,
  x .pxor .xmm6 .xmm2, tb .xmm0 384, x .pshufb .xmm5 .xmm0, x .pxor .xmm6 .xmm5, tb .xmm0 304, x .movdqa .xmm4 .xmm3,
  x .pshufb .xmm4 .xmm0, x .pxor .xmm6 .xmm4, tb .xmm0 320, x .movdqa .xmm5 .xmm3, x .pshufb .xmm5 .xmm0,
  x .pxor .xmm6 .xmm5, tb .xmm0 336, x .movdqa .xmm2 .xmm3, x .pshufb .xmm2 .xmm0, x .pxor .xmm6 .xmm2, tb .xmm0 352,
  x .pshufb .xmm3 .xmm0, x .pxor .xmm6 .xmm3, stx sb 528 .xmm1, stx sb 560 .xmm6, x .aesenclast .xmm1 .xmm7,
  ld .xmm0 sb 512, lq .xmm3 16, x .punpcklqdq .xmm3 .xmm3, x .pxor .xmm0 .xmm3, x .movdqa .xmm4 .xmm7,
  x .pand .xmm4 .xmm1, sh .psrld .xmm1 4, x .pand .xmm1 .xmm7, tb .xmm5 272, x .pshufb .xmm5 .xmm4, tb .xmm2 288,
  x .pshufb .xmm2 .xmm1, x .pxor .xmm5 .xmm2, tb .xmm3 432, x .movdqa .xmm2 .xmm5, x .pshufb .xmm2 .xmm3,
  x .pxor .xmm0 .xmm2, tb .xmm3 448, x .pshufb .xmm5 .xmm3, x .pxor .xmm0 .xmm5, tb .xmm3 240, x .pshufb .xmm3 .xmm4,
  tb .xmm5 256, x .pshufb .xmm5 .xmm1, x .pxor .xmm3 .xmm5, tb .xmm2 400, x .movdqa .xmm5 .xmm3,
  x .pshufb .xmm5 .xmm2, x .pxor .xmm0 .xmm5, tb .xmm2 416, x .pshufb .xmm3 .xmm2, x .pxor .xmm0 .xmm3, tb .xmm2 176,
  x .pshufb .xmm2 .xmm4, tb .xmm3 208, x .pshufb .xmm3 .xmm4, tb .xmm4 224, x .pshufb .xmm4 .xmm1,
  x .pxor .xmm3 .xmm4, tb .xmm4 192, x .pshufb .xmm4 .xmm1, x .pxor .xmm2 .xmm4, tb .xmm1 368, x .movdqa .xmm4 .xmm3,
  x .pshufb .xmm4 .xmm1, x .pxor .xmm0 .xmm4, tb .xmm1 384, x .pshufb .xmm3 .xmm1, x .pxor .xmm0 .xmm3, tb .xmm1 304,
  x .movdqa .xmm5 .xmm2, x .pshufb .xmm5 .xmm1, x .pxor .xmm0 .xmm5, tb .xmm1 320, x .movdqa .xmm3 .xmm2,
  x .pshufb .xmm3 .xmm1, x .pxor .xmm0 .xmm3, tb .xmm1 336, x .movdqa .xmm5 .xmm2, x .pshufb .xmm5 .xmm1,
  x .pxor .xmm0 .xmm5, tb .xmm1 352, x .pshufb .xmm2 .xmm1, x .pxor .xmm0 .xmm2, x .aesenclast .xmm6 .xmm7,
  ld .xmm1 sb 544, lq .xmm2 16, x .punpcklqdq .xmm2 .xmm2, x .pxor .xmm1 .xmm2, x .movdqa .xmm2 .xmm7,
  x .pand .xmm2 .xmm6, sh .psrld .xmm6 4, x .pand .xmm6 .xmm7, tb .xmm4 272, x .pshufb .xmm4 .xmm2, tb .xmm3 288,
  x .pshufb .xmm3 .xmm6, x .pxor .xmm4 .xmm3, tb .xmm5 432, x .movdqa .xmm3 .xmm4, x .pshufb .xmm3 .xmm5,
  x .pxor .xmm1 .xmm3, tb .xmm5 448, x .pshufb .xmm4 .xmm5, x .pxor .xmm1 .xmm4, tb .xmm5 240, x .pshufb .xmm5 .xmm2,
  tb .xmm4 256, x .pshufb .xmm4 .xmm6, x .pxor .xmm5 .xmm4, tb .xmm3 400, x .movdqa .xmm4 .xmm5,
  x .pshufb .xmm4 .xmm3, x .pxor .xmm1 .xmm4, tb .xmm3 416, x .pshufb .xmm5 .xmm3, x .pxor .xmm1 .xmm5, tb .xmm3 208,
  x .pshufb .xmm3 .xmm2, tb .xmm5 176, x .pshufb .xmm5 .xmm2, tb .xmm2 224, x .pshufb .xmm2 .xmm6,
  x .pxor .xmm3 .xmm2, tb .xmm2 192, x .pshufb .xmm2 .xmm6, x .pxor .xmm5 .xmm2, tb .xmm6 368, x .movdqa .xmm2 .xmm3,
  x .pshufb .xmm2 .xmm6, x .pxor .xmm1 .xmm2, tb .xmm6 384, x .pshufb .xmm3 .xmm6, x .pxor .xmm1 .xmm3, tb .xmm6 304,
  x .movdqa .xmm4 .xmm5, x .pshufb .xmm4 .xmm6, x .pxor .xmm1 .xmm4, tb .xmm6 320, x .movdqa .xmm3 .xmm5,
  x .pshufb .xmm3 .xmm6, x .pxor .xmm1 .xmm3, tb .xmm6 336, x .movdqa .xmm2 .xmm5, x .pshufb .xmm2 .xmm6,
  x .pxor .xmm1 .xmm2, tb .xmm6 352, x .pshufb .xmm5 .xmm6, x .pxor .xmm1 .xmm5, stx sb 512 .xmm0, stx sb 544 .xmm1,
  ld .xmm6 sb 528, x .aesenclast .xmm0 .xmm7, x .movdqa .xmm5 .xmm7, x .pand .xmm5 .xmm0, sh .psrld .xmm0 4,
  x .pand .xmm0 .xmm7, lq .xmm3 24, x .punpcklqdq .xmm3 .xmm3, x .pxor .xmm6 .xmm3, tb .xmm4 272,
  x .pshufb .xmm4 .xmm5, tb .xmm2 288, x .pshufb .xmm2 .xmm0, x .pxor .xmm4 .xmm2, tb .xmm3 432,
  x .movdqa .xmm2 .xmm4, x .pshufb .xmm2 .xmm3, x .pxor .xmm6 .xmm2, tb .xmm3 448, x .pshufb .xmm4 .xmm3,
  x .pxor .xmm6 .xmm4, tb .xmm3 240, x .pshufb .xmm3 .xmm5, tb .xmm4 256, x .pshufb .xmm4 .xmm0, x .pxor .xmm3 .xmm4,
  tb .xmm2 400, x .movdqa .xmm4 .xmm3, x .pshufb .xmm4 .xmm2, x .pxor .xmm6 .xmm4, tb .xmm2 416,
  x .pshufb .xmm3 .xmm2, x .pxor .xmm6 .xmm3, tb .xmm2 176, x .pshufb .xmm2 .xmm5, tb .xmm3 208,
  x .pshufb .xmm3 .xmm5, tb .xmm5 224, x .pshufb .xmm5 .xmm0, x .pxor .xmm3 .xmm5, tb .xmm5 192,
  x .pshufb .xmm5 .xmm0, x .pxor .xmm2 .xmm5, tb .xmm0 368, x .movdqa .xmm5 .xmm3, x .pshufb .xmm5 .xmm0,
  x .pxor .xmm6 .xmm5, tb .xmm0 384, x .pshufb .xmm3 .xmm0, x .pxor .xmm6 .xmm3, tb .xmm0 304, x .movdqa .xmm4 .xmm2,
  x .pshufb .xmm4 .xmm0, x .pxor .xmm6 .xmm4, tb .xmm0 320, x .movdqa .xmm3 .xmm2, x .pshufb .xmm3 .xmm0,
  x .pxor .xmm6 .xmm3, tb .xmm0 336, x .movdqa .xmm4 .xmm2, x .pshufb .xmm4 .xmm0, x .pxor .xmm6 .xmm4, tb .xmm0 352,
  x .pshufb .xmm2 .xmm0, x .pxor .xmm6 .xmm2, x .aesenclast .xmm1 .xmm7, ld .xmm0 sb 560, x .movdqa .xmm2 .xmm7,
  x .pand .xmm2 .xmm1, sh .psrld .xmm1 4, x .pand .xmm1 .xmm7, lq .xmm5 24, x .punpcklqdq .xmm5 .xmm5,
  x .pxor .xmm0 .xmm5, tb .xmm3 272, x .pshufb .xmm3 .xmm2, tb .xmm4 288, x .pshufb .xmm4 .xmm1, x .pxor .xmm3 .xmm4,
  tb .xmm5 432, x .movdqa .xmm4 .xmm3, x .pshufb .xmm4 .xmm5, x .pxor .xmm0 .xmm4, tb .xmm5 448,
  x .pshufb .xmm3 .xmm5, x .pxor .xmm0 .xmm3, tb .xmm5 240, x .pshufb .xmm5 .xmm2, tb .xmm3 256,
  x .pshufb .xmm3 .xmm1, x .pxor .xmm5 .xmm3, tb .xmm4 400, x .movdqa .xmm3 .xmm5, x .pshufb .xmm3 .xmm4,
  x .pxor .xmm0 .xmm3, tb .xmm4 416, x .pshufb .xmm5 .xmm4, x .pxor .xmm0 .xmm5, tb .xmm4 208, x .pshufb .xmm4 .xmm2,
  tb .xmm5 224, x .pshufb .xmm5 .xmm1, x .pxor .xmm4 .xmm5, tb .xmm3 176, x .pshufb .xmm3 .xmm2, tb .xmm2 192,
  x .pshufb .xmm2 .xmm1, x .pxor .xmm3 .xmm2, tb .xmm1 368, x .movdqa .xmm2 .xmm4, x .pshufb .xmm2 .xmm1,
  x .pxor .xmm0 .xmm2, tb .xmm1 384, x .pshufb .xmm4 .xmm1, x .pxor .xmm0 .xmm4, tb .xmm1 304, x .movdqa .xmm5 .xmm3,
  x .pshufb .xmm5 .xmm1, x .pxor .xmm0 .xmm5, tb .xmm1 320, x .movdqa .xmm4 .xmm3, x .pshufb .xmm4 .xmm1,
  x .pxor .xmm0 .xmm4, tb .xmm1 336, x .movdqa .xmm2 .xmm3, x .pshufb .xmm2 .xmm1, x .pxor .xmm0 .xmm2, tb .xmm1 352,
  x .pshufb .xmm3 .xmm1, x .pxor .xmm0 .xmm3, stx sb 528 .xmm6, stx sb 560 .xmm0, x .aesenclast .xmm6 .xmm7,
  ld .xmm1 sb 512, lq .xmm3 32, x .punpcklqdq .xmm3 .xmm3, x .pxor .xmm1 .xmm3, x .movdqa .xmm4 .xmm7,
  x .pand .xmm4 .xmm6, sh .psrld .xmm6 4, x .pand .xmm6 .xmm7, tb .xmm5 272, x .pshufb .xmm5 .xmm4, tb .xmm2 288,
  x .pshufb .xmm2 .xmm6, x .pxor .xmm5 .xmm2, tb .xmm3 432, x .movdqa .xmm2 .xmm5, x .pshufb .xmm2 .xmm3,
  x .pxor .xmm1 .xmm2, tb .xmm3 448, x .pshufb .xmm5 .xmm3, x .pxor .xmm1 .xmm5, tb .xmm3 240, x .pshufb .xmm3 .xmm4,
  tb .xmm5 256, x .pshufb .xmm5 .xmm6, x .pxor .xmm3 .xmm5, tb .xmm2 400, x .movdqa .xmm5 .xmm3,
  x .pshufb .xmm5 .xmm2, x .pxor .xmm1 .xmm5, tb .xmm2 416, x .pshufb .xmm3 .xmm2, x .pxor .xmm1 .xmm3, tb .xmm2 208,
  x .pshufb .xmm2 .xmm4, tb .xmm3 224, x .pshufb .xmm3 .xmm6, x .pxor .xmm2 .xmm3, tb .xmm5 176,
  x .pshufb .xmm5 .xmm4, tb .xmm4 192, x .pshufb .xmm4 .xmm6, x .pxor .xmm5 .xmm4, tb .xmm6 368,
  x .movdqa .xmm4 .xmm2, x .pshufb .xmm4 .xmm6, x .pxor .xmm1 .xmm4, tb .xmm6 384, x .pshufb .xmm2 .xmm6,
  x .pxor .xmm1 .xmm2, tb .xmm6 304, x .movdqa .xmm3 .xmm5, x .pshufb .xmm3 .xmm6, x .pxor .xmm1 .xmm3, tb .xmm6 320,
  x .movdqa .xmm2 .xmm5, x .pshufb .xmm2 .xmm6, x .pxor .xmm1 .xmm2, tb .xmm6 336, x .movdqa .xmm4 .xmm5,
  x .pshufb .xmm4 .xmm6, x .pxor .xmm1 .xmm4, tb .xmm6 352, x .pshufb .xmm5 .xmm6, x .pxor .xmm1 .xmm5,
  x .aesenclast .xmm0 .xmm7, ld .xmm6 sb 544, x .movdqa .xmm5 .xmm7, x .pand .xmm5 .xmm0, sh .psrld .xmm0 4,
  x .pand .xmm0 .xmm7, lq .xmm2 32, x .punpcklqdq .xmm2 .xmm2, x .pxor .xmm6 .xmm2, tb .xmm3 272,
  x .pshufb .xmm3 .xmm5, tb .xmm4 288, x .pshufb .xmm4 .xmm0, x .pxor .xmm3 .xmm4, tb .xmm2 432,
  x .movdqa .xmm4 .xmm3, x .pshufb .xmm4 .xmm2, x .pxor .xmm6 .xmm4, tb .xmm2 448, x .pshufb .xmm3 .xmm2,
  x .pxor .xmm6 .xmm3, tb .xmm2 240, x .pshufb .xmm2 .xmm5, tb .xmm3 256, x .pshufb .xmm3 .xmm0, x .pxor .xmm2 .xmm3,
  tb .xmm4 400, x .movdqa .xmm3 .xmm2, x .pshufb .xmm3 .xmm4, x .pxor .xmm6 .xmm3, tb .xmm4 416,
  x .pshufb .xmm2 .xmm4, x .pxor .xmm6 .xmm2, tb .xmm4 208, x .pshufb .xmm4 .xmm5, tb .xmm2 224,
  x .pshufb .xmm2 .xmm0, x .pxor .xmm4 .xmm2, tb .xmm3 176, x .pshufb .xmm3 .xmm5, tb .xmm5 192,
  x .pshufb .xmm5 .xmm0, x .pxor .xmm3 .xmm5, tb .xmm0 368, x .movdqa .xmm5 .xmm4, x .pshufb .xmm5 .xmm0,
  x .pxor .xmm6 .xmm5, tb .xmm0 384, x .pshufb .xmm4 .xmm0, x .pxor .xmm6 .xmm4, tb .xmm0 304, x .movdqa .xmm2 .xmm3,
  x .pshufb .xmm2 .xmm0, x .pxor .xmm6 .xmm2, tb .xmm0 320, x .movdqa .xmm4 .xmm3, x .pshufb .xmm4 .xmm0,
  x .pxor .xmm6 .xmm4, tb .xmm0 336, x .movdqa .xmm5 .xmm3, x .pshufb .xmm5 .xmm0, x .pxor .xmm6 .xmm5, tb .xmm0 352,
  x .pshufb .xmm3 .xmm0, x .pxor .xmm6 .xmm3, stx sb 512 .xmm1, stx sb 544 .xmm6, x .aesenclast .xmm1 .xmm7,
  ld .xmm0 sb 528, lq .xmm3 40, x .punpcklqdq .xmm3 .xmm3, x .pxor .xmm0 .xmm3, x .movdqa .xmm2 .xmm7,
  x .pand .xmm2 .xmm1, sh .psrld .xmm1 4, x .pand .xmm1 .xmm7, tb .xmm4 272, x .pshufb .xmm4 .xmm2, tb .xmm3 288,
  x .pshufb .xmm3 .xmm1, x .pxor .xmm4 .xmm3, tb .xmm5 432, x .movdqa .xmm3 .xmm4, x .pshufb .xmm3 .xmm5,
  x .pxor .xmm0 .xmm3, tb .xmm5 448, x .pshufb .xmm4 .xmm5, x .pxor .xmm0 .xmm4, tb .xmm5 240, x .pshufb .xmm5 .xmm2,
  tb .xmm4 256, x .pshufb .xmm4 .xmm1, x .pxor .xmm5 .xmm4, tb .xmm3 400, x .movdqa .xmm4 .xmm5,
  x .pshufb .xmm4 .xmm3, x .pxor .xmm0 .xmm4, tb .xmm3 416, x .pshufb .xmm5 .xmm3, x .pxor .xmm0 .xmm5, tb .xmm3 208,
  x .pshufb .xmm3 .xmm2, tb .xmm5 224, x .pshufb .xmm5 .xmm1, x .pxor .xmm3 .xmm5, tb .xmm4 176,
  x .pshufb .xmm4 .xmm2, tb .xmm2 192, x .pshufb .xmm2 .xmm1, x .pxor .xmm4 .xmm2, tb .xmm1 368,
  x .movdqa .xmm2 .xmm3, x .pshufb .xmm2 .xmm1, x .pxor .xmm0 .xmm2, tb .xmm1 384, x .pshufb .xmm3 .xmm1,
  x .pxor .xmm0 .xmm3, tb .xmm1 304, x .movdqa .xmm5 .xmm4, x .pshufb .xmm5 .xmm1, x .pxor .xmm0 .xmm5, tb .xmm1 320,
  x .movdqa .xmm3 .xmm4, x .pshufb .xmm3 .xmm1, x .pxor .xmm0 .xmm3, tb .xmm1 336, x .movdqa .xmm2 .xmm4,
  x .pshufb .xmm2 .xmm1, x .pxor .xmm0 .xmm2, tb .xmm1 352, x .pshufb .xmm4 .xmm1, x .pxor .xmm0 .xmm4,
  x .aesenclast .xmm6 .xmm7, ld .xmm1 sb 560, lq .xmm4 40, x .punpcklqdq .xmm4 .xmm4, x .pxor .xmm1 .xmm4,
  x .movdqa .xmm3 .xmm7, x .pand .xmm3 .xmm6, sh .psrld .xmm6 4, x .pand .xmm6 .xmm7, tb .xmm5 272,
  x .pshufb .xmm5 .xmm3, tb .xmm2 288, x .pshufb .xmm2 .xmm6, x .pxor .xmm5 .xmm2, tb .xmm4 432,
  x .movdqa .xmm2 .xmm5, x .pshufb .xmm2 .xmm4, x .pxor .xmm1 .xmm2, tb .xmm4 448, x .pshufb .xmm5 .xmm4,
  x .pxor .xmm1 .xmm5, tb .xmm4 240, x .pshufb .xmm4 .xmm3, tb .xmm5 256, x .pshufb .xmm5 .xmm6, x .pxor .xmm4 .xmm5,
  tb .xmm2 400, x .movdqa .xmm5 .xmm4, x .pshufb .xmm5 .xmm2, x .pxor .xmm1 .xmm5, tb .xmm2 416,
  x .pshufb .xmm4 .xmm2, x .pxor .xmm1 .xmm4, tb .xmm2 208, x .pshufb .xmm2 .xmm3, tb .xmm4 224,
  x .pshufb .xmm4 .xmm6, x .pxor .xmm2 .xmm4, tb .xmm5 176, x .pshufb .xmm5 .xmm3, tb .xmm3 192,
  x .pshufb .xmm3 .xmm6, x .pxor .xmm5 .xmm3, tb .xmm6 368, x .movdqa .xmm3 .xmm2, x .pshufb .xmm3 .xmm6,
  x .pxor .xmm1 .xmm3, tb .xmm6 384, x .pshufb .xmm2 .xmm6, x .pxor .xmm1 .xmm2, tb .xmm6 304, x .movdqa .xmm4 .xmm5,
  x .pshufb .xmm4 .xmm6, x .pxor .xmm1 .xmm4, tb .xmm6 320, x .movdqa .xmm2 .xmm5, x .pshufb .xmm2 .xmm6,
  x .pxor .xmm1 .xmm2, tb .xmm6 336, x .movdqa .xmm3 .xmm5, x .pshufb .xmm3 .xmm6, x .pxor .xmm1 .xmm3, tb .xmm6 352,
  x .pshufb .xmm5 .xmm6, x .pxor .xmm1 .xmm5, stx sb 528 .xmm0, stx sb 560 .xmm1, ld .xmm6 sb 512,
  x .aesenclast .xmm0 .xmm7, x .movdqa .xmm5 .xmm7, x .pand .xmm5 .xmm0, sh .psrld .xmm0 4, x .pand .xmm0 .xmm7,
  tb .xmm2 272, x .pshufb .xmm2 .xmm5, lq .xmm4 48, x .punpcklqdq .xmm4 .xmm4, x .pxor .xmm6 .xmm4, tb .xmm3 288,
  x .pshufb .xmm3 .xmm0, x .pxor .xmm2 .xmm3, tb .xmm4 432, x .movdqa .xmm3 .xmm2, x .pshufb .xmm3 .xmm4,
  x .pxor .xmm6 .xmm3, tb .xmm4 448, x .pshufb .xmm2 .xmm4, x .pxor .xmm6 .xmm2, tb .xmm4 240, x .pshufb .xmm4 .xmm5,
  tb .xmm2 256, x .pshufb .xmm2 .xmm0, x .pxor .xmm4 .xmm2, tb .xmm3 400, x .movdqa .xmm2 .xmm4,
  x .pshufb .xmm2 .xmm3, x .pxor .xmm6 .xmm2, tb .xmm3 416, x .pshufb .xmm4 .xmm3, x .pxor .xmm6 .xmm4, tb .xmm3 176,
  x .pshufb .xmm3 .xmm5, tb .xmm4 208, x .pshufb .xmm4 .xmm5, tb .xmm5 224, x .pshufb .xmm5 .xmm0,
  x .pxor .xmm4 .xmm5, tb .xmm5 192, x .pshufb .xmm5 .xmm0, x .pxor .xmm3 .xmm5, tb .xmm0 368, x .movdqa .xmm5 .xmm4,
  x .pshufb .xmm5 .xmm0, x .pxor .xmm6 .xmm5, tb .xmm0 384, x .pshufb .xmm4 .xmm0, x .pxor .xmm6 .xmm4, tb .xmm0 304,
  x .movdqa .xmm2 .xmm3, x .pshufb .xmm2 .xmm0, x .pxor .xmm6 .xmm2, tb .xmm0 320, x .movdqa .xmm2 .xmm3,
  x .pshufb .xmm2 .xmm0, x .pxor .xmm6 .xmm2, tb .xmm0 336, x .movdqa .xmm4 .xmm3, x .pshufb .xmm4 .xmm0,
  x .pxor .xmm6 .xmm4, tb .xmm0 352, x .pshufb .xmm3 .xmm0, x .pxor .xmm6 .xmm3, x .aesenclast .xmm1 .xmm7,
  ld .xmm0 sb 544, x .movdqa .xmm3 .xmm7, x .pand .xmm3 .xmm1, sh .psrld .xmm1 4, x .pand .xmm1 .xmm7, lq .xmm5 48,
  x .punpcklqdq .xmm5 .xmm5, x .pxor .xmm0 .xmm5, tb .xmm2 272, x .pshufb .xmm2 .xmm3, tb .xmm4 288,
  x .pshufb .xmm4 .xmm1, x .pxor .xmm2 .xmm4, tb .xmm5 432, x .movdqa .xmm4 .xmm2, x .pshufb .xmm4 .xmm5,
  x .pxor .xmm0 .xmm4, tb .xmm5 448, x .pshufb .xmm2 .xmm5, x .pxor .xmm0 .xmm2, tb .xmm5 240, x .pshufb .xmm5 .xmm3,
  tb .xmm2 256, x .pshufb .xmm2 .xmm1, x .pxor .xmm5 .xmm2, tb .xmm4 400, x .movdqa .xmm2 .xmm5,
  x .pshufb .xmm2 .xmm4, x .pxor .xmm0 .xmm2, tb .xmm4 416, x .pshufb .xmm5 .xmm4, x .pxor .xmm0 .xmm5, tb .xmm4 208,
  x .pshufb .xmm4 .xmm3, tb .xmm5 224, x .pshufb .xmm5 .xmm1, x .pxor .xmm4 .xmm5, tb .xmm2 176,
  x .pshufb .xmm2 .xmm3, tb .xmm3 192, x .pshufb .xmm3 .xmm1, x .pxor .xmm2 .xmm3, tb .xmm1 368,
  x .movdqa .xmm3 .xmm4, x .pshufb .xmm3 .xmm1, x .pxor .xmm0 .xmm3, tb .xmm1 384, x .pshufb .xmm4 .xmm1,
  x .pxor .xmm0 .xmm4, tb .xmm1 304, x .movdqa .xmm5 .xmm2, x .pshufb .xmm5 .xmm1, x .pxor .xmm0 .xmm5, tb .xmm1 320,
  x .movdqa .xmm4 .xmm2, x .pshufb .xmm4 .xmm1, x .pxor .xmm0 .xmm4, tb .xmm1 336, x .movdqa .xmm3 .xmm2,
  x .pshufb .xmm3 .xmm1, x .pxor .xmm0 .xmm3, tb .xmm1 352, x .pshufb .xmm2 .xmm1, x .pxor .xmm0 .xmm2,
  stx sb 512 .xmm6, stx sb 544 .xmm0]

/-- The FL layer after a group on both pairs, to the next group's form: `refLayer`, scheduled. -/
def wLayer : List Instr := [
  ld .xmm0 sb 512, x .movdqa .xmm1 .xmm7, x .pand .xmm1 .xmm0, sh .psrld .xmm0 4, x .pand .xmm0 .xmm7, tb .xmm2 112,
  x .pshufb .xmm2 .xmm1, tb .xmm3 32, x .pand .xmm1 .xmm3, x .pand .xmm3 .xmm0, tb .xmm4 128, x .pshufb .xmm4 .xmm0,
  x .pxor .xmm2 .xmm4, tb .xmm5 144, x .pshufb .xmm5 .xmm1, x .pxor .xmm2 .xmm5, tb .xmm6 160, x .pshufb .xmm6 .xmm3,
  x .pxor .xmm2 .xmm6, lq .xmm0 64, x .punpcklqdq .xmm0 .xmm0, x .pand .xmm0 .xmm2, sh .psrld .xmm0 31, lq .xmm1 64,
  x .punpcklqdq .xmm1 .xmm1, x .pand .xmm1 .xmm2, sh .psrlq .xmm1 32, lq .xmm3 64, x .punpcklqdq .xmm3 .xmm3,
  x .pand .xmm3 .xmm2, sh .pslld .xmm3 1, x .por .xmm3 .xmm0, sh .psllq .xmm3 32, x .pxor .xmm2 .xmm3,
  x .pxor .xmm2 .xmm1, lq .xmm4 96, x .punpcklqdq .xmm4 .xmm4, x .pxor .xmm2 .xmm4, ld .xmm5 sb 560, lq .xmm6 56,
  x .punpcklqdq .xmm6 .xmm6, x .pxor .xmm5 .xmm6, x .movdqa .xmm4 .xmm7, x .pand .xmm4 .xmm5, sh .psrld .xmm5 4,
  x .pand .xmm5 .xmm7, tb .xmm6 112, x .pshufb .xmm6 .xmm4, tb .xmm0 32, x .pand .xmm4 .xmm0, x .pand .xmm0 .xmm5,
  tb .xmm1 128, x .pshufb .xmm1 .xmm5, x .pxor .xmm6 .xmm1, tb .xmm5 144, x .pshufb .xmm5 .xmm4, x .pxor .xmm6 .xmm5,
  tb .xmm1 160, x .pshufb .xmm1 .xmm0, x .pxor .xmm6 .xmm1, lq .xmm0 80, x .punpcklqdq .xmm0 .xmm0,
  x .pand .xmm0 .xmm2, sh .psrld .xmm0 31, lq .xmm3 80, x .punpcklqdq .xmm3 .xmm3, x .pand .xmm3 .xmm2,
  sh .psrlq .xmm3 32, lq .xmm4 80, x .punpcklqdq .xmm4 .xmm4, x .pand .xmm4 .xmm2, sh .pslld .xmm4 1,
  x .por .xmm4 .xmm0, sh .psllq .xmm4 32, x .pxor .xmm2 .xmm4, x .pxor .xmm2 .xmm3, x .movdqa .xmm5 .xmm7,
  x .pand .xmm5 .xmm2, sh .psrld .xmm2 4, x .pand .xmm2 .xmm7, lq .xmm1 72, x .punpcklqdq .xmm1 .xmm1,
  x .pand .xmm1 .xmm6, sh .psrld .xmm1 31, lq .xmm0 72, x .punpcklqdq .xmm0 .xmm0, x .pand .xmm0 .xmm6,
  sh .psrlq .xmm0 32, lq .xmm3 72, x .punpcklqdq .xmm3 .xmm3, x .pand .xmm3 .xmm6, sh .pslld .xmm3 1,
  x .por .xmm3 .xmm1, sh .psllq .xmm3 32, x .pxor .xmm6 .xmm3, x .pxor .xmm6 .xmm0, tb .xmm1 48,
  x .pshufb .xmm1 .xmm5, tb .xmm4 32, x .pand .xmm5 .xmm4, x .pand .xmm4 .xmm2, tb .xmm0 64, x .pshufb .xmm0 .xmm2,
  x .pxor .xmm1 .xmm0, lq .xmm2 104, x .punpcklqdq .xmm2 .xmm2, x .pxor .xmm6 .xmm2, tb .xmm3 80,
  x .pshufb .xmm3 .xmm5, x .pxor .xmm1 .xmm3, tb .xmm5 96, x .pshufb .xmm5 .xmm4, x .pxor .xmm1 .xmm5,
  ld .xmm0 sb 528, lq .xmm4 112, x .punpcklqdq .xmm4 .xmm4, x .pxor .xmm1 .xmm4, stx sb 512 .xmm1, lq .xmm2 56,
  x .punpcklqdq .xmm2 .xmm2, x .pxor .xmm0 .xmm2, lq .xmm3 88, x .punpcklqdq .xmm3 .xmm3, x .pand .xmm3 .xmm6,
  sh .psrld .xmm3 31, lq .xmm5 88, x .punpcklqdq .xmm5 .xmm5, x .pand .xmm5 .xmm6, sh .psrlq .xmm5 32, lq .xmm4 88,
  x .punpcklqdq .xmm4 .xmm4, x .pand .xmm4 .xmm6, sh .pslld .xmm4 1, x .por .xmm4 .xmm3, sh .psllq .xmm4 32,
  x .pxor .xmm6 .xmm4, x .pxor .xmm6 .xmm5, x .movdqa .xmm2 .xmm7, x .pand .xmm2 .xmm0, sh .psrld .xmm0 4,
  x .pand .xmm0 .xmm7, tb .xmm1 112, x .pshufb .xmm1 .xmm2, tb .xmm3 32, x .pand .xmm2 .xmm3, x .pand .xmm3 .xmm0,
  tb .xmm5 128, x .pshufb .xmm5 .xmm0, x .pxor .xmm1 .xmm5, tb .xmm0 144, x .pshufb .xmm0 .xmm2, x .pxor .xmm1 .xmm0,
  tb .xmm2 160, x .pshufb .xmm2 .xmm3, x .pxor .xmm1 .xmm2, lq .xmm3 72, x .punpcklqdq .xmm3 .xmm3,
  x .pand .xmm3 .xmm1, sh .psrld .xmm3 31, lq .xmm5 72, x .punpcklqdq .xmm5 .xmm5, x .pand .xmm5 .xmm1,
  sh .psrlq .xmm5 32, x .movdqa .xmm0 .xmm7, x .pand .xmm0 .xmm6, sh .psrld .xmm6 4, x .pand .xmm6 .xmm7,
  lq .xmm4 72, x .punpcklqdq .xmm4 .xmm4, x .pand .xmm4 .xmm1, sh .pslld .xmm4 1, x .por .xmm4 .xmm3,
  sh .psllq .xmm4 32, x .pxor .xmm1 .xmm4, x .pxor .xmm1 .xmm5, tb .xmm2 48, x .pshufb .xmm2 .xmm0, tb .xmm3 32,
  x .pand .xmm0 .xmm3, x .pand .xmm3 .xmm6, tb .xmm5 64, x .pshufb .xmm5 .xmm6, x .pxor .xmm2 .xmm5, tb .xmm6 80,
  x .pshufb .xmm6 .xmm0, x .pxor .xmm2 .xmm6, tb .xmm0 96, x .pshufb .xmm0 .xmm3, x .pxor .xmm2 .xmm0,
  ld .xmm3 sb 544, lq .xmm4 104, x .punpcklqdq .xmm4 .xmm4, x .pxor .xmm1 .xmm4, lq .xmm5 88,
  x .punpcklqdq .xmm5 .xmm5, x .pand .xmm5 .xmm1, sh .psrld .xmm5 31, lq .xmm6 120, x .punpcklqdq .xmm6 .xmm6,
  x .pxor .xmm2 .xmm6, stx sb 560 .xmm2, x .movdqa .xmm0 .xmm7, x .pand .xmm0 .xmm3, sh .psrld .xmm3 4,
  x .pand .xmm3 .xmm7, tb .xmm4 112, x .pshufb .xmm4 .xmm0, tb .xmm6 32, x .pand .xmm0 .xmm6, x .pand .xmm6 .xmm3,
  tb .xmm2 128, x .pshufb .xmm2 .xmm3, x .pxor .xmm4 .xmm2, tb .xmm3 144, x .pshufb .xmm3 .xmm0, x .pxor .xmm4 .xmm3,
  lq .xmm0 88, x .punpcklqdq .xmm0 .xmm0, x .pand .xmm0 .xmm1, sh .psrlq .xmm0 32, tb .xmm2 160,
  x .pshufb .xmm2 .xmm6, x .pxor .xmm4 .xmm2, lq .xmm6 88, x .punpcklqdq .xmm6 .xmm6, x .pand .xmm6 .xmm1,
  sh .pslld .xmm6 1, x .por .xmm6 .xmm5, sh .psllq .xmm6 32, x .pxor .xmm1 .xmm6, x .pxor .xmm1 .xmm0, lq .xmm5 64,
  x .punpcklqdq .xmm5 .xmm5, x .pand .xmm5 .xmm4, sh .psrld .xmm5 31, lq .xmm3 64, x .punpcklqdq .xmm3 .xmm3,
  x .pand .xmm3 .xmm4, sh .psrlq .xmm3 32, lq .xmm2 64, x .punpcklqdq .xmm2 .xmm2, x .pand .xmm2 .xmm4,
  sh .pslld .xmm2 1, x .por .xmm2 .xmm5, sh .psllq .xmm2 32, x .movdqa .xmm0 .xmm7, x .pand .xmm0 .xmm1,
  sh .psrld .xmm1 4, x .pand .xmm1 .xmm7, x .pxor .xmm4 .xmm2, x .pxor .xmm4 .xmm3, tb .xmm3 48,
  x .pshufb .xmm3 .xmm0, lq .xmm5 96, x .punpcklqdq .xmm5 .xmm5, x .pxor .xmm4 .xmm5, tb .xmm6 32,
  x .pand .xmm0 .xmm6, x .pand .xmm6 .xmm1, tb .xmm5 64, x .pshufb .xmm5 .xmm1, x .pxor .xmm3 .xmm5, tb .xmm2 80,
  x .pshufb .xmm2 .xmm0, x .pxor .xmm3 .xmm2, tb .xmm0 96, x .pshufb .xmm0 .xmm6, x .pxor .xmm3 .xmm0, lq .xmm1 120,
  x .punpcklqdq .xmm1 .xmm1, x .pxor .xmm3 .xmm1, stx sb 528 .xmm3, lq .xmm2 80, x .punpcklqdq .xmm2 .xmm2,
  x .pand .xmm2 .xmm4, sh .psrld .xmm2 31, lq .xmm5 80, x .punpcklqdq .xmm5 .xmm5, x .pand .xmm5 .xmm4,
  sh .psrlq .xmm5 32, lq .xmm6 80, x .punpcklqdq .xmm6 .xmm6, x .pand .xmm6 .xmm4, sh .pslld .xmm6 1,
  x .por .xmm6 .xmm2, sh .psllq .xmm6 32, x .pxor .xmm4 .xmm6, x .pxor .xmm4 .xmm5, x .movdqa .xmm0 .xmm7,
  x .pand .xmm0 .xmm4, sh .psrld .xmm4 4, x .pand .xmm4 .xmm7, tb .xmm1 48, x .pshufb .xmm1 .xmm0, tb .xmm2 32,
  x .pand .xmm0 .xmm2, x .pand .xmm2 .xmm4, tb .xmm3 64, x .pshufb .xmm3 .xmm4, x .pxor .xmm1 .xmm3, tb .xmm5 80,
  x .pshufb .xmm5 .xmm0, x .pxor .xmm1 .xmm5, tb .xmm6 96, x .pshufb .xmm6 .xmm2, x .pxor .xmm1 .xmm6, lq .xmm0 112,
  x .punpcklqdq .xmm0 .xmm0, x .pxor .xmm1 .xmm0, stx sb 544 .xmm1]

/-- The pairs' halves after the last round to the four blocks of the buffer: `refOut`, scheduled. -/
def wOut : List Instr := [
  ld .xmm0 sb 512, x .movdqa .xmm1 .xmm7, x .pand .xmm1 .xmm0, sh .psrld .xmm0 4, x .pand .xmm0 .xmm7, tb .xmm2 112,
  x .pshufb .xmm2 .xmm1, tb .xmm3 32, x .pand .xmm1 .xmm3, x .pand .xmm3 .xmm0, tb .xmm4 128, x .pshufb .xmm4 .xmm0,
  x .pxor .xmm2 .xmm4, tb .xmm5 144, x .pshufb .xmm5 .xmm1, x .pxor .xmm2 .xmm5, tb .xmm6 160, x .pshufb .xmm6 .xmm3,
  x .pxor .xmm2 .xmm6, ld .xmm0 sb 528, lq .xmm1 56, x .punpcklqdq .xmm1 .xmm1, x .pxor .xmm0 .xmm1, ld .xmm3 sb 544,
  x .movdqa .xmm4 .xmm7, x .pand .xmm4 .xmm0, sh .psrld .xmm0 4, x .pand .xmm0 .xmm7, tb .xmm5 112,
  x .pshufb .xmm5 .xmm4, tb .xmm1 32, x .pand .xmm4 .xmm1, x .pand .xmm1 .xmm0, tb .xmm6 128, x .pshufb .xmm6 .xmm0,
  x .pxor .xmm5 .xmm6, tb .xmm0 144, x .pshufb .xmm0 .xmm4, x .pxor .xmm5 .xmm0, tb .xmm4 160, x .pshufb .xmm4 .xmm1,
  x .pxor .xmm5 .xmm4, x .movdqa .xmm1 .xmm7, x .pand .xmm1 .xmm3, sh .psrld .xmm3 4, x .pand .xmm3 .xmm7,
  tb .xmm6 112, x .pshufb .xmm6 .xmm1, tb .xmm0 32, x .pand .xmm1 .xmm0, x .pand .xmm0 .xmm3, tb .xmm4 128,
  x .pshufb .xmm4 .xmm3, x .pxor .xmm6 .xmm4, tb .xmm3 144, x .pshufb .xmm3 .xmm1, x .pxor .xmm6 .xmm3, tb .xmm1 160,
  x .pshufb .xmm1 .xmm0, x .pxor .xmm6 .xmm1, ld .xmm0 sb 560, x .movdqa .xmm4 .xmm5, x .punpcklqdq .xmm4 .xmm2,
  x .punpckhqdq .xmm5 .xmm2, lq .xmm2 56, x .punpcklqdq .xmm2 .xmm2, x .pxor .xmm0 .xmm2, tb .xmm2 16,
  x .pshufb .xmm4 .xmm2, x .pshufb .xmm5 .xmm2, ld .xmm2 kr 64, x .pxor .xmm4 .xmm2, x .pxor .xmm5 .xmm2,
  stx sb 576 .xmm4, stx sb 592 .xmm5, x .movdqa .xmm2 .xmm7, x .pand .xmm2 .xmm0, sh .psrld .xmm0 4,
  x .pand .xmm0 .xmm7, tb .xmm3 112, x .pshufb .xmm3 .xmm2, tb .xmm1 32, x .pand .xmm2 .xmm1, x .pand .xmm1 .xmm0,
  tb .xmm5 128, x .pshufb .xmm5 .xmm0, x .pxor .xmm3 .xmm5, tb .xmm0 144, x .pshufb .xmm0 .xmm2, x .pxor .xmm3 .xmm0,
  tb .xmm2 160, x .pshufb .xmm2 .xmm1, x .pxor .xmm3 .xmm2, x .movdqa .xmm4 .xmm3, x .punpcklqdq .xmm4 .xmm6,
  x .punpckhqdq .xmm3 .xmm6, tb .xmm6 16, x .pshufb .xmm4 .xmm6, x .pshufb .xmm3 .xmm6, ld .xmm6 kr 64,
  x .pxor .xmm4 .xmm6, x .pxor .xmm3 .xmm6, stx sb 608 .xmm4, stx sb 624 .xmm3]

/-! ## The block function -/

/-- The table's address, the groups left and the keys' pointer
(`AesNi.setup`), the mask, and the blocks to the places. -/
def cryptHead : List Instr := [.mov tbr (.mem (at_ sb 0))] ++ AesNi.setup ++ [tb m0 wM0] ++ wIn

/-- The six rounds of a group, and one group fewer left (ZF set when none
is). -/
def rounds : List Instr := wGroup ++ [.alu .sub .ecx (.imm 1)]

/-- The FL layer after a group, on to the next group's keys. -/
def layer : List Instr := wLayer ++ [.alu .add kr (.imm 112), .alu .test .ecx (.reg .ecx)]

/-- The four blocks of the core's buffer, enciphered in place. -/
def crypt : Prog isa :=
  .seq (.block cryptHead) (.seq
    (.loop (.seq (.block rounds) (.ite .e (.block []) (.block layer))) .ne) (.block wOut))

/-! ## The keys -/

/-- The 16 bytes at `16 src` of the schedule (at `eax`) to those at
`16 dst` of its copy in the scratch buffer, the two words exchanged when
`sw`. -/
def copyUnit (src dst : Nat) (sw : Bool) : List Instr :=
  [ld .xmm0 .eax (16 * src)] ++ (if sw then [.xop (.pshufd .xmm0 .xmm0 0x4e)] else []) ++
    [stx sb (544 + 16 * dst) .xmm0]

/-- The schedule's 34 words, copied. -/
def copyEnc : List Instr := (List.range 17).flatMap fun u => copyUnit u u false

/-- The `8 g + 2` subkeys of `g` groups of rounds, copied in decryption's
order: the first and last pairs exchanged, the words between in reverse. -/
def copyDec (g : Nat) : List Instr :=
  (List.range (4 * g + 1)).flatMap fun u => copyUnit (4 * g - u) u (decide (0 < u ∧ u < 4 * g))

/-- The schedule (at `eax`) to its copy, in `d`'s order for the number of
groups in `ecx`. -/
def prepCopy : Dir → Prog isa
  | .encrypt => .block copyEnc
  | .decrypt => .seq (.block [.alu .cmp .ecx (.imm 3)]) (.ite .e (.block (copyDec 3)) (.block (copyDec 4)))

/-- This file's table's address (in `esi`) to the scratch buffer's first
slot, `AesNi.table`'s to its register, the schedule's pointer, the groups
and the keys' pointer. -/
def prepHead : List Instr :=
  [.store (at_ sb 0) kr, .mov tbr (.reg .eax), .mov .eax (.mem (argOp 0))] ++ AesNi.setup

/-- The schedule's pointer to the copy, the mask, and the copy's first two
subkeys in the rounds' form (`AesNi.prepHeadX`). -/
def prepStart : List Instr := [.mov .eax (.reg sb), .alu .add .eax (.imm 544)] ++ AesNi.prepHeadX

/-- The keys the rounds read, in `d`'s order, from the schedule and the
number of rounds in the first two stack arguments: this file's table's
address to the scratch buffer's first slot, and `AesNi.prepare`'s keys of
the schedule's copy. Both tables' addresses are taken before anything is
stored. -/
def prepare (d : Dir) : Prog isa :=
  .seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1)) (.seq (.block [.mov kr (.reg .eax)]) (.seq
    (.frame (.symPush .eax AesNi.tableName) (.block []) (.pop .ecx 1)) (.seq (.block prepHead) (.seq (prepCopy d)
    (.seq (.block prepStart) (.seq
      (.loop (.seq (.block AesNi.prepGroup) (.ite .e (.block []) (.block AesNi.prepMasks))) .ne)
      (.block AesNi.prepTail)))))))

/-- The slots of the scratch buffer the core uses: the table's address and
five spare slots, 480 bytes for the keys and two spare slots, the four
places and the four blocks, and from byte 544 on, while `prepare` runs,
the schedule's 272 bytes. -/
def slots : Nat := 204

/-- The modes' core: four blocks at a time, in the direction `d`. -/
def core (d : Dir) : Core :=
  { prepare := prepare d, crypt := crypt, slots := slots, total := slots + 10, buf := 144, G := 4, bw := 4,
    stack := 4, ka := 2 }

/-- The sizes of the groups of blocks a wide mode takes in turn, before the
blocks left one at a time. -/
def levels : List Nat := [4, 2]

/-- `vg_camellia_cbc_decrypt_chained`, with its scratch buffer as the sixth argument. -/
def cbcDecryptChained : Prog isa :=
  (core .decrypt).seqLevels (Modes.Mode.cbcDecWide 4) levels (Modes.Mode.cbcDecChained 4)

/-- `vg_camellia_cfb128_decrypt`, with its scratch buffer as the sixth argument. -/
def cfbDecrypt : Prog isa :=
  (core .encrypt).seqLevels (Modes.Mode.cfbDecWide 4) levels (Modes.Mode.cfbDecEarly 4)

/-- `vg_camellia_ctr`, with its scratch buffer as the sixth argument. -/
def ctr : Prog isa := (core .encrypt).seqLevels Modes.Mode.ctrWide levels Modes.Mode.ctrEarly

end VG.Impl.Camellia.X86.AesNiWide
