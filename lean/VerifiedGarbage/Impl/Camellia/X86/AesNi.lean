module

public import VerifiedGarbage.Impl.Modes.X86.Seq

/-!
# Camellia on x86 (32-bit) with its S-boxes by `aesenclast`: one block

Camellia's s1 is the AES S-box between two affine maps of a byte (RFC 3713
§2.4.2 gives it as an inversion in GF(2⁸) between affine maps, as FIPS 197
§5.1.1 gives the AES S-box), and s2, s3, s4 are s1 with a byte rotated after
or before. So with AES-NI (`aesenclast`, whose `SubBytes` is all that is
used of it) and SSSE3 (`pshufb`, for an affine map of every byte of a
register as two look-ups of a nibble, and for byte shuffles) a round's eight
S-boxes are one `aesenclast`.

The state between rounds is kept in the form the S-boxes take: byte `i` of a
half `h` as `Q i (h i) = L1 (rot^a_i (h i))`, where `L1` is the linear part of
the map before the AES S-box and `a_i = 1` at the two positions of s4. A
round is then `aesenclast`, and one linear map of its output: `Q` of the P
function of the S-boxes' outer maps, per byte one of four maps
`N_e = L1 ∘ rot^e ∘ L2` (`e = a_i + b_j`, `b_j` the rotation after s1 at
position `j`), each two look-ups, and byte shuffles. The FL layers and the
two ends convert to and from the bytes themselves.

A register holds one block's half in its low quadword, in the byte order in
which a 32-bit word is a little-endian lane (`BSW`); a half is *spread* when
it is the exclusive-or of the register's two quadwords: a round's shuffles
put terms in both, and the next round folds them (`pshufd`, `pxor`) before
its `aesenclast`.

`prepare` and `crypt` are a core of the modes (`core`,
`Impl.Modes.X86.Core`) for one block at a time. With the modes' scratch
buffer at `sb`: its first slot holds the address of the table of constants
`VG_CAMELLIA_AESNI` (taken once, by `prepare`, with `symPush`), the block is
at byte 8, and the keys the rounds read are from byte 24 on, made by
`prepare` from the schedule `vg_camellia_expand_key` stores:

* `KIN` (16 bytes): `[Q (kw1 ⊕ k1) ⊕ c | Q (kw2 ⊕ k2) ⊕ c ⊕ g]`, where `c`
  and `g` are the constants of the maps;
* then for each group of six rounds, 112 bytes: the rounds' keys as
  differences `Q (k_r ⊕ k_(r+2))` in three pairs (a round loads its eight
  bytes with `movq`), the masks of the FL layer after the group (`E1`,
  `E2`, `C12`) and the next group's `KIN`; the last group has, in place of
  the masks, the last two subkeys as stored.

The code is `aes` and `ssse3` code: its dispatcher runs it only where the
CPU has both.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86.AesNi

open VG.X86
open VG.Impl.Modes.X86 (sb at_ argOp Core)

/-- The table of constants' name. -/
def tableName : String := "VG_CAMELLIA_AESNI"

/-- The constants, 16 bytes each (two words): the masks, the nibble tables of
the byte maps, the shuffles of a round, and the constants of the keys. -/
def table : List (BitVec 64) := [
  0x0f0f0f0f0f0f0f0f, 0x0f0f0f0f0f0f0f0f, 0x0405060700010203, 0x0c0d0e0f08090a0b,
  0x0c0d0e0f08090a0b, 0x0405060700010203, 0x00000f000000000f, 0x00000f000000000f,
  0xa9a8b0b118190100, 0x02031b1ab3b2aaab, 0x55f2c6613493a700, 0x8c2b1fb8ed4a7ed9,
  0xaab2021ab0a81800, 0xa6be0e16bca4140c, 0x7e4a8cb8c6f23400, 0xa69254601e2aecd8,
  0xd3d2dcdd0e0f0100, 0x16171918cbcac4c5, 0x8741ac6aed2bc600, 0x6fa9448205c32ee8,
  0x3abbb23309888100, 0x1d9c95142eafa627, 0x44e1fa5f1bbea500, 0xd87d66c38722399c,
  0xf2943c5a6305adcb, 0x0066cea891f75f39, 0xb9ff0c4af3b54600, 0x581eedab1254a7e1,
  0xb88298a27d475d67, 0x003a201ac5ffe5df, 0xc1953460a1f55400, 0x0652f3a7663293c7,
  0x34263e2ce3f1e9fb, 0x00120a18d7c5ddcf, 0x2bf71ac6ed31dc00, 0x5c806db19a46ab77,
  0xd8bab6d42f4d4123, 0x00626e0cf79599fb, 0xa99bf2c0695b3200, 0xfac8a1933a086153,
  0x0701050707070705, 0x0104060000000406, 0x0480800101018080, 0x8080808004048080,
  0x0202000380020200, 0x8003048080030301, 0x0605800605800580, 0x8080808006800680,
  0x8080038080808002, 0x8080808080808003, 0x0000000000000000, 0xffffffff00000000,
  0x00000000ffffffff, 0xffffffff00000000, 0xffffffff00000000, 0x0000000000000000,
  0xffffffff00000000, 0x00000000ffffffff, 0x0808080808080808, 0x567ad85608080808,
  0x5e72d05e00000000, 0x5e72d05e00000000, 0x567ad85608080808, 0x0808080808080808
]

/-! ## The constants' offsets -/

def oM0 : Nat := 0
def oBSW : Nat := 16
def oOUTC : Nat := 32
def oM4 : Nat := 48
/-- The byte maps into the rounds' form (`oT`: low nibbles, high nibbles,
and those of the difference at the positions of s4) and out of it (`oI`). -/
def oT : Nat := 64
def oI : Nat := 128
/-- The four maps after the S-box (low and high nibbles): `N_0`, `N_1`,
`N_(-1)`, `N_2`. -/
def oN : Nat → Nat := fun k => 192 + 32 * k
/-- A round's five shuffles: two of `N_0`'s bytes, one of each other's. -/
def oS : Nat → Nat := fun k => 320 + 16 * k
def oN1 : Nat := 400
def oM1 : Nat := 416
def oN2 : Nat := 432
def oM2 : Nat := 448
def oCK : Nat := 464
def oGG : Nat := 480
def oCW2 : Nat := 496

/-- The table's base register in `prepare` and `crypt`. -/
def tbr : Reg := .ebx
/-- The keys' pointer: `KIN` of the group at hand. -/
def kr : Reg := .esi
/-- The mask `0x0f` of every byte, in both. -/
def m0 : XReg := .xmm7

/-- A constant to `d`. -/
def tb (d : XReg) (off : Nat) : Instr := .movdquTbl d (at_ tbr off) tableName table
def x (op : XBinOp) (a b : XReg) : Instr := .xop (.bin op a b)
def ld (d : XReg) (b : Reg) (off : Nat) : Instr := .movdquLoad d (at_ b off)
def stx (b : Reg) (off : Nat) (r : XReg) : Instr := .movdquStore (at_ b off) r

/-- The byte map at `t` (`oT` or `oI`) of every byte of `v`, to `b`; `v`,
`a`, `c` and `d` are lost. -/
def conv (v a b c d : XReg) (t : Nat) : List Instr :=
  [x .movdqa a v, x .pand a m0, .xop (.shift .psrld v 4), x .pand v m0,
   tb b t, x .pshufb b a, tb c oM4, x .pand a c, x .pand c v,
   tb d (t + 16), x .pshufb d v, x .pxor b d,
   tb d (t + 32), x .pshufb d a, x .pxor b d,
   tb d (t + 48), x .pshufb d c, x .pxor b d]

/-- `[a | b]` in `w` to `xmm0` and `xmm1`, each with a zero high quadword;
`z` is lost. -/
def unpack (w z : XReg) : List Instr :=
  [x .pxor z z, .xop (.pshufd .xmm1 w 0x4e), x .punpcklqdq .xmm1 z] ++
    (if w = .xmm0 then [] else [x .movdqa .xmm0 w]) ++ [x .punpcklqdq .xmm0 z]

/-- The halves spread in `xmm0` and `xmm1` to `[a | b]` in `xmm2`; `xmm3` is
lost. -/
def pack : List Instr :=
  [.xop (.pshufd .xmm2 .xmm0 0x4e), x .pxor .xmm2 .xmm0, .xop (.pshufd .xmm3 .xmm1 0x4e), x .pxor .xmm3 .xmm1,
   x .punpcklqdq .xmm2 .xmm3]

/-- The shuffles at `ms` of `acc`'s bytes into `y`, through `o` for all but
the last. -/
def shufs (acc o y : XReg) : List Nat → List Instr
  | [] => []
  | [k] => [tb .xmm6 (oS k), x .pshufb acc .xmm6, x .pxor y acc]
  | k :: ks => [x .movdqa o acc, tb .xmm6 (oS k), x .pshufb o .xmm6, x .pxor y o] ++ shufs acc o y ks

/-- Map `k` of the S-boxes' bytes (their nibbles in `xmm3` and `xmm2`) to
`acc`, and its shuffles `ms` into `y`. -/
def flavor (acc o y : XReg) (k : Nat) (ms : List Nat) : List Instr :=
  [tb acc (oN k), x .pshufb acc .xmm3, tb .xmm6 (oN k + 16), x .pshufb .xmm6 .xmm2, x .pxor acc .xmm6] ++
    shufs acc o y ms

/-- Round `i` of a group: `y ⊕=` the round's map of the S-boxes of `xr`
(folded), and `xr ⊕=` the keys' difference. The accumulator alternates
between `xmm4` and `xmm5`, so that a register is written whole only after
what it held is long computed. -/
def round (xr y : XReg) (i : Nat) : List Instr :=
  [.xop (.pshufd .xmm2 xr 0x4e), x .pxor .xmm2 xr, .movqLoad .xmm5 (at_ kr (16 + 8 * i)), x .pxor xr .xmm5,
   x .aesenclast .xmm2 m0,
   x .movdqa .xmm3 .xmm2, x .pand .xmm3 m0, .xop (.shift .psrld .xmm2 4), x .pand .xmm2 m0] ++
    flavor .xmm4 .xmm5 y 0 [0, 1] ++ flavor .xmm5 .xmm4 y 1 [2] ++ flavor .xmm4 .xmm5 y 2 [3] ++
    flavor .xmm5 .xmm4 y 3 [4]

/-- The six rounds of a group. -/
def rounds6 : List Instr :=
  round .xmm0 .xmm1 0 ++ (round .xmm1 .xmm0 1 ++ (round .xmm0 .xmm1 2 ++ (round .xmm1 .xmm0 3 ++
    (round .xmm0 .xmm1 4 ++ round .xmm1 .xmm0 5))))

/-- The six rounds of a group, and one group fewer left (ZF set when none
is). -/
def rounds : List Instr := rounds6 ++ [.alu .sub .ecx (.imm 1)]

/-- `v ⊕= ((v ∧ e) rotated left by one in its 32 bits, moved up 32 bits) ⊕
((v ∧ e) moved down 32 bits)`, `e` the mask at `off`: the lanes that are not
to move are shifted out. -/
def step (v t s u : XReg) (off : Nat) : List Instr :=
  [ld t kr off, x .pand t v, x .movdqa s t, x .movdqa u t, .xop (.shift .pslld u 1), .xop (.shift .psrld t 31),
   x .por u t, .xop (.shift .psllq u 32), .xop (.shift .psrlq s 32), x .pxor v u, x .pxor v s]

/-- The spread halves as bytes, `[L | R]`, in `xmm4`. -/
def layerIn : List Instr := pack ++ conv .xmm2 .xmm3 .xmm4 .xmm5 .xmm6 oI

/-- FL of the low quadword of `xmm4` and FL⁻¹ of the high one, with the
masks of the group at hand. -/
def layerMid : List Instr :=
  step .xmm4 .xmm2 .xmm3 .xmm5 64 ++ [ld .xmm2 kr 96, x .pxor .xmm4 .xmm2] ++ step .xmm4 .xmm2 .xmm3 .xmm5 80

/-- The bytes of `xmm4` back to the rounds' form with the next group's
first keys, as the halves in `xmm0` and `xmm1`. -/
def layerOut : List Instr :=
  conv .xmm4 .xmm2 .xmm3 .xmm5 .xmm6 oT ++ [ld .xmm5 kr 112, x .pxor .xmm3 .xmm5] ++ unpack .xmm3 .xmm2

/-- The FL layer after a group (FL of the half in `xmm0`, FL⁻¹ of the one
in `xmm1`), on to the next group's keys. -/
def layer : List Instr :=
  layerIn ++ layerMid ++ layerOut ++ [.alu .add kr (.imm 112), .alu .test .ecx (.reg .ecx)]

/-- The groups left to `ecx` (3 for 18 rounds, 4 for 24), from the second
key argument, and the keys' pointer. -/
def setup : List Instr :=
  [.mov .ecx (.mem (argOp 1)), .shift .shr .ecx 3, .alu .add .ecx (.imm 1), .mov kr (.reg sb),
   .alu .add kr (.imm 24)]

/-- The block in `xmm0` to the first round's halves, in the rounds' form
with the first keys; and the mask. -/
def headX : List Instr :=
  [tb m0 oM0, tb .xmm5 oBSW, x .pshufb .xmm0 .xmm5] ++
    conv .xmm0 .xmm2 .xmm3 .xmm4 .xmm5 oT ++ [ld .xmm5 kr 0, x .pxor .xmm3 .xmm5] ++ unpack .xmm3 .xmm2

/-- The block at byte 8 of the scratch buffer to the first round's halves. -/
def cryptHead : List Instr :=
  [.mov tbr (.mem (at_ sb 0))] ++ setup ++ [ld .xmm0 sb 8] ++ headX

/-- The halves after the last round to the block's bytes, in `xmm6`. -/
def tailX : List Instr :=
  pack ++ conv .xmm2 .xmm3 .xmm6 .xmm4 .xmm5 oI ++
    [tb .xmm5 oOUTC, x .pshufb .xmm6 .xmm5, ld .xmm5 kr 64, x .pxor .xmm6 .xmm5]

/-- The halves after the last round to the block. -/
def cryptTail : List Instr := tailX ++ [stx sb 8 .xmm6]

/-- The block of the core's buffer, enciphered in place. -/
def crypt : Prog isa :=
  .seq (.block cryptHead) (.seq
    (.loop (.seq (.block rounds) (.ite .e (.block []) (.block layer))) .ne) (.block cryptTail))

/-- The two words at `off` of the schedule (at `eax`) in the rounds' form,
to `xmm2`. -/
def pair (off : Nat) : List Instr :=
  [ld .xmm0 .eax off, tb .xmm1 oBSW, x .pshufb .xmm0 .xmm1] ++ conv .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 oT

/-- The mask, and the first two subkeys in the rounds' form to `xmm6`. -/
def prepHeadX : List Instr := [tb m0 oM0] ++ pair 0 ++ [x .movdqa .xmm6 .xmm2]

/-- The table's address to the scratch buffer's first slot, and the first
two subkeys in the rounds' form to `xmm6`. -/
def prepHead : List Instr :=
  [.store (at_ sb 0) .eax, .mov tbr (.reg .eax), .mov .eax (.mem (argOp 0))] ++ setup ++ prepHeadX

/-- A group's keys from its six subkeys (at `[eax + 16]`): its `KIN` (with
the first two subkeys, in `xmm6`, for the first group), and the three pairs
of differences. -/
def prepGroupX : List Instr :=
  pair 16 ++ [x .movdqa .xmm5 .xmm2, tb .xmm0 oCK, x .pxor .xmm0 .xmm5, x .pxor .xmm0 .xmm6, stx kr 0 .xmm0,
    x .pxor .xmm6 .xmm6] ++
  pair 32 ++ [x .pxor .xmm5 .xmm2, tb .xmm0 oGG, x .pxor .xmm5 .xmm0, stx kr 16 .xmm5, x .movdqa .xmm5 .xmm2] ++
  pair 48 ++ [x .pxor .xmm5 .xmm2, tb .xmm0 oGG, x .pxor .xmm5 .xmm0, stx kr 32 .xmm5,
    tb .xmm0 oCW2, x .pxor .xmm2 .xmm0, stx kr 48 .xmm2]

/-- A group's keys, and the count of the groups left. -/
def prepGroup : List Instr := prepGroupX ++ [.alu .sub .ecx (.imm 1)]

/-- The masks of the FL layer after a group, from its two subkeys (at
`[eax + 64]`). -/
def prepMasksX : List Instr :=
  [ld .xmm0 .eax 64, tb .xmm1 oBSW, x .pshufb .xmm0 .xmm1,
   x .movdqa .xmm1 .xmm0, tb .xmm2 oN1, x .pxor .xmm1 .xmm2, tb .xmm2 oM1, x .pand .xmm1 .xmm2, stx kr 64 .xmm1,
   x .movdqa .xmm1 .xmm0, tb .xmm2 oN2, x .pxor .xmm1 .xmm2, tb .xmm2 oM2, x .pand .xmm1 .xmm2, stx kr 80 .xmm1,
   .xop (.shift .psrlq .xmm0 32), stx kr 96 .xmm0]

/-- The masks of the FL layer after a group, and on to the next group. -/
def prepMasks : List Instr :=
  prepMasksX ++ [.alu .add .eax (.imm 64), .alu .add kr (.imm 112), .alu .test .ecx (.reg .ecx)]

/-- The last two subkeys, as stored. -/
def prepTail : List Instr := [ld .xmm0 .eax 64, stx kr 64 .xmm0]

/-- The keys the rounds read, from the schedule and the number of rounds in
the first two stack arguments. -/
def prepare : Prog isa :=
  .seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1)) (.seq (.block prepHead) (.seq
    (.loop (.seq (.block prepGroup) (.ite .e (.block []) (.block prepMasks))) .ne) (.block prepTail)))

/-- The slots of the scratch buffer the core uses: the table's address and
a spare slot, the block, and 480 bytes for the keys, of which four groups
(16 + 4 · 112 bytes) take 464. -/
def slots : Nat := 126

/-- The modes' core: one block at a time. -/
def core : Core :=
  { prepare := prepare, crypt := crypt, slots := slots, total := slots + 10, buf := 2, G := 1, bw := 4,
    stack := 4, ka := 2 }

end VG.Impl.Camellia.X86.AesNi
