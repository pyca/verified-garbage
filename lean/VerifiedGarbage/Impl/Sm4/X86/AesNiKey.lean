module

public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-!
# The SM4 key schedule on x86 (32-bit) with its S-box by `aesenclast`

`vg_sm4_expand_key(key, schedule)` (cdecl), for CPUs with `aes` and `ssse3`:
the 32 round keys of GB/T 32907-2016 §7.3, `rkᵢ = Kᵢ₊₄ = Kᵢ ⊕ T'(Kᵢ₊₁ ⊕
Kᵢ₊₂ ⊕ Kᵢ₊₃ ⊕ CKᵢ)`, to `schedule` as 32 little-endian 32-bit words, the
format `Spec.Sm4.scheduleAt` reads.

SM4's S-box is the AES S-box between two affine maps of a byte
(`Proof/Sm4/X86/AesNiKeyMaps.lean`), so a word's S-boxes are `aesenclast`
between byte maps, each two look-ups of a nibble with `pshufb`;
`aesenclast`'s round key is the mask `0x0f` of every byte, and the tables
of low nibbles after it take the complemented nibble. Every word `K` is
kept as `PL K`, the linear part of the map before the S-box on each byte,
in the first 32-bit lane of a register, its bytes in the key's order (the
most significant first); the constants `CKᵢ` are in the table with that
map's constant as well, so that `aesenclast` takes the exclusive-or of
three words and a constant.

`T' = L' ∘ τ`, and byte `j` of `L'(B) = B ⊕ (B ⋘ 13) ⊕ (B ⋘ 23)` is
`b[j] ⊕ N₁ b[j+1] ⊕ N₂ b[j+2] ⊕ N₃ b[j+3]` for three linear maps of a
byte: four byte maps after the S-box (eight look-ups), each of the word
rotated by its number of bytes. A shuffle before `aesenclast` puts byte
`l` of its input in every byte of lane `l`, so that `aesenclast`'s
ShiftRows leaves the S-boxes of the word rotated by `k` bytes in lane `k`;
the nibbles are then moved on by a lane (`pshufd`) between the maps, whose
look-ups are all right in the first lane, and nothing but exclusive-ors is
between a word and the next that depends on it.

`movdquTbl` loads a constant at a fixed place of the table, so a loop
cannot walk the 32 `CKᵢ` there: the code first copies them, four to a row
of 16 bytes, to the schedule's 128 bytes, and a turn of the loop, four
rounds, reads its row there, then stores its four round keys over it. The
four words are in `xmm0` to `xmm3`, a round replacing the oldest. There is
no working space in memory: the table's address is taken with `symPush`,
in a frame of four bytes, and the registers are the caller's to lose.
-/

@[expose] public section

namespace VG.Impl.Sm4.X86.AesNiKey

open VG.X86

/-- The table of constants' name. -/
def tableName : String := "VG_SM4_KEY_AESNI"

/-- The constants, 16 bytes each (two words): the mask, the nibble tables
of the byte maps, a lane's bytes reversed, `FK`, the shuffle before
`aesenclast`, and the 32 `CKᵢ`. -/
def table : List (BitVec 64) := [
  0x0f0f0f0f0f0f0f0f, 0x0f0f0f0f0f0f0f0f, 0x9096e3e575730600, 0xc6c0b5b323255056,
  0xe240ab09eb49a200, 0xf052b91bf95bb012, 0x74019de89ce97500, 0x4134a8dda9dc4035,
  0x9ef70960fe976900, 0xf099670e90f9076e, 0x0405060700010203, 0x0c0d0e0f08090a0b,
  0x61396a32b4ecbfe7, 0x0e56055ddb83d088, 0x9b91060c979d0a00, 0xa4ae3933a8a2353f,
  0x091b40520012495b, 0x12005b491b095240, 0x1b09495b40521200, 0x495b1b0912004052,
  0xa232f161c6569505, 0x9606c555f262a131, 0x41c01293d2538100, 0x61e032b3f273a120,
  0x0f6d4123583a1674, 0x87e5c9abd0b29efc, 0x3bbb0080bb3b8000, 0x56d66dedd656ed6d,
  0xab9e7e3d8ddcff2e, 0x0a3ae28a20b657d0, 0x0101010100000000, 0x0303030302020202,
  0xec6d3d1040c19101, 0x1132894fbd9e2cbc, 0x5c94c4a0f02373e3, 0xe8cb39ff4d6e9c0c,
  0xa52474421293c353, 0x587bc90ffdde65f5, 0x15c696f2a26a3aaa, 0xa88b79bf0427d545,
  0xf776260b5bda8a1a, 0x183b8046b49737a7, 0x478fdfbbeb2a7aea, 0xe1c230f656758717,
  0xbe3f6f4b1b9aca5a, 0x5172d214e6c57eee, 0x0ecf9ffbab6333a3, 0xb39062a41f3cce5e
]

/-- The mask `0x0f` of every byte. -/
def oM0 : Nat := 0
/-- `PL`, into the rounds' form: the tables of its low nibble and its high nibble. -/
def oCV : Nat := 16
/-- Out of it. -/
def oIV : Nat := 48
/-- A lane's bytes reversed. -/
def oBSW : Nat := 80
/-- The byte map after the S-box of the byte `r` places on is at
`oQ + 32 r`: the tables of its low nibble (complemented) and its high
nibble. -/
def oQ : Nat := 96
/-- `PL FK`. -/
def oFK : Nat := 224
/-- Byte `l` of a lane to every byte of lane `l`. -/
def oSPR : Nat := 240
/-- `PL CKᵢ` and the constant of the map before the S-box, four to a row:
`CK₄ₘ … CK₄ₘ₊₃` at `oCK + 16 m`. -/
def oCK : Nat := 256

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }
/-- Stack argument `i`. -/
def argOp (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

/-- The table's base register. -/
def tbr : Reg := .eax
/-- The schedule's pointer: the row of the turn at hand. -/
def kp : Reg := .edx
/-- The mask `0x0f` of every byte. -/
def m0 : XReg := .xmm7

/-- A constant to `d`. -/
def tb (d : XReg) (off : Nat) : Instr := .movdquTbl d (at_ tbr off) tableName table
def x (op : XBinOp) (a b : XReg) : Instr := .xop (.bin op a b)
def ld (d : XReg) (b : Reg) (off : Nat) : Instr := .movdquLoad d (at_ b off)
def stx (b : Reg) (off : Nat) (r : XReg) : Instr := .movdquStore (at_ b off) r

/-- The byte map at `t` (`oCV` or `oIV`) of every byte of `v`, to `b`; `v`
and `a` are lost. -/
def conv (v a b : XReg) (t : Nat) : List Instr :=
  [x .movdqa a v, .xop (.shift .psrld a 4), x .pand a m0, x .pand v m0,
   tb b t, x .pshufb b v, tb v (t + 16), x .pshufb v a, x .pxor b v]

/-- The eight rows of constants to the schedule's 128 bytes. -/
def stage : List Instr :=
  (List.range 8).flatMap fun m => [tb .xmm6 (oCK + 16 * m), stx kp (16 * m) .xmm6]

/-- The mask, and the key at `ecx` to its four words with `FK`, in the
rounds' form, in `xmm0` to `xmm3`. -/
def headX : List Instr :=
  [tb m0 oM0, ld .xmm4 .ecx 0] ++ conv .xmm4 .xmm5 .xmm6 oCV ++
    [tb .xmm5 oFK, x .pxor .xmm6 .xmm5,
     .xop (.pshufd .xmm0 .xmm6 0x00), .xop (.pshufd .xmm1 .xmm6 0x55), .xop (.pshufd .xmm2 .xmm6 0xaa),
     .xop (.pshufd .xmm3 .xmm6 0xff)]

/-- Constant `w` of the row in `xmm4` to its first lane. -/
def pick (w : Nat) : List Instr :=
  if w = 0 then [] else [.xop (.pshufd .xmm4 .xmm4 (BitVec.ofNat 8 w))]

/-- `aesenclast`'s input for the round `w` of a turn whose other three
words are in `v1`, `v2` and `v3`: their exclusive-or with constant `w` of
the turn's row, byte `l` of it in every byte of lane `l`. -/
def prepX (v1 v2 v3 : XReg) (w : Nat) : List Instr :=
  [ld .xmm4 kp 0] ++ pick w ++
    [x .pxor .xmm4 v1, x .pxor .xmm4 v2, x .pxor .xmm4 v3, tb .xmm6 oSPR, x .pshufb .xmm4 .xmm6]

/-- The byte map `r` of the S-boxes whose nibbles are in `xmm4` and `xmm5`,
added to `v0`. -/
def look (v0 : XReg) (r : Nat) : List Instr :=
  [tb .xmm6 (oQ + 32 * r), x .pshufb .xmm6 .xmm4, x .pxor v0 .xmm6,
   tb .xmm6 (oQ + 32 * r + 16), x .pshufb .xmm6 .xmm5, x .pxor v0 .xmm6]

/-- The nibbles on by a lane. -/
def lanes : List Instr := [.xop (.pshufd .xmm4 .xmm4 0x39), .xop (.pshufd .xmm5 .xmm5 0x39)]

/-- The S-boxes of `xmm4` and the four byte maps of them, added to `v0`. -/
def roundX (v0 : XReg) : List Instr :=
  [x .aesenclast .xmm4 m0, x .movdqa .xmm5 .xmm4, .xop (.shift .psrld .xmm5 4), x .pand .xmm5 m0,
   x .pand .xmm4 m0] ++ look v0 0 ++ lanes ++ look v0 1 ++ lanes ++ look v0 2 ++ lanes ++ look v0 3

/-- Round `w` of a turn: `v0` becomes `v0 ⊕ T'(v1 ⊕ v2 ⊕ v3 ⊕ CK)`. -/
def round (v0 v1 v2 v3 : XReg) (w : Nat) : List Instr := prepX v1 v2 v3 w ++ roundX v0

/-- The four words to the schedule's format, in `xmm4`: out of the rounds'
form, each word's bytes reversed. -/
def outX : List Instr :=
  [x .movdqa .xmm6 .xmm0, x .punpcklqdq .xmm6 .xmm1, .xop (.pshufd .xmm6 .xmm6 0x88),
   x .movdqa .xmm5 .xmm2, x .punpcklqdq .xmm5 .xmm3, .xop (.pshufd .xmm5 .xmm5 0x88),
   x .punpcklqdq .xmm6 .xmm5] ++ conv .xmm6 .xmm5 .xmm4 oIV ++ [tb .xmm6 oBSW, x .pshufb .xmm4 .xmm6]

/-- The store of a turn's four round keys over its row, on to the next
row, and a turn fewer. -/
def step : List Instr := [stx kp 0 .xmm4, .alu .add kp (.imm 16), .alu .sub .ecx (.imm 1)]

/-- A turn of the loop: four rounds, and their round keys stored. -/
def turn : List Instr :=
  round .xmm0 .xmm1 .xmm2 .xmm3 0 ++ round .xmm1 .xmm2 .xmm3 .xmm0 1 ++ round .xmm2 .xmm3 .xmm0 .xmm1 2 ++
    round .xmm3 .xmm0 .xmm1 .xmm2 3 ++ outX ++ step

/-- The schedule's address, the constants to it, the key's address, the
key's words, and the eight turns. -/
def head : List Instr :=
  [.mov kp (.mem (argOp 1))] ++ stage ++ [.mov .ecx (.mem (argOp 0))] ++ headX ++ [.mov .ecx (.imm 8)]

/-- `vg_sm4_expand_key(key, schedule)`. -/
def expandKey : Prog isa :=
  .seq (.frame (.symPush tbr tableName) (.block []) (.pop .ecx 1)) (.seq (.block head)
    (.loop (.block turn) .ne))

end VG.Impl.Sm4.X86.AesNiKey

namespace VG.Impl.Sm4.X86.AesNiKey.Fn

open VG.X86

/-- The doublewords of the 4 bytes of stack below `esp` that the residue
analysis finds the function may leave different in two runs: none. -/
def noWords : List Nat := []

/-- `Spec.Sm4.expandKeyApi`'s function as emitted: the code, then its
cleanup (`Impl.Scrub.X86.scrubSel`), which clears the registers a callee
may change, so that it returns without secret residue. -/
def expandKey : Prog isa := Impl.Scrub.X86.scrubSel 0 4 noWords Impl.Sm4.X86.AesNiKey.expandKey

end VG.Impl.Sm4.X86.AesNiKey.Fn
