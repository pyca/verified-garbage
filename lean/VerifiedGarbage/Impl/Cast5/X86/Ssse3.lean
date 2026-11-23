module

public import VerifiedGarbage.Impl.Cast5.X86.Modes
public import VerifiedGarbage.Impl.Cast5.X86.FbFinal
public import VerifiedGarbage.Impl.Modes.X86.SeqFinal
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-!
# CAST5 on x86 (32-bit) with its S-box look-ups by `pshufb`: one block

`lookup`, the internal function `vg_cast5_lookup_ssse3`: the four look-ups
of a round, `S4[Id], S3[Ic], S2[Ib], S1[Ia]` in the doublewords of `xmm1`
for the bytes of `I` in the doublewords of `xmm0`, as the baseline's scan of
`VG_CAST5_S1234` gives them (`Impl/Cast5/X86.lean`); a round is the
baseline's with the scan replaced by its call (`round`), and the blocks and
the modes' core are the baseline's over that round.

The S-boxes S1 to S4 are a static table in byte planes, `VG_CAST5_SSSE3`:
byte `p` of `S_{j+1}[x]` at `1024 j + 256 p + x`, then the constants. A
look-up of a byte `x` in a plane of 256 bytes reads the plane's sixteen rows
of sixteen bytes, each through `pshufb` with the row's index vector, and ORs
them: the index vector of row `r` holds `x`'s low nibble where `x`'s high
nibble is `r`, and `0x80` ORed with it elsewhere, for which `pshufb` gives
zero; it is `pshufb(C_r, H) | L` for the high and the low nibbles `H` and
`L` and the constant row `C_r`. Every doubleword of the index register holds
`I`, so a row's index vector serves the four S-boxes: the function makes the
sixteen index vectors once, to the working space (`vOff`), and then for each
S-box reads its four planes' rows (`scan`), which gives each plane's byte at
each byte of `I`; two unpacks and a `pshufb` turn them into the S-box's
entries at the four bytes of `I` (`eOff`), and the four doublewords a round
uses, one of each S-box, are put together at the end (`assemble`).

The XMM registers take turns (`xr`), as in Blowfish's function
(`Impl/Blowfish/X86/Ssse3.lean`): load `k` of an S-box's pass goes to
register `k mod 8`.

The function's convention is its own: the working space at `esi`, of which
it writes the bytes 272 to 591 at fixed offsets; it keeps `ebx`, `ebp`,
`esi`, `edi` and `esp`, changes `eax`, `ecx`, `edx`, the flags and the XMM
registers, and uses eight bytes of stack: its return address and the slot in
which it takes its table's address. No address and no branch depends on the
key or the block.
-/

@[expose] public section

namespace VG.Impl.Cast5.X86.Ssse3

open VG.X86
open VG.Impl.Cast5.X86
open VG.Impl.Modes.X86 (Core)
open VG.Impl.Modes (Mode)

/-- The internal function's name. -/
def fnName : String := "vg_cast5_lookup_ssse3"

/-- The table's name. -/
def tableName : String := "VG_CAST5_SSSE3"

/-! ## The table -/

/-- The S-box `S_{j+1}`. -/
def sboxOf : Nat → Byte → Spec.Cast5.Word
  | 0 => Spec.Cast5.S1
  | 1 => Spec.Cast5.S2
  | 2 => Spec.Cast5.S3
  | _ => Spec.Cast5.S4

/-- Byte `p` of `S_{j+1}[x]`. -/
def planeByte (j p x : Nat) : Byte := (sboxOf j (BitVec.ofNat 8 x) >>> (8 * p)).setWidth 8

/-- Eight bytes as a little-endian word. -/
def le8 (f : Nat → Byte) : BitVec 64 := f 7 ++ f 6 ++ f 5 ++ f 4 ++ f 3 ++ f 2 ++ f 1 ++ f 0

/-- The planes: word `w` holds the bytes `8 (w mod 32)` on of plane
`w / 32 mod 4` of S-box `w / 128`. -/
def planes : List (BitVec 64) :=
  (List.range 512).map fun w => le8 fun c => planeByte (w / 128) (w / 32 % 4) (8 * (w % 32) + c)

/-- The constants, 16 bytes each (two words): the sixteen rows `C_r` (zero
at byte `r`, `0x80` elsewhere), the shuffle that gathers the bytes 0, 4, 8
and 12, then 1, 5, 9 and 13, and so on, `0x0f` in every byte, and the
shuffle that puts the bytes 0, 4, 8 and 12 in every doubleword. -/
def consts : List (BitVec 64) := [
  0x8080808080808000, 0x8080808080808080, 0x8080808080800080, 0x8080808080808080,
  0x8080808080008080, 0x8080808080808080, 0x8080808000808080, 0x8080808080808080,
  0x8080800080808080, 0x8080808080808080, 0x8080008080808080, 0x8080808080808080,
  0x8000808080808080, 0x8080808080808080, 0x0080808080808080, 0x8080808080808080,
  0x8080808080808080, 0x8080808080808000, 0x8080808080808080, 0x8080808080800080,
  0x8080808080808080, 0x8080808080008080, 0x8080808080808080, 0x8080808000808080,
  0x8080808080808080, 0x8080800080808080, 0x8080808080808080, 0x8080008080808080,
  0x8080808080808080, 0x8000808080808080, 0x8080808080808080, 0x0080808080808080,
  0x0d0905010c080400, 0x0f0b07030e0a0602, 0x0f0f0f0f0f0f0f0f, 0x0f0f0f0f0f0f0f0f,
  0x0c0804000c080400, 0x0c0804000c080400
]

/-- `VG_CAST5_SSSE3`: the planes, then the constants. -/
def table : List (BitVec 64) := planes ++ consts

/-! ## The table's and the working space's offsets -/

/-- Plane `p` of S-box `j`. -/
def planeOff (j p : Nat) : Nat := 1024 * j + 256 * p
/-- The row `C_r`. -/
def oC (r : Nat) : Nat := 4096 + 16 * r
/-- The shuffle that gathers. -/
def oT : Nat := 4352
/-- `0x0f` in every byte. -/
def oM : Nat := 4368
/-- The shuffle that spreads `I` to every doubleword. -/
def oS : Nat := 4384

/-- The index vector of row `r`, in the working space. -/
def vOff (r : Nat) : Nat := 272 + 16 * r
/-- S-box `j`'s entries at the four bytes of `I`. -/
def eOff (j : Nat) : Nat := 528 + 16 * j

/-- The table's base register. -/
def tbr : Reg := .edx

/-- XMM register `k`, modulo 8. -/
def xr (k : Nat) : XReg :=
  match k % 8 with
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | 3 => .xmm3 | 4 => .xmm4 | 5 => .xmm5 | 6 => .xmm6 | _ => .xmm7

/-- Sixteen bytes of the table to `d`. -/
def tb (d : XReg) (off : Nat) : Instr := .movdquTbl d (at_ tbr off) tableName table
def x (op : XBinOp) (a b : XReg) : Instr := .xop (.bin op a b)
def ld (d : XReg) (b : Reg) (off : Nat) : Instr := .movdquLoad d (at_ b off)
def stx (b : Reg) (off : Nat) (r : XReg) : Instr := .movdquStore (at_ b off) r

/-! ## The look-ups -/

/-- The table's address; `I`, whose bytes are the doublewords of `xmm0`, to
every doubleword of it, and its bytes' high nibbles to `xmm1` and low
nibbles to `xmm0`. -/
def head : List Instr :=
  [.mov tbr (.reg .eax), tb .xmm2 oS, x .pshufb .xmm0 .xmm2, tb .xmm2 oM, x .movdqa .xmm1 .xmm0,
   .xop (.shift .psrld .xmm1 4), x .pand .xmm1 .xmm2, x .pand .xmm0 .xmm2]

/-- The index vector of row `r` to the working space, through one of the
six registers the nibbles are not in. -/
def index (r : Nat) : List Instr :=
  [tb (xr (2 + r % 6)) (oC r), x .pshufb (xr (2 + r % 6)) .xmm1, x .por (xr (2 + r % 6)) .xmm0,
   stx .esi (vOff r) (xr (2 + r % 6))]

/-- Row `r` of plane `p` of S-box `j` at the row's index vector, in the
register `5r`: to the register `5r + 1 + p`, with the plane's rows before
it, in the register `5r + 4 + p` (that of row `r - 1`), ORed in. -/
def plane (j r p : Nat) : List Instr :=
  [tb (xr (5 * r + 1 + p)) (planeOff j p + 16 * r), x .pshufb (xr (5 * r + 1 + p)) (xr (5 * r))] ++
    (if r = 0 then [] else [x .por (xr (5 * r + 1 + p)) (xr (5 * r + 4 + p))])

/-- Row `r` of the four planes of S-box `j`. -/
def row (j r : Nat) : List Instr :=
  [ld (xr (5 * r)) .esi (vOff r)] ++ plane j r 0 ++ plane j r 1 ++ plane j r 2 ++ plane j r 3

/-- S-box `j`'s four planes at the bytes of `I`, in `xmm4` to `xmm7`. -/
def scan (j : Nat) : List Instr := (List.range 16).flatMap (row j)

/-- The planes' bytes to S-box `j`'s entries at the four bytes of `I`, in
the working space. -/
def gather (j : Nat) : List Instr :=
  [x .punpckldq .xmm4 .xmm5, x .punpckldq .xmm6 .xmm7, x .punpcklqdq .xmm4 .xmm6, tb .xmm0 oT,
   x .pshufb .xmm4 .xmm0, stx .esi (eOff j) .xmm4]

/-- S-box `j` of the four bytes of `I`. -/
def sbox (j : Nat) : List Instr := scan j ++ gather j

/-- `S4` at byte 0 of `I`, `S3` at byte 1, `S2` at byte 2 and `S1` at byte 3
to the doublewords of `xmm1`. -/
def assemble : List Instr :=
  [ld .xmm1 .esi (eOff 3), ld .xmm2 .esi (eOff 2), x .punpckldq .xmm1 .xmm2, .xop (.pshufd .xmm1 .xmm1 0x0c),
   ld .xmm3 .esi (eOff 1), ld .xmm2 .esi (eOff 0), x .punpckhdq .xmm3 .xmm2, .xop (.pshufd .xmm3 .xmm3 0x0c),
   x .punpcklqdq .xmm1 .xmm3]

/-- `vg_cast5_lookup_ssse3`: for the bytes `Id, Ic, Ib, Ia` of `I` in the
doublewords of `xmm0`, `S4[Id], S3[Ic], S2[Ib], S1[Ia]` in those of `xmm1`,
with the working space at `esi`. -/
def lookup : Prog isa :=
  .seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1))
    (.block (head ++ (List.range 16).flatMap index ++ sbox 0 ++ sbox 1 ++ sbox 2 ++ sbox 3 ++ assemble))

/-! ## The block

The baseline's rounds, groups and blocks (`Impl/Cast5/X86.lean`), with the
scan of a round replaced by the call of `lookup`. -/

/-- A round of Type `t` (1, 2 or 3). -/
def round (t : Nat) (up : Bool) : Prog isa :=
  .seq (.block (mask t ++ rotate ++ spread))
    (.seq (.call fnName lookup)
      (.block (([.movdquStore (at_ .esi 0) .xmm1] : List Instr) ++ combine t ++ feistel up)))

/-- Three rounds, of Types 1, 2 and 3 (encryption) or 3, 2 and 1
(decryption), then the count of groups left down (ZF set at 0). -/
def group (up : Bool) : Prog isa :=
  .seq (round (if up then 1 else 3) up) (.seq (round 2 up)
    (.seq (round (if up then 3 else 1) up)
      (.block [.mov .edx (.mem (at_ .esi gcOff)), .alu .sub .edx (imm 1), .store (at_ .esi gcOff) .edx])))

/-- Encrypting the block `(L₀, R₀)` in `(ebx, ebp)`. -/
def encryptBlock : Prog isa :=
  .seq (.block (([.mov .edx (.mem (at_ .esi schedOff)), .store (at_ .esi kpOff) .edx] : List Instr) ++
      groups))
    (.seq (.loop (group true) .ne)
      (.seq (.block [.mov .ecx (.mem (at_ .esi roundsOff)), .alu .cmp .ecx (imm 16)])
        (.ite .e (round 1 true) (.block []))))

/-- Decrypting the block in `(ebx, ebp)`. -/
def decryptBlock : Prog isa :=
  .seq (.block (([.mov .edx (.mem (at_ .esi roundsOff)), .alu .add .edx (.reg .edx),
      .alu .add .edx (.reg .edx), .mov .ecx (.mem (at_ .esi schedOff)), .alu .add .edx (.reg .ecx),
      .alu .sub .edx (imm 4),
      .store (at_ .esi kpOff) .edx] : List Instr) ++ groups))
    (.seq (.ite .e (round 1 false) (.block []))
      (.loop (group false) .ne))

/-! ## The modes' core -/

/-- The core's slots: the baseline's working space and block (slots 0 to
65), and the look-ups' index vectors and entries (bytes 272 to 591). -/
def coreSlots : Nat := 148
def dSlot : Nat := coreSlots + 4
def nSlot : Nat := coreSlots + 5

/-- `(Rₙ, Lₙ)` to the block, the modes' data pointer and steps left read
before and written again after, and `edi` the working space's address. -/
def store : List Instr :=
  [.mov .edx (.mem (at_ .esi dataOff)), .mov .eax (.mem (at_ .esi (4 * dSlot))),
   .mov .ecx (.mem (at_ .esi (4 * nSlot))),
   .bswap .ebp, .store (at_ .edx 0) .ebp, .bswap .ebx, .store (at_ .edx 4) .ebx,
   .store (at_ .esi (4 * dSlot)) .eax, .store (at_ .esi (4 * nSlot)) .ecx, .mov .edi (.reg .esi)]

/-- The block, encrypted (`up`) or decrypted. -/
def crypt (up : Bool) : Prog isa :=
  .seq (.block Modes.setup) (.seq (.block load) (.seq (if up then encryptBlock else decryptBlock) (.block store)))

/-- CAST5's core for the modes over the look-ups by `pshufb`. -/
def core (up : Bool) : Core where
  prepare := .block []
  crypt := crypt up
  slots := coreSlots
  total := coreSlots + 10
  buf := Modes.bufSlot
  G := 1
  bw := 2
  stack := 8
  ka := 2

/-- CBC encryption that updates the chaining value, with its scratch buffer as the sixth argument. -/
def cbcEncryptChained : Prog isa := (core true).seq (Mode.cbcEncChained 2)
/-- OFB. -/
def ofb : Prog isa := (core true).seq (Mode.ofb 2)
/-- CFB64 encryption. -/
def cfbEncrypt : Prog isa := (core true).seq (Mode.cfbEnc 2)
/-- CFB64 encryption of a message's last piece. -/
def cfbEncryptFinal : Prog isa := (core true).seqFinal (Mode.cfbEnc 2)
/-- CFB64 decryption of a message's last piece. -/
def cfbDecryptFinal : Prog isa := (core true).seqFinal (Mode.cfbDec 2)
/-- OFB of a message's last piece. -/
def ofbFinal : Prog isa := (core true).seqFinal (Mode.ofb 2)

end VG.Impl.Cast5.X86.Ssse3
