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
`VG_CAST5_S1234` gives them (`Impl/Cast5/X86.lean`); the rounds, the blocks
and the modes' core are the baseline's over its call (`roundWith`,
`Modes.coreWith`): `core`.

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

/-! ## The modes' core -/

/-- The core's slots: the baseline's working space and block (slots 0 to
65), and the look-ups' index vectors and entries (bytes 272 to 591). -/
def coreSlots : Nat := 148

/-- CAST5's core for the modes (`Modes.coreWith`) with the rounds' look-ups
the call of `lookup`: the baseline's rounds, blocks and core
(`Impl/Cast5/X86.lean`, `Impl/Cast5/X86/Modes.lean`) over it. -/
def core (up : Bool) : Core := Modes.coreWith (.call fnName lookup) coreSlots 8 up

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

/-! ## The functions as emitted

Each function with its working space in a frame on the stack, which it
wipes (`withStackScratchWiped`), then its cleanup
(`Impl.Scrub.X86.scrubSel rb W ws`): of the `W` bytes of stack below `esp`
that its contract reserves, the doublewords `ws` its code may leave
different in two runs zeroed, and the registers a callee may change
cleared, so that it returns without secret residue.

The frame is larger than its working space and header need (664 bytes for
660), so that the working space, which `withStackScratchWiped` puts 28 bytes
above the frame's base for five arguments, is at a multiple of 16 when `esp`
is one at the call: the look-ups' 16-byte loads and stores then cross no
page, or line of the cache. -/

namespace Fn

/-- The doublewords of the 672 bytes of stack below `esp` that the residue
analysis finds a function may leave different in two runs: the look-ups'
call and its table's address, the frame's header, and the four bytes at the
frame's top that the working space does not reach. -/
def words : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 167]

/-- `Spec.Cast5.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 672 words (Impl.StackScratch.X86.withStackScratchWiped 664 5 158 Ssse3.cbcEncryptChained)

/-- `Spec.Cast5.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 672 words (Impl.StackScratch.X86.withStackScratchWiped 664 5 158 Ssse3.ofb)

/-- `Spec.Cast5.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 672 words (Impl.StackScratch.X86.withStackScratchWiped 664 5 158 Ssse3.cfbEncrypt)

/-- `Spec.Cast5.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 672 words (Impl.StackScratch.X86.withStackScratchWiped 664 5 158 Ssse3.cfbEncryptFinal)

/-- `Spec.Cast5.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 672 words (Impl.StackScratch.X86.withStackScratchWiped 664 5 158 Ssse3.cfbDecryptFinal)

/-- `Spec.Cast5.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 672 words (Impl.StackScratch.X86.withStackScratchWiped 664 5 158 Ssse3.ofbFinal)

end Fn

end VG.Impl.Cast5.X86.Ssse3
