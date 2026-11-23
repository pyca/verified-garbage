module

public import VerifiedGarbage.Impl.Blowfish.X86
public import VerifiedGarbage.Impl.Modes.X86.SeqFinal
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-!
# Blowfish on x86 (32-bit) with its S-box look-ups by `pshufb`: one block

`encryptBlock`, the internal function `vg_blowfish_encrypt_block_ssse3`: a
block's encryption for the functions that encrypt one block at a time (key
expansion, CBC encryption, CFB, OFB). It is `ssse3` code: the dispatchers
of the functions that call it run them only where the CPU has SSSE3.

Its convention is its own (only the code below calls it): the halves in
`edx` (xL) and `ebp` (xR), the schedule's address in `esi`, and working
space at `edi`, of which it writes the bytes 64 to 383; it returns the
encrypted halves in `ecx` and `edx`, keeps `esi`, `edi` and `esp`, and
changes `eax`, `ebx`, `ebp`, the flags and the XMM registers. It uses eight
bytes of stack: its return address and the slot in which it takes the
address of its table of constants, `VG_BLOWFISH_SSSE3` (in `eax`, losing
`ecx`: the halves then go to `ecx` and `edx`, where the rounds keep them).

A look-up of a byte `x` in a plane of 256 bytes (the schedule holds each
S-box as four planes, one of each byte of its entries) reads the plane's
sixteen rows of sixteen bytes, each through `pshufb` with the row's index
vector, and ORs them: the index vector of row `r` holds `x`'s low nibble
where `x`'s high nibble is `r`, and `0x80` ORed with it elsewhere, for which
`pshufb` gives zero. It is `pshufb(C_r, H) | L` for the high and the low
nibbles `H` and `L` and the constant row `C_r` (zero at `r`, `0x80`
elsewhere). Every doubleword of the index register holds xL, so that a row's
index vector serves the four S-boxes: a round makes the sixteen index
vectors once, to the working space (`vOff`), and then for each S-box reads
its four planes' rows (`scan`), which gives, in the four doublewords of four
registers, each plane's byte at each byte of xL; two unpacks and a `pshufb`
turn them into the S-box's entries at the four bytes of xL (`fOff`), of
which F takes the entry at the S-box's byte.

The XMM registers take turns (`xr`): every instruction that writes a whole
register (a load) writes the one that was written the longest ago, eight
loads before, and a row's bytes are ORed into the register just loaded, not
into the one that held the plane's bytes so far. On a processor that makes
a load into a register wait for the register's old value, a load then waits
for a value computed eight loads before, not for the one before it.

No address and no branch depends on the key or the block: the planes are
read in full, at fixed offsets from `esi`, and every store is at a fixed
offset from `edi`.

`core`: the block function as a core of the modes
(`Impl.Modes.X86.Core`); `blkKey`: as the block function of key expansion
(`expandKeyWith`).
-/

@[expose] public section

namespace VG.Impl.Blowfish.X86.Ssse3

open VG.X86
open VG.Impl.Modes.X86 (sb argOp Core)
open VG.Impl.Modes (Mode)

/-- The internal function's name. -/
def fnName : String := "vg_blowfish_encrypt_block_ssse3"

/-- The table of constants' name. -/
def tableName : String := "VG_BLOWFISH_SSSE3"

/-- The constants, 16 bytes each (two words): the sixteen rows `C_r` (zero
at byte `r`, `0x80` elsewhere), the shuffle that gathers the bytes 0, 4, 8
and 12, then 1, 5, 9 and 13, and so on, and `0x0f` in every byte. -/
def table : List (BitVec 64) := [
  0x8080808080808000, 0x8080808080808080, 0x8080808080800080, 0x8080808080808080,
  0x8080808080008080, 0x8080808080808080, 0x8080808000808080, 0x8080808080808080,
  0x8080800080808080, 0x8080808080808080, 0x8080008080808080, 0x8080808080808080,
  0x8000808080808080, 0x8080808080808080, 0x0080808080808080, 0x8080808080808080,
  0x8080808080808080, 0x8080808080808000, 0x8080808080808080, 0x8080808080800080,
  0x8080808080808080, 0x8080808080008080, 0x8080808080808080, 0x8080808000808080,
  0x8080808080808080, 0x8080800080808080, 0x8080808080808080, 0x8080008080808080,
  0x8080808080808080, 0x8000808080808080, 0x8080808080808080, 0x0080808080808080,
  0x0d0905010c080400, 0x0f0b07030e0a0602, 0x0f0f0f0f0f0f0f0f, 0x0f0f0f0f0f0f0f0f
]

/-! ## The constants' and the working space's offsets -/

/-- The row `C_r`. -/
def oC (r : Nat) : Nat := 16 * r
/-- The shuffle. -/
def oT : Nat := 256
/-- `0x0f` in every byte. -/
def oM : Nat := 272

/-- The index vector of row `r`, in the working space. -/
def vOff (r : Nat) : Nat := 64 + 16 * r
/-- S-box `j`'s entries at the four bytes of xL. -/
def fOff (j : Nat) : Nat := 320 + 16 * j
/-- The working space's bytes. -/
def workBytes : Nat := 384

/-- The table's base register. -/
def tbr : Reg := .ebx

/-- XMM register `k`, modulo 8. -/
def xr (k : Nat) : XReg :=
  match k % 8 with
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | 3 => .xmm3 | 4 => .xmm4 | 5 => .xmm5 | 6 => .xmm6 | _ => .xmm7

/-- A constant to `d`. -/
def tb (d : XReg) (off : Nat) : Instr := .movdquTbl d (at_ tbr off) tableName table
def x (op : XBinOp) (a b : XReg) : Instr := .xop (.bin op a b)
def ld (d : XReg) (b : Reg) (off : Nat) : Instr := .movdquLoad d (at_ b off)
def stx (b : Reg) (off : Nat) (r : XReg) : Instr := .movdquStore (at_ b off) r

/-! ## A round -/

/-- `xL ^= P` for the entry at `ebp`; xL to every doubleword of `xmm0`, and
its bytes' high nibbles to `xmm1` and low nibbles to `xmm0`. -/
def head : List Instr :=
  [.alu .xor .ecx (.mem (at_ .ebp 0)), .xop (.movd .xmm0 .ecx), .xop (.pshufd .xmm0 .xmm0 0),
   tb .xmm2 oM, x .movdqa .xmm1 .xmm0, .xop (.shift .psrld .xmm1 4), x .pand .xmm1 .xmm2,
   x .pand .xmm0 .xmm2]

/-- The index vector of row `r` to the working space, through one of the
six registers the nibbles are not in. -/
def index (r : Nat) : List Instr :=
  [tb (xr (2 + r % 6)) (oC r), x .pshufb (xr (2 + r % 6)) .xmm1, x .por (xr (2 + r % 6)) .xmm0,
   stx .edi (vOff r) (xr (2 + r % 6))]

/-- Row `r` of plane `p` of S-box `j` at the row's index vector, in the
register `5r`: to the register `5r + 1 + p`, with the plane's rows before
it, in the register `5r + 4 + p` (that of row `r - 1`), ORed in. -/
def plane (j r p : Nat) : List Instr :=
  [ld (xr (5 * r + 1 + p)) .esi (planeOff j p + 16 * r), x .pshufb (xr (5 * r + 1 + p)) (xr (5 * r))] ++
    (if r = 0 then [] else [x .por (xr (5 * r + 1 + p)) (xr (5 * r + 4 + p))])

/-- Row `r` of the four planes of S-box `j`. -/
def row (j r : Nat) : List Instr :=
  [ld (xr (5 * r)) .edi (vOff r)] ++ plane j r 0 ++ plane j r 1 ++ plane j r 2 ++ plane j r 3

/-- S-box `j`'s four planes at the bytes of xL, in `xmm4` to `xmm7`. -/
def scan (j : Nat) : List Instr := (List.range 16).flatMap (row j)

/-- The planes' bytes to S-box `j`'s entries at the four bytes of xL, in the
working space. -/
def gather (j : Nat) : List Instr :=
  [x .punpckldq .xmm4 .xmm5, x .punpckldq .xmm6 .xmm7, x .punpcklqdq .xmm4 .xmm6, tb .xmm0 oT,
   x .pshufb .xmm4 .xmm0, stx .edi (fOff j) .xmm4]

/-- S-box `j` of the four bytes of xL. -/
def sbox (j : Nat) : List Instr := scan j ++ gather j

/-- F from the S-boxes' entries (S-box `j`'s at byte `3 - j` of xL), the
halves' exchange, and the next entry of P; the flags say whether it was the
sixteenth round's. -/
def tail : List Instr :=
  [.mov .eax (.mem (at_ .edi (fOff 0 + 12))), .alu .add .eax (.mem (at_ .edi (fOff 1 + 8))),
   .alu .xor .eax (.mem (at_ .edi (fOff 2 + 4))), .alu .add .eax (.mem (at_ .edi (fOff 3))),
   .alu .xor .eax (.reg .edx), .mov .edx (.reg .ecx), .mov .ecx (.reg .eax),
   .alu .add .ebp (imm 4), .mov .eax (.reg .esi), .alu .add .eax (imm (pOff + 64)),
   .alu .cmp .ebp (.reg .eax)]

/-- A round. -/
def round : List Instr :=
  head ++ (List.range 16).flatMap index ++ sbox 0 ++ sbox 1 ++ sbox 2 ++ sbox 3 ++ tail

/-- The last exchange undone, with the last two entries of P. -/
def finish : List Instr :=
  [.alu .xor .ecx (.mem (at_ .ebp 0)), .alu .xor .edx (.mem (at_ .ebp 4)), .mov .eax (.reg .ecx),
   .mov .ecx (.reg .edx), .mov .edx (.reg .eax)]

/-- The table's address, the halves and the pointer to P where the rounds
keep them. -/
def start : List Instr :=
  [.mov tbr (.reg .eax), .mov .ecx (.reg .edx), .mov .edx (.reg .ebp), .mov .ebp (.reg .esi),
   .alu .add .ebp (imm pOff)]

/-- `vg_blowfish_encrypt_block_ssse3`: the halves in `edx` and `ebp`
encrypted under the schedule at `esi`, to `ecx` and `edx`, with the working
space at `edi`. -/
def encryptBlock : Prog isa :=
  .seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1))
    (.seq (.block start) (.seq (.loop (.block round) .ne) (.block finish)))

/-! ## The modes' core -/

/-- The block's byte offset in the modes' scratch buffer. -/
def blkOff : Nat := 8

/-- The schedule's address and the buffer's block, as big-endian words. -/
def cryptHead : List Instr :=
  [.mov .esi (.mem (argOp 0)), .mov .edx (.mem (at_ sb blkOff)), .bswap .edx,
   .mov .ebp (.mem (at_ sb (blkOff + 4))), .bswap .ebp]

/-- The halves back to the buffer. -/
def cryptTail : List Instr :=
  [.bswap .ecx, .bswap .edx, .store (at_ sb blkOff) .ecx, .store (at_ sb (blkOff + 4)) .edx]

/-- The block of the core's buffer, encrypted in place. -/
def crypt : Prog isa :=
  .seq (.block cryptHead) (.seq (.call fnName encryptBlock) (.block cryptTail))

/-- The modes' core: one block at a time, encrypting. Its slots are the
block function's working space, the block in two of the slots the block
function does not write. -/
def core : Core :=
  { prepare := .block [], crypt := crypt, slots := 96, total := 106, buf := 2, G := 1, bw := 2, stack := 8 }

/-- CBC encryption that updates the chaining value. -/
def cbcEncryptChained : Prog isa := core.seq (Mode.cbcEncChained 2)

/-- OFB. -/
def ofb : Prog isa := core.seq (Mode.ofb 2)

/-- CFB64 encryption. -/
def cfbEncrypt : Prog isa := core.seq (Mode.cfbEnc 2)

/-- CFB64 decryption. -/
def cfbDecrypt : Prog isa := core.seq (Mode.cfbDec 2)

/-- CFB64 encryption of a message's last piece. -/
def cfbEncryptFinal : Prog isa := core.seqFinal (Mode.cfbEnc 2)

/-- CFB64 decryption of a message's last piece. -/
def cfbDecryptFinal : Prog isa := core.seqFinal (Mode.cfbDec 2)

/-- OFB of a message's last piece. -/
def ofbFinal : Prog isa := core.seqFinal (Mode.ofb 2)

/-! ## Key expansion -/

/-- Key expansion's block function: the halves at `ebp + 16` and `ebp + 20`
encrypted under the schedule whose address is at `esp + 12`, with the
working space at `ebp`, of which key expansion itself uses the first 64
bytes. -/
def blkKey : Prog isa :=
  .seq (.block [.mov .edx (.mem (at_ .ebp xlOff)), .mov .esi (.mem (at_ .esp 12)), .mov .edi (.reg .ebp),
      .mov .ebp (.mem (at_ .ebp xrOff))])
    (.seq (.call fnName encryptBlock)
      (.block [.mov .ebp (.reg .edi), .store (at_ .ebp xlOff) .ecx, .store (at_ .ebp xrOff) .edx]))

/-- Key expansion. -/
def expandKey : Prog isa := expandKeyWith blkKey

/-! ## The functions as emitted

Each function with its working space in a frame on the stack, which it
wipes (`withStackScratchWiped`), then its cleanup
(`Impl.Scrub.X86.scrubSel rb W ws`): of the `W` bytes of stack below `esp`
that its contract reserves, the doublewords `ws` its code may leave
different in two runs zeroed, and the registers a callee may change
cleared, so that it returns without secret residue. -/

namespace Fn

/-- The doublewords of the 456 bytes of stack below `esp` that the residue
analysis finds a mode's function may leave different in two runs: the block
function's return address and the header of the working space's frame. -/
def words : List Nat := [1, 2, 3, 4, 5, 6, 7]

/-- Those of the 412 bytes of key expansion. -/
def keyWords : List Nat := [1, 2, 3, 4, 5, 6]

/-- `Spec.Blowfish.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 456 words (Impl.StackScratch.X86.withStackScratchWiped 448 4 106 Ssse3.cbcEncryptChained)

/-- `Spec.Blowfish.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 456 words (Impl.StackScratch.X86.withStackScratchWiped 448 4 106 Ssse3.ofb)

/-- `Spec.Blowfish.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 456 words (Impl.StackScratch.X86.withStackScratchWiped 448 4 106 Ssse3.cfbEncrypt)

/-- `Spec.Blowfish.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 456 words (Impl.StackScratch.X86.withStackScratchWiped 448 4 106 Ssse3.cfbDecrypt)

/-- `Spec.Blowfish.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 456 words (Impl.StackScratch.X86.withStackScratchWiped 448 4 106 Ssse3.cfbEncryptFinal)

/-- `Spec.Blowfish.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 456 words (Impl.StackScratch.X86.withStackScratchWiped 448 4 106 Ssse3.cfbDecryptFinal)

/-- `Spec.Blowfish.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 456 words (Impl.StackScratch.X86.withStackScratchWiped 448 4 106 Ssse3.ofbFinal)

/-- `Spec.Blowfish.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 412 keyWords (Impl.StackScratch.X86.withStackScratchWiped 404 3 96 Ssse3.expandKey)

end Fn

end VG.Impl.Blowfish.X86.Ssse3
