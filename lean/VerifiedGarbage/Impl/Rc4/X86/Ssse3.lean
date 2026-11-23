module

public import VerifiedGarbage.Impl.Rc4.X86

/-!
# RC4 on x86 (32-bit) with the table's rows in XMM registers (SSSE3)

`vg_rc4_init_ssse3` and `vg_rc4_apply_ssse3`: the baseline's functions
(`Impl/Rc4/X86.lean`) with the table at `edi` visited as sixteen rows of
sixteen bytes, each loaded, changed and stored whole, where the baseline
visits it as 64 doublewords in the general registers. Every address is
public: the rows are at fixed offsets, `S[i]` is at the public index `i`,
and the constants are at fixed offsets of a table (`VG_RC4_SSSE3`).

A step, with `S[i]` in `ecx` and the secret index `j` in `ebp`:

* `head`: the index vector `X` (`xmm4`), `j`'s high nibble at the lane of
  its low nibble and `0x80` at the other lanes, and `S[i]` at that lane
  (`xmm5`), by one `pshufb` each with the vector that is zero at that lane
  only (the lanes' numbers exclusive-ored with the low nibble).
* `swapRows`: for each row `r`, its mask `pshufb(C_r, X)`, `C_r` being
  `0xff` at byte `r`: `0xff` at the lane of `j` if `j` is in the row, else
  zero; the row's bytes that change, `(row ^ S[i]) & mask`; and the row
  exclusive-ored with them, stored. So `S[j] := S[i]`, and the bytes that
  changed, ORed over the rows (`xmm3`), are `S[j] ^ S[i]` at `j`'s lane.
* `sj`: that byte out of the register (a shuffle by the low nibble, a store
  of eight bytes and a byte load), exclusive-ored with `S[i]`: `S[j]`.

`S[i] := S[j]` is a byte store at the public index. The stream function then
reads `S[S[i] + S[j]]` (`readRows`): each row's byte at the index's low
nibble into the next lane of a column (`pshufb`, `palignr`), and the
column's byte at the high nibble.

The rows' temporaries are two pairs of registers in turn, a row's loads go
to registers last written two rows before, and the head writes no register
that the second pass writes: a write of a whole XMM register by these
instructions waits for the register's old value where the upper halves of
the registers are not known to be zero.

The working space is the baseline's `scratch` (64 bytes): our caller's
registers in its first 16 bytes, eight bytes for a byte out of a register
at 16, `S[i]` at 24 and the constants' address at 28.
-/

@[expose] public section

namespace VG.Impl.Rc4.X86.Ssse3

open VG.X86
open VG.Impl.Rc4.X86 (at_ imm save restore entry start finish)

/-- The table of constants' name. -/
def tableName : String := "VG_RC4_SSSE3"

/-- The constants, 16 bytes each (two words): `C_r` for each row `r` (`0xff`
at byte `r`), the identity permutation's sixteen rows, and the row that is
zero at byte 0 and `0x80` elsewhere. -/
def table : List (BitVec 64) := [
  0x00000000000000ff, 0x0000000000000000, 0x000000000000ff00, 0x0000000000000000,
  0x0000000000ff0000, 0x0000000000000000, 0x00000000ff000000, 0x0000000000000000,
  0x000000ff00000000, 0x0000000000000000, 0x0000ff0000000000, 0x0000000000000000,
  0x00ff000000000000, 0x0000000000000000, 0xff00000000000000, 0x0000000000000000,
  0x0000000000000000, 0x00000000000000ff, 0x0000000000000000, 0x000000000000ff00,
  0x0000000000000000, 0x0000000000ff0000, 0x0000000000000000, 0x00000000ff000000,
  0x0000000000000000, 0x000000ff00000000, 0x0000000000000000, 0x0000ff0000000000,
  0x0000000000000000, 0x00ff000000000000, 0x0000000000000000, 0xff00000000000000,
  0x0706050403020100, 0x0f0e0d0c0b0a0908, 0x1716151413121110, 0x1f1e1d1c1b1a1918,
  0x2726252423222120, 0x2f2e2d2c2b2a2928, 0x3736353433323130, 0x3f3e3d3c3b3a3938,
  0x4746454443424140, 0x4f4e4d4c4b4a4948, 0x5756555453525150, 0x5f5e5d5c5b5a5958,
  0x6766656463626160, 0x6f6e6d6c6b6a6968, 0x7776757473727170, 0x7f7e7d7c7b7a7978,
  0x8786858483828180, 0x8f8e8d8c8b8a8988, 0x9796959493929190, 0x9f9e9d9c9b9a9998,
  0xa7a6a5a4a3a2a1a0, 0xafaeadacabaaa9a8, 0xb7b6b5b4b3b2b1b0, 0xbfbebdbcbbbab9b8,
  0xc7c6c5c4c3c2c1c0, 0xcfcecdcccbcac9c8, 0xd7d6d5d4d3d2d1d0, 0xdfdedddcdbdad9d8,
  0xe7e6e5e4e3e2e1e0, 0xefeeedecebeae9e8, 0xf7f6f5f4f3f2f1f0, 0xfffefdfcfbfaf9f8,
  0x8080808080808000, 0x8080808080808080, 0x8080808080808080, 0x8080808080808080
]

/-- `C_r`. -/
def oC (r : Nat) : Nat := 16 * r
/-- Row `r` of the identity permutation. -/
def oI (r : Nat) : Nat := 256 + 16 * r
/-- Zero at byte 0 and `0x80` elsewhere. -/
def oT : Nat := 512
/-- `0x80` at every byte. -/
def oH : Nat := 528

/-- The working space's offsets: the eight bytes for a byte out of a
register, `S[i]`, and the constants' address. -/
def sSlot : Nat := 16
def sSi : Nat := 24
def sTab : Nat := 28
/-- The stream function's: `S[j]`, the next `S[i]`, and the index of the keystream byte. -/
def sSj : Nat := 32
def sNext : Nat := 36
def sT : Nat := 40

/-- The register of the constants' address. -/
def tbr : Reg := .edx

def tb (d : XReg) (off : Nat) : Instr := .movdquTbl d (at_ tbr off) tableName table
def x (op : XBinOp) (a b : XReg) : Instr := .xop (.bin op a b)
def ld (d : XReg) (off : Nat) : Instr := .movdquLoad d (at_ .edi off)
def stx (off : Nat) (r : XReg) : Instr := .movdquStore (at_ .edi off) r

/-- `xmm4` := `X`, `xmm5` := `S[i]` (`ecx`) at the lane of `j`'s (`ebp`) low
nibble. Clobbers `eax`, `xmm0` and `xmm1`. -/
def head : List Instr :=
  [.mov .eax (.reg .ebp), .alu .and .eax (imm 15), .xop (.movd .xmm0 .eax), x .pxor .xmm1 .xmm1,
   x .pshufb .xmm0 .xmm1, tb .xmm1 (oI 0), x .pxor .xmm1 .xmm0, .xop (.movd .xmm5 .ecx), x .pshufb .xmm5 .xmm1,
   tb .xmm4 oT, .mov .eax (.reg .ebp), .shift .shr .eax 4, .xop (.movd .xmm0 .eax), x .por .xmm4 .xmm0,
   x .pshufb .xmm4 .xmm1]

/-- A row's mask, the bytes that change, and the row stored: the mask and
then the row in `m`, the bytes that change in `a`. -/
def swapRow (m a : XReg) (r : Nat) : List Instr :=
  [tb m (oC r), x .pshufb m .xmm4, ld a (16 * r), x .pxor a .xmm5, x .pand a m, ld m (16 * r), x .pxor m a,
   stx (16 * r) m]

/-- The rows `2p` and `2p + 1`, and their changed bytes into `xmm3`. -/
def swapPair (p : Nat) : List Instr :=
  swapRow .xmm0 .xmm1 (2 * p) ++ swapRow .xmm2 .xmm6 (2 * p + 1) ++
    [x .por .xmm6 .xmm1, if p = 0 then x .movdqa .xmm3 .xmm6 else x .por .xmm3 .xmm6]

/-- `S[j] := S[i]`, and `xmm3` := `S[j] ^ S[i]` at the lane of `j`'s low nibble. -/
def swapRows : List Instr := (List.range 8).flatMap swapPair

/-- `eax` := the old `S[j]`, with the working space's address in `edx`.
Clobbers `xmm3` and `xmm7`. -/
def sj : List Instr :=
  [.mov .eax (.reg .ebp), .alu .and .eax (imm 15), .xop (.movd .xmm7 .eax), x .pshufb .xmm3 .xmm7,
   .mov .edx (.mem (at_ .esp 16)), .movqStore (at_ .edx sSlot) .xmm3, .movzx8 .eax (at_ .edx sSlot),
   .alu .xor .eax (.mem (at_ .edx sSi))]

/-! ## The stream function's passes

The stream function knows both bytes of an exchange before it: `S[i]` is
read at the public index, and `S[j]` by the second pass of the iteration
before, which reads two columns, for the keystream byte and for the next
`j`. -/

/-- The registers of the first pass, in turn: a row's mask, and the row. -/
def maskReg (r : Nat) : XReg := if r % 3 = 0 then .xmm0 else if r % 3 = 1 then .xmm2 else .xmm3
def rowReg (r : Nat) : XReg := if r % 3 = 0 then .xmm1 else if r % 3 = 1 then .xmm6 else .xmm7

/-- A row exclusive-ored with `xmm5` under its mask: the byte `j` takes the
difference in `xmm5`'s lane. -/
def xorRow (r : Nat) : List Instr :=
  [tb (maskReg r) (oC r), x .pshufb (maskReg r) .xmm4, x .pand (maskReg r) .xmm5, ld (rowReg r) (16 * r),
   x .pxor (rowReg r) (maskReg r), stx (16 * r) (rowReg r)]

def xorRows : List Instr := (List.range 16).flatMap xorRow

/-- The registers of a half's columns, in turn. -/
def colReg (h k : Nat) : XReg :=
  if h = 0 then (if k % 3 = 0 then .xmm0 else if k % 3 = 1 then .xmm1 else .xmm2)
  else (if k % 3 = 0 then .xmm3 else if k % 3 = 1 then .xmm6 else .xmm4)

/-- A row's bytes at the two low nibbles in `xmm7`'s bytes 0 and 1, into
the columns of its half. -/
def readRow2 (h k : Nat) : List Instr :=
  [ld (colReg h k) (16 * (8 * h + k)), x .pshufb (colReg h k) .xmm7,
   .xop (.palignr (colReg h k) (colReg h (k + 2)) 2)]

/-- The eight rows of a half: `colReg h 7` := their bytes at the two low
nibbles, a row's two bytes after another's. -/
def readHalf (h : Nat) : List Instr := (List.range 8).flatMap (readRow2 h)

/-- The next `S[i]` to its slot: the table's byte at `i + 1`, or `S[i]` if
the exchange to come puts it there (`j = i + 1`). `edx` := the working
space. -/
def nextSi : List Instr :=
  [.mov .ecx (.reg .esi), .alu .add .ecx (imm 1), .alu .and .ecx (imm 255),
   .mov .eax (.reg .edi), .alu .add .eax (.reg .ecx), .movzx8 .eax (at_ .eax 0),
   .alu .xor .ecx (.reg .ebp), .alu .sub .ecx (imm 1), .alu .sbb .ecx (.reg .ecx),
   .mov .edx (.mem (at_ .esp 16)), .store (at_ .edx sNext) .eax, .alu .xor .eax (.mem (at_ .edx sSi)),
   .alu .and .eax (.reg .ecx), .alu .xor .eax (.mem (at_ .edx sNext)), .store (at_ .edx sNext) .eax]

/-- `ecx` := `S[i] ^ S[j]`, the constants' address to `edx`, and the row of
the public `i` exclusive-ored with that difference at `i`'s lane. -/
def iRow : List Instr :=
  [.mov .ecx (.mem (at_ .edx sSj)), .alu .xor .ecx (.mem (at_ .edx sSi)), .mov .edx (.mem (at_ .edx sTab)),
   .xop (.movd .xmm7 .ecx), .mov .eax (.reg .esi), .alu .and .eax (imm 15), .xop (.movd .xmm0 .eax),
   x .pxor .xmm1 .xmm1, x .pshufb .xmm0 .xmm1, tb .xmm1 (oI 0), x .pxor .xmm1 .xmm0, x .pshufb .xmm7 .xmm1,
   .mov .eax (.reg .esi), .alu .and .eax (imm 240), .alu .add .eax (.reg .edi),
   .movdquLoad .xmm3 (at_ .eax 0), x .pxor .xmm3 .xmm7, .movdquStore (at_ .eax 0) .xmm3]

/-- The index of the keystream byte to `eax`, and the next `i`, `S[i]` and
`j`. -/
def advance : List Instr :=
  [.mov .edx (.mem (at_ .esp 16)), .mov .eax (.mem (at_ .edx sSj)), .alu .add .eax (.mem (at_ .edx sSi)),
   .alu .and .eax (imm 255), .alu .add .esi (imm 1), .alu .and .esi (imm 255),
   .mov .ecx (.mem (at_ .edx sNext)), .store (at_ .edx sSi) .ecx, .alu .add .ebp (.reg .ecx),
   .alu .and .ebp (imm 255)]

/-- The second pass: `eax` := the table's byte at `eax`, and the table's
byte at `ebp` to its slot, with the working space's address in `edx`. -/
def read2 : List Instr :=
  ([.store (at_ .edx sT) .eax, .mov .ecx (.reg .ebp), .alu .and .ecx (imm 15), .shift .ror .ecx 24,
    .alu .and .eax (imm 15), .alu .or .eax (.reg .ecx), .xop (.movd .xmm7 .eax)] : List Instr) ++
    readHalf 0 ++ readHalf 1 ++
  ([.mov .eax (.mem (at_ .edx sT)), .mov .ecx (.reg .eax), .shift .shr .ecx 3, .alu .and .ecx (imm 14),
    .alu .and .eax (imm 128), .alu .or .eax (.reg .ecx), .store (at_ .edx sT) .eax,
    .mov .eax (.reg .ebp), .mov .ecx (.reg .eax), .shift .shr .ecx 3, .alu .and .ecx (imm 14),
    .alu .and .eax (imm 128), .alu .or .eax (.reg .ecx), .alu .or .eax (imm 1), .shift .ror .eax 24,
    .alu .or .eax (.mem (at_ .edx sT)), .xop (.movd .xmm7 .eax),
    x .pshufb .xmm1 .xmm7, .mov .eax (.reg .edx), .mov .edx (.mem (at_ .eax sTab)), tb .xmm5 oH,
    x .pxor .xmm7 .xmm5, x .pshufb .xmm6 .xmm7, x .por .xmm1 .xmm6, .movqStore (at_ .eax sSlot) .xmm1,
    .movzx8 .ecx (at_ .eax (sSlot + 1)), .store (at_ .eax sSj) .ecx, .movzx8 .eax (at_ .eax sSlot)] : List Instr)

/-- `S[i]` (`esi`) to `ecx` and to its slot, and the constants' address to `edx`. -/
def loadSi : List Instr :=
  [.mov .eax (.reg .edi), .alu .add .eax (.reg .esi), .movzx8 .ecx (at_ .eax 0),
   .mov .eax (.mem (at_ .esp 16)), .store (at_ .eax sSi) .ecx, .mov .edx (.mem (at_ .eax sTab))]

/-! ## Initialization: `vg_rc4_init(key, key_len, ctx, scratch)` -/

/-- A row of the identity permutation. -/
def identityRow (r : Nat) : List Instr := [tb .xmm0 (oI r), stx (16 * r) .xmm0]

/-- `j += S[i] + key[off]`, the swap, the next key offset and `i`, as the
baseline's `scheduleStep`. -/
def scheduleStep : List Instr :=
  loadSi ++ ([.alu .add .ebp (.reg .ecx), .mov .eax (.mem (at_ .esp 4)), .alu .add .eax (.reg .ebx),
    .movzx8 .eax (at_ .eax 0), .alu .add .ebp (.reg .eax), .alu .and .ebp (imm 255)] : List Instr) ++
    head ++ swapRows ++ sj ++
    ([.alu .add .ebx (imm 1), .mov .edx (.mem (at_ .esp 8)), .alu .cmp .ebx (.reg .edx),
      .mov .edx (imm 0), .alu .sbb .edx (.reg .edx), .alu .and .ebx (.reg .edx),
      .mov .edx (.reg .edi), .alu .add .edx (.reg .esi), .store8 (at_ .edx 0) .al,
      .alu .add .esi (imm 1), .alu .cmp .esi (imm 256)] : List Instr)

/-- The constants' address to its slot and to `edx`, after `symPush` took it into `eax`. -/
def keepTable : List Instr :=
  [.mov .ecx (.mem (at_ .esp 16)), .store (at_ .ecx sTab) .eax, .mov .edx (.reg .eax)]

/-- Key scheduling after the key-length check. -/
def initValid : Prog isa :=
  .seq (.block (save ++ ([.mov .edi (.mem (at_ .esp 12))] : List Instr)))
    (.seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1))
      (.seq (.block (keepTable ++ (List.range 16).flatMap identityRow ++
          ([.mov .esi (imm 0), .mov .ebx (imm 0), .mov .ebp (imm 0)] : List Instr)))
        (.seq (.loop (.block scheduleStep) .ne)
          (.block (([.mov .eax (imm 0), .store8 (at_ .edi 256) .al, .store8 (at_ .edi 257) .al] :
            List Instr) ++ restore)))))

/-- Checked key scheduling, as the baseline's. -/
def init : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .esp 8)), .alu .sub .eax (imm 1), .alu .cmp .eax (imm 256)])
    (.ite .ae (.block [.mov .eax (imm 1)]) initValid)

/-! ## The stream function: `vg_rc4_apply(ctx, data, len, scratch)` -/

/-- The first `i`, `S[i]`, `j` and `S[j]`, before the loop. -/
def first : List Instr :=
  ([.alu .add .esi (imm 1), .alu .and .esi (imm 255)] : List Instr) ++ loadSi ++
    ([.alu .add .ebp (.reg .ecx), .alu .and .ebp (imm 255), .mov .edx (.mem (at_ .esp 16)),
      .mov .eax (imm 0)] : List Instr) ++ read2

/-- One byte: the exchange at `i` (`esi`) and `j` (`ebp`), whose bytes are
in their slots; the next `i`, `S[i]` and `j`; then the keystream byte
`S[S[i] + S[j]]`, exclusive-ored into data byte `ebx`, with the next `S[j]`. -/
def applyStep : List Instr :=
  nextSi ++ iRow ++ head ++ xorRows ++ advance ++ read2 ++
    ([.mov .ecx (.mem (at_ .esp 8)), .alu .add .ecx (.reg .ebx), .movzx8 .edx (at_ .ecx 0),
      .alu .xor .edx (.reg .eax), .store8 (at_ .ecx 0) .dl,
      .alu .add .ebx (imm 1), .mov .edx (.mem (at_ .esp 12)), .alu .cmp .ebx (.reg .edx)] : List Instr)

/-- The indices of the last exchange, from the next ones. -/
def last : List Instr :=
  [.alu .sub .esi (imm 1), .alu .and .esi (imm 255), .mov .edx (.mem (at_ .esp 16)),
   .alu .sub .ebp (.mem (at_ .edx sSi)), .alu .and .ebp (imm 255)]

/-- The stream function after its entry, for data that is not empty. -/
def applyRest : Prog isa :=
  .seq (.block (save ++ start))
    (.seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1))
      (.seq (.block (keepTable ++ first))
        (.seq (.loop (.block applyStep) .ne) (.block (last ++ finish ++ restore)))))

/-- Streaming XOR, as the baseline's `apply`: `i` is loaded first (`entry`). -/
def apply : Prog isa := .seq (.block entry) (.ite .e (.block []) applyRest)

/-! ## The functions as emitted

Each function with its working space in a frame on the stack
(`withStackScratch`), then its cleanup (`Impl.Scrub.X86.scrubAll rb W`). -/

namespace Fn

/-- `Spec.Rc4.initApi`'s function as emitted. -/
def init : Prog isa :=
  Impl.Scrub.X86.scrubAll 32 92 (Impl.StackScratch.X86.withStackScratch 88 3 Ssse3.init)

/-- `Spec.Rc4.applyApi`'s function as emitted. -/
def apply : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 92 (Impl.StackScratch.X86.withStackScratch 88 3 Ssse3.apply)

end Fn

end VG.Impl.Rc4.X86.Ssse3
