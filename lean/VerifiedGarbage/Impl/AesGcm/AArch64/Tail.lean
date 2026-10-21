module

public import VerifiedGarbage.Impl.AesGcm.AArch64
public import VerifiedGarbage.Impl.Gcm.AArch64.Pmull

/-!
# AES-GCM on AArch64: the last bytes of a text of at least a block

On the path for TLS records (`Fast`, `Stitch`), a text's last `r < 16`
bytes were XORed with their keystream eight, four, two and one at a time,
and copied into `T`, zeroed by two 8-byte stores, to be absorbed by a
16-byte load (`padMul`): a load the stores before it cannot forward to. When
the whole text (of `x26` bytes) is at least a block long, its last 16 bytes
are in the buffer, `16 - r` of them already done, and these take their
place:

* `cryptAlT`: `cryptAl`, its keystream block zeroed by one 16-byte store
  (`crSeg2T`), and the last bytes (`ksTail`) XORed with the keystream block
  moved up by `16 - r` bytes (`tbl` with the indices `i - (16 - r)`, which
  are 16 or more, and so read as zeros, below `16 - r`) into the 16 bytes
  that end the text, loaded and stored back whole: the bytes before the last
  `r` are stored as they were;
* `Fast.padMulT`: `padMul`, the last bytes (`padVec`) moved down from the 16 that
  end the text into the bytes of a block padded with zeros, as `loadRev`
  leaves a block (`tbl` with the indices `rev64(i) + 16 - r`, 16 or more
  past the last bytes), and absorbed from the register.

The indices come from a table of two vectors (`VG_GCM_TAIL_IDX`, `ldrqTbl`)
and `16 - r`, which depends only on the length; texts shorter than a block
keep the code of before.
-/

@[expose] public section

namespace VG.Impl.AesGcm.AArch64.Tail

open VG.AArch64
open VG.Impl.AesGcm.AArch64
open VG.Impl.Gcm.AArch64.Pmull (A T Y mul tReg sReg)

/-- The name of the table of indices. -/
def idxName : String := "VG_GCM_TAIL_IDX"

/-- The bytes `0, 1, …, 15`, then the same with each doubleword's bytes
reversed (`rev64`): `7, 6, …, 0, 15, 14, …, 8`. -/
def idxTable : List (BitVec 64) :=
  [0x0706050403020100#64, 0x0f0e0d0c0b0a0908#64, 0x0001020304050607#64, 0x08090a0b0c0d0e0f#64]

/-- `x9 = 16 - x` in every byte of `d`, and the table's address in `t`. -/
def shift (x : Reg) (d : VReg) (t : Reg) : List Instr :=
  [imm .x9 16, .sub .x .x9 .x9 x, .vop (.dup .b16 d .x9), .adrSym t idxName]

/-- The last `x24` bytes, ending the text at `x23 + x24`, XORed with the
keystream block at `x20 + 64` moved up by `16 - x24` bytes. -/
def ksTail : List Instr :=
  shift .x24 .v1 .x10 ++
  [.ldrqTbl .v0 .x10 0 idxName idxTable, .vop (.sub .b16 .v0 .v0 .v1),
   .ldrq .v2 .x20 64, .vop (.tbl .v2 .v2 .v0),
   .sub .x .x10 .x23 .x9, .ldrq .v3 .x10 0, .vop (.logic .eor .v3 .v3 .v2), .strq .v3 .x10 0]

/-- The `x13` (1 to 15) bytes at `x12`, ending the text, padded with zeros as
`loadRev` leaves a block, and absorbed. -/
def padVec : List Instr :=
  shift .x13 A .x11 ++
  [.ldrqTbl T .x11 16 idxName idxTable, .vop (.add .b16 T T A),
   .sub .x .x11 .x12 .x9, .ldrq A .x11 0, .vop (.tbl A A T),
   .vop (.logic .eor A A Y)] ++ mul Y A (sReg 1) (tReg 1)

variable (c : Callees)

/-- `crSeg2`, the keystream block zeroed by one 16-byte store. -/
def crSeg2T : Prog isa :=
  .seq (.ite (.zero .x .x24) (.block [imm .x4 0])
      (.block [imm .x4 1, .vop (.movi0 .v0), .strq .v0 .x20 64]))
    (.block (ctrArgs ++ [ptr .x3 .x20 64]))

/-- Nothing if there are no last bytes; else `crTail`, or `ksTail` if the
text is at least a block long. -/
def crTailT : Prog isa :=
  .ite (.zero .x .x24) (.block [])
    (.seq (.block [.lsr .x .x9 .x26 4]) (.ite (.zero .x .x9) crTail (.block ksTail)))

/-- `cryptAl` with `crSeg2T` and `crTailT`. -/
def cryptAlT : Prog isa :=
  .seq (.block crArgs) (.seq (ctrCall c) (.seq crSeg2T (.seq (ctrCall c) crTailT)))

end VG.Impl.AesGcm.AArch64.Tail
