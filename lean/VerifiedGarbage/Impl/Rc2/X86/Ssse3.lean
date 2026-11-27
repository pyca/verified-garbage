module

public import VerifiedGarbage.Impl.Rc2.X86.Stream
public import VerifiedGarbage.Impl.Rc2.Table

/-!
# RC2 key expansion on x86 (32-bit) with PITABLE read by `pshufb`

The baseline's key expansion (`Impl/Rc2/X86/ExpandKey.lean`) with another
look-up of PITABLE (`piLookup`), which reads the table, the static
`VG_RC2_PITABLE` (`Impl/Rc2/Table.lean`), as sixteen rows of sixteen bytes,
all of them at every look-up: no address and no branch depends on the index.

For the index `x` in EAX, `xmm6` holds `x`'s low nibble in byte 0 and `0x80`
in byte 1, and `xmm7` the same two bytes exchanged: `pshufb` of an even row
with `xmm6` leaves the row's byte at that nibble in byte 0 and nothing in
byte 1, and of the odd row after it with `xmm7` the other way round, so their
OR holds the two rows' bytes in its low word (`pair`). `punpcklwd` of two
pairs holds four rows' bytes (`quad`), `punpckldq` of two of those eight
(`octet`) and `punpcklqdq` of the two halves all sixteen, the byte of row `r`
in byte `r`; `pshufb` with `x`'s high nibble (`xmm5`) then leaves the table's
byte at `x` in byte 0, which goes to EAX through the 16 bytes at EDI, as the
baseline's does (`extract`).

The table's address is in EBP, which the key expansion no longer needs once
it has copied the key: `expandKey` takes it then (`tableBase`, in a frame of
four bytes), and restores ECX, the copy's counter, from the key's length.
-/

@[expose] public section

namespace VG.Impl.Rc2.X86.Ssse3

open VG.X86
open VG.Impl.Rc2 (piSym piQuads)
open VG.Impl.Rc2.X86.Stream (initWith)

/-- The table's 16 bytes at `off` (a row) into `d`; the table's address is in EBP. -/
def tb (d : XReg) (off : Nat) : Instr := .movdquTbl d (memOp .ebp off) piSym piQuads

/-- `EBX := (EAX >> 4) & 15` and `xmm5` its doubleword; `xmm6` the
doubleword `EAX & 15 | 0x80808000` and `xmm7` that rotated left by 8. -/
def start : List Instr :=
  [rr .ebx .eax, .shift .shr .ebx 4, .alu .and .ebx (.imm 15), .xop (.movd .xmm5 .ebx),
   .alu .and .eax (.imm 15), .alu .or .eax (.imm 0x80808000), .xop (.movd .xmm6 .eax),
   .shift .ror .eax 24, .xop (.movd .xmm7 .eax)]

/-- The bytes of rows `2 k` and `2 k + 1` at the index's low nibble, in bytes
0 and 1 of `d`; through `xmm0`. -/
def pair (d : XReg) (k : Nat) : List Instr :=
  [tb d (32 * k), .xop (.bin .pshufb d .xmm6),
   tb .xmm0 (32 * k + 16), .xop (.bin .pshufb .xmm0 .xmm7), .xop (.bin .por d .xmm0)]

/-- Those of rows `2 k … 2 k + 3`, in bytes 0 to 3 of `a`; through `b`. -/
def quad (a b : XReg) (k : Nat) : List Instr :=
  pair a k ++ pair b (k + 1) ++ ([.xop (.bin .punpcklwd a b)] : List Instr)

/-- Those of rows `2 k … 2 k + 7`, in bytes 0 to 7 of `a`; through `b` and `c`. -/
def octet (a b c : XReg) (k : Nat) : List Instr :=
  quad a b k ++ quad b c (k + 2) ++ ([.xop (.bin .punpckldq a b)] : List Instr)

/-- The sixteen rows' bytes at the index's low nibble in `xmm1`, and of
those the one at its high nibble in byte 0. -/
def rows : List Instr :=
  octet .xmm1 .xmm2 .xmm3 0 ++ octet .xmm2 .xmm3 .xmm4 4 ++
    ([.xop (.bin .punpcklqdq .xmm1 .xmm2), .xop (.bin .pshufb .xmm1 .xmm5)] : List Instr)

/-- Byte 0 of `xmm1` to EAX through the 16 bytes at EDI, which are kept in
`xmm7` and stored back. -/
def extract : List Instr :=
  [.movdquLoad .xmm7 (memOp .edi 0), .movdquStore (memOp .edi 0) .xmm1,
   .mov .eax (.mem (memOp .edi 0)), .movdquStore (memOp .edi 0) .xmm7, .alu .and .eax (.imm 255)]

/-- Select PITABLE[EAX & 255], with the table's address in EBP; clobbers
EAX, EBX, `xmm0`–`xmm7` and the flags, and needs the 16 bytes at EDI
readable and writable. -/
def piLookup : List Instr := start ++ rows ++ extract

/-- The table's address into EAX; ECX changes. -/
def tableBase : Prog isa := .frame (.symPush .eax piSym) (.block []) (.pop .ecx 1)

/-- `vg_rc2_expand_key_ssse3(key, key_len, effective_bits, out, scratch)`:
the baseline's function, with the table's address in EBP from the end of the
copy of the key. -/
def expandKey : Prog isa :=
  .seq (.block [.mov .eax (.mem (memOp .esp 20))])
    (.seq (.block (save ++
        ([.mov .ebp (.mem (memOp .esp 4)), .mov .esi (.mem (memOp .esp 8)),
          .mov .edi (.mem (memOp .esp 16)), imm .ecx 0] : List Instr)))
      (.seq (.loop (.block copyKey) .ne)
        (.seq tableBase
          (.seq (.block [rr .ebp .eax, rr .ecx .esi])
            (.seq (maybeFillWith piLookup) (.seq (expandReduceWith piLookup)
              (.block (([.mov .eax (.mem (memOp .esp 20))] : List Instr) ++ restore))))))))

/-- The function's name. -/
def keyName : String := "vg_rc2_expand_key_ssse3"

/-- `vg_rc2_cbc_init_ssse3`: the baseline's `init` over `expandKey`. -/
def init : Prog isa := initWith keyName expandKey

end VG.Impl.Rc2.X86.Ssse3
