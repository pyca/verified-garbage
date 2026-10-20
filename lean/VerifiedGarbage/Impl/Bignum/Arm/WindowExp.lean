module

public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Impl.Bignum.Arm.SelectArray

/-!
# Private RSA exponentiation by fixed windows of three bits

The table `T[j] = x^j R mod M` (`j < 8`, `R = 2^(64 w)`) is in arrays 8 to 15
of the workspace, after the RSA layout's eight (`arrAt w (8 + j)`), so the
workspace must be at least `arrAt w 16` bytes. The exponent's bits are read
most significant first: each squares the running power (array 6) and joins
the pending digit, and after every third the power is multiplied by
`T[digit]`. A pass over the whole table selects that entry into array 1,
each entry copied under a mask that is set for the digit's alone, so that no
address or branch depends on the digit. The pending bits of a last, shorter
window are applied by one more product at the end (by `T[0] = R mod M` when
there are none). Every bit costs a square and a third of a product, where
reading the exponent a bit at a time costs a square and a product.

Header bytes: 192 the bits left in the byte and 200 the byte, shifted
(`Exp.lean`'s); 196 the pending digit, 204 the count of pending bits; 220 the
table entry and 228 its index, while the table is built or scanned.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

/-! ## The table -/

/-- `r12 :=` the table's first entry, after array 7 (the header's array 7
address plus the stride `8 (w + 2)`), with `r1` the stride. -/
def tableStart : List Instr :=
  [.ldr .r12 .r0 120, .ldr .r1 .r0 48, .dp .add .r1 .r1 (.imm 2), .mov .r1 (.shifted .r1 .lsl 3),
   .dp .add .r12 .r12 (.reg .r1)]

/-- The entry at 220 and its index at 228 move to the next; Z after the last. -/
def entryNext : List Instr :=
  [.ldr .r1 .r0 220, .ldr .r2 .r0 48, .dp .add .r2 .r2 (.imm 2), .dp .add .r1 .r1 (.shifted .r2 .lsl 3),
   .str .r1 .r0 220, .ldr .r1 .r0 228, .dp .add .r1 .r1 (.imm 1), .str .r1 .r0 228,
   .cmp .r1 (.imm 8)]

/-- Copy array `a` to the entry at 220: `selectRow` in place with the bit set. -/
def entryCopyArgs (a : Nat) : List Instr :=
  [.mov .r11 (.imm 1), .ldr .r12 .r0 (64 + 8 * a), .ldr .lr .r0 48, .dp .add .lr .lr (.reg .lr),
   .ldr .r0 .r0 220, .mov .r10 (.reg .r0)]

def entryCopy (a : Nat) : Prog isa :=
  .seq (.block (entryCopyArgs a)) (.seq selectRow (.block [.ldrSp .r0 0]))

/-- The first entry and index 0. -/
def tableInit : List Instr := tableStart ++ [.str .r12 .r0 220, .mov .r1 (.imm 0), .str .r1 .r0 228]

/-- `T[j] := [1] := [1] · x R`, for `j` from 2 to 7. -/
def tableBody : Prog isa := .seq (montOp 1 1 5) (.seq (entryCopy 1) (.block entryNext))

/-- `T[0] := R mod M` (array 6), `T[1] := x R` (array 5), array 1 `:= x R`,
then the other six entries. -/
def tableBuild : Prog isa :=
  .seq (.block tableInit) (.seq (entryCopy 6) (.seq (.block entryNext) (.seq (entryCopy 5)
    (.seq (.block entryNext) (.seq (.block [.mov .r11 (.imm 1)]) (.seq (selectArray 1 1 5)
      (.loop tableBody .ne)))))))

/-! ## The selection of `T[digit]` -/

/-- Entry 0 and index 0. -/
def scanInit : List Instr := tableInit

/-- The mask bit of the entry at index `j` (228) for the digit `d` (196):
`((d ^ j) - 1) >> 31`, one when they are equal (both are below 8). -/
def scanBit : List Instr :=
  [.ldr .r1 .r0 196, .ldr .r2 .r0 228, .dp .eor .r11 .r1 (.reg .r2), .dp .sub .r11 .r11 (.imm 1),
   .mov .r11 (.shifted .r11 .lsr 31)]

/-- Array 1 in place, or the entry at 220, under the bit: `2 w` words. -/
def scanArgs : List Instr :=
  [.ldr .r10 .r0 72, .ldr .r12 .r0 220, .ldr .lr .r0 48, .dp .add .lr .lr (.reg .lr), .ldr .r0 .r0 72]

def scanBody : Prog isa :=
  .seq (.block (scanBit ++ scanArgs)) (.seq selectRow (.seq (.block [.ldrSp .r0 0]) (.block entryNext)))

/-- Array 1 `:= T[d]`, every entry read. -/
def scan : Prog isa := .seq (.block scanInit) (.loop scanBody .ne)

/-! ## The exponent -/

/-- No pending bits. -/
def windowReset : List Instr := [.mov .r1 (.imm 0), .str .r1 .r0 196, .str .r1 .r0 204]

/-- The power times `T[d]`, and no pending bits. -/
def windowApply : Prog isa := .seq scan (.seq (montOp 6 6 1) (.block windowReset))

/-- Bit 7 of the shifted byte joins the pending digit, `d := 2 d + bit`, and
the count of pending bits; Z when it is three. -/
def windowBitValue : List Instr :=
  [.ldr .r1 .r0 200, .mov .r1 (.shifted .r1 .lsr 7), .dp .and .r1 .r1 (.imm 1),
   .ldr .r2 .r0 196, .dp .add .r2 .r1 (.shifted .r2 .lsl 1), .str .r2 .r0 196,
   .ldr .r1 .r0 204, .dp .add .r1 .r1 (.imm 1), .str .r1 .r0 204, .cmp .r1 (.imm 3)]

/-- One exponent bit: square, join the digit, apply a full window. -/
def windowBit : Prog isa :=
  .seq (squareOp 6 6) (.seq (.block windowBitValue) (.ite .eq windowApply (.block [])))

def windowRound : Prog isa := .seq windowBit (.seq (.block expShift) (.block expDecrement))
def windowBits : Prog isa := .loop windowRound .ne
def windowBytes : Prog isa := .loop (.seq expByteHead (.seq windowBits (.block expByteNext))) .ne

/-- Encode the input and build the table, scan the exponent bytes, apply the
last window, then convert back to ordinary form. -/
def windowExpPhase : Prog isa :=
  .seq expInit (.seq tableBuild (.seq (.block windowReset) (.seq windowBytes
    (.seq windowApply (montOp 6 6 7)))))

end VG.Impl.Bignum.Arm
