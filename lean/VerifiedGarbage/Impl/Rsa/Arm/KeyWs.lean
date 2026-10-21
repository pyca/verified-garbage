module

public import VerifiedGarbage.Impl.Bignum.Arm.Select
public import VerifiedGarbage.Impl.Rsa.Arm.ShiftRight
public import VerifiedGarbage.Impl.Bignum.Arm.CompareWords

/-! # The working space of the RSA key operations on ARMv7

The key operations (`vg_rsa_crt_values` and those after it) keep their
numbers in the caller's working space, whose base is in `r8`: a header of
`hdr` bytes (slots of 32 bits at fixed offsets, the first 20 bytes those of
`Impl/Rsa/Arm/Div.lean`), then arrays of `w + 2` words of 32 bits, array `j`
at byte `hdr + j · S` with the stride `S = 4 (w + 2)` in `r7` and `w` in
`r9`. Numbers are `w` words, least significant first; the words after them
are the division's extra word and the shift's incoming word.

The operations here compute every address from `r7`, `r8` and `r9`, which
they leave alone, with `mul` (`ptr`), so their addresses and branches depend
only on them, and they run the verified word loops on the arrays:

* `sub3 o a b`: `[o] := [a] - [b]` modulo `2^(32 w)`, the borrow in `r11`.
* `sel o a b sl`: `[o] := [b]` if the slot `sl` holds 1, `[a]` if it holds 0.
* `copy o a`: `[o] := [a]`.
* `half j`: `[j] := ([j] + r11 · 2^(32 w)) / 2`, for `r11` 0 or 1.
* `eqS d a b t`: the slot `d` := 1 if `[a] = [b]`, 0 otherwise (`[t]` scratch).
-/

@[expose] public section

namespace VG.Impl.Rsa.Arm.Keys
open VG VG.Arm VG.Impl.Bignum.Arm

/-- Right-nested sequencing. -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-- The header's size in bytes: the arrays start there. -/
def hdr : Nat := 160

/-- Slots of the shared routines. -/
def sOdd : Nat := 100
def sB : Nat := 104
def sC : Nat := 108
def sT : Nat := 112

/-- `r` := the address of array `j`, `r8 + hdr + j · r7`. -/
def ptr (r : Reg) (j : Nat) : List Instr :=
  [.mov r (.imm (BitVec.ofNat 32 j)), .mul r r .r7, .dp .add r r (.reg .r8),
   .dp .add r r (.imm (BitVec.ofNat 32 hdr))]

/-- `r7 := 4 (r9 + 2)`, the stride. -/
def stride : List Instr := [.dp .add .r7 .r9 (.imm 2), .mov .r7 (.shifted .r7 .lsl 2)]

/-- `[o] := [a] - [b]`, the borrow out in `r11`. -/
def sub3 (o a b : Nat) : Prog isa :=
  .seq (.block (ptr .r0 o ++ ptr .r10 a ++ ptr .r12 b ++ [.mov .lr (.reg .r9), .mov .r11 (.imm 0)]))
    subRow

/-- `[o] := [b]` if the slot `sl` holds 1, else `[a]`. -/
def sel (o a b sl : Nat) : Prog isa :=
  .seq (.block (ptr .r0 o ++ ptr .r10 a ++ ptr .r12 b ++ [.mov .lr (.reg .r9), .ldr .r11 .r8 sl]))
    selectRow

/-- `[o] := [a]`. -/
def copy (o a : Nat) : Prog isa :=
  .seq (.block (ptr .r0 o ++ ptr .r10 a ++ ptr .r12 a ++ [.mov .lr (.reg .r9), .mov .r11 (.imm 0)]))
    selectRow

/-- `[j] := ([j] + r11 · 2^(32 w)) / 2`: `r11` stored as word `w`, then the shift. -/
def half (j : Nat) : Prog isa :=
  .seq (.block (ptr .r0 j ++ [.dp .add .r1 .r0 (.shifted .r9 .lsl 2), .str .r11 .r1 0, .mov .lr (.reg .r9)]))
    shiftRight

/-- The slot `sl` := the low bit of `[j]`. -/
def bitOf (sl j : Nat) : List Instr :=
  ptr .r0 j ++ [.ldr .r1 .r0 0, .dp .and .r1 .r1 (.imm 1), .str .r1 .r8 sl]

/-- The slot `d` := the slots `a` and `b` and'ed. -/
def andS (d a b : Nat) : List Instr :=
  [.ldr .r1 .r8 a, .ldr .r2 .r8 b, .dp .and .r1 .r1 (.reg .r2), .str .r1 .r8 d]

/-- The low word of `[j]` := 1. -/
def setOne (j : Nat) : List Instr := ptr .r0 j ++ [.mov .r1 (.imm 1), .str .r1 .r0 0]

/-- The low bit of `[j]` set. -/
def orOne (j : Nat) : List Instr :=
  ptr .r0 j ++ [.ldr .r1 .r0 0, .dp .orr .r1 .r1 (.imm 1), .str .r1 .r0 0]

/-- The low bit of `[j]` cleared. -/
def clrLow (j : Nat) : List Instr :=
  ptr .r0 j ++ [.ldr .r1 .r0 0, .dp .orr .r1 .r1 (.imm 1), .dp .eor .r1 .r1 (.imm 1), .str .r1 .r0 0]

/-- Convert the full-word comparison accumulator to the equality bit. -/
def eqNormalize : List Instr :=
  [.mov .r1 (.imm 0), .dp .sub .r1 .r1 (.reg .r2), .dp .orr .r1 .r1 (.reg .r2),
    .mov .r1 (.shifted .r1 .lsr 31), .dp .eor .r1 .r1 (.imm 1)]

/-- The slot `d` := 1 if `[a] = [b]`, else 0. Compare each word once;
`t` remains an allowed scratch array for callers of the existing contract. -/
def eqS (d a b _t : Nat) : Prog isa :=
  .seq (.block (ptr .r0 a ++ ptr .r1 b ++ [.mov .lr (.reg .r9), .mov .r2 (.imm 0)]))
    (.seq compareWords (.block (eqNormalize ++ [.str .r1 .r8 d])))

end VG.Impl.Rsa.Arm.Keys
