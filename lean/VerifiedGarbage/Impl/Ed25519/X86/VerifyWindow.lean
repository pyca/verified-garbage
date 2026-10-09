import VerifiedGarbage.Impl.Ed25519.BaseMultiples
import VerifiedGarbage.Impl.Ed25519.X86.PointTable

/-!
# Verification's equation with 4-bit windows

Verification may leak its inputs, so its scalars `S` and `k` are public. It
computes `[k]A - [S]B` with one chain of doublings (`dblOps`, `dbl-2008-hwcd`),
four per 4-bit window of the scalars (a loop, `doubleWindow`), from the top: each window adds `[a]A`
for `k`'s digit `a` from a table of `[1]A … [15]A` built at run time (byte
1024), and `[-b]B` for `S`'s digit `b` from a table of constants
(`baseMultiples`, negated, byte 3072), both with the specification's
addition. A zero digit adds nothing. The leading zero bytes of `k` above its
low 32 are skipped (`skipZero`, counting bytes in `esi`): before them the sum
is zero, which doubles to itself. The windows are then one loop
(`nibbleStep`) over the nibbles left (in `esi`, twice the bytes), from the
top, each read from the inputs: `k`'s 128, of which only the low 64 have a
nibble of `S` beside them. The equation
`[S]B = R + [k]A` holds exactly when the result equals `-R`, which the
projective comparison `pointEqual` checks.

`A` is at byte 7680 of the workspace and `R` at byte 7808, as decoded.
-/

namespace VG.Impl.Ed25519.X86

open VG.X86
open VG.Impl.X25519.X86 (sc at_)

/-- The table entry at `edx` to slots 4–7. -/
def pointFromTableQ : List Instr := workspaceCopyWords .edx .edi 0 192 32

/-- The point at byte `o` to slots 4–7. -/
def pointTableQ (o : Nat) : List Instr :=
  [.mov .edx (.reg .edi), .alu .add .edx (.imm (BitVec.ofNat 32 o))] ++ pointFromTableQ

/-- The point at byte `o` to slots 0–3. -/
def pointTableRead (o : Nat) : List Instr :=
  [.mov .edx (.reg .edi), .alu .add .edx (.imm (BitVec.ofNat 32 o))] ++ pointFromTable

/-- Slots 0–3 to the point at byte `o`. -/
def pointTableWrite (o : Nat) : List Instr :=
  [.mov .edx (.reg .edi), .alu .add .edx (.imm (BitVec.ofNat 32 o))] ++ pointToTable

/-- Doubles slots 0–3 in place with `dbl-2008-hwcd` (for `a = -1`): `A = X²`, `B = Y²`,
`C = 2Z²`, `E = 2XY`, `G = B - A`, `F = C - G`, `H = A + B`, and `X = EF`, `Y = GH`,
`Z = FG`, `T = EH`. -/
def dblOps : List FieldOp :=
  [.mul 8 0 0, .mul 9 1 1, .mul 10 2 2, .add 10 10 10, .mul 11 0 1, .add 11 11 11,
    .sub 12 9 8, .sub 13 10 12, .add 14 8 9, .mul 0 11 13, .mul 1 12 14, .mul 2 13 12,
    .mul 3 11 14]

/-- One doubling. -/
def dbl : Prog isa := fieldProg dblOps

/-- A doubling, then `2³⁰` added to `esi`. -/
def dblStep : Prog isa := .seq (fieldProg dblOps) (.block [.alu .add .esi (.imm 0x40000000)])

/-- Four doublings, in a loop counted by the top two bits of `esi` (the byte counter, below
`2³⁰`): adding `2³⁰` carries out of them the fourth time, leaving `esi` as it was. -/
def doubleWindow : Prog isa := .loop dblStep .ae

/-- `A` from byte 7680 into slots 0–3 and into the table's entry 0; the counter `esi` = 1. -/
def aTableInit : List Instr := pointTableRead 7680 ++ pointTableWrite 1024 ++ [.mov .esi (.imm 1)]

/-- Entry `esi` = entry `esi - 1` (in slots 0–3) + `A`; ZF is clear while another follows. -/
def aTableBody : Prog isa :=
  .seq (.block (pointTableQ 7680)) (.seq pointAdd (.block (tableAddr 1024 ++ pointToTable ++
    [.alu .add .esi (.imm 1), .alu .cmp .esi (.imm 15)])))

/-- Entries `j < 15` of the table at byte 1024 are `[j + 1]A`. -/
def aTable : Prog isa := .seq (.block aTableInit) (.loop aTableBody .ne)

/-- `-[i + 1]B`, affine, with `Z = 1`. -/
def negBase (i : Nat) : Spec.Ed25519.Point :=
  let m := Impl.Ed25519.baseMultiples.getD i (0, 1)
  ⟨0 - m.1, m.2, 1, 0 - m.1 * m.2⟩

/-- Entry `i` of the table at byte 3072: `-[i + 1]B`, through slots 0–3. -/
def bEntry (i : Nat) : List Instr := constPoint (negBase i) ++ pointTableWrite (3072 + 128 * i)

/-- The entries listed of the table at byte 3072. -/
def bEntries : List Nat → Prog isa
  | [] => .block []
  | i :: is => .seq (.block (bEntry i)) (bEntries is)

/-- Entries `j < 15` of the table at byte 3072 are `-[j + 1]B`. -/
def bTable : Prog isa := bEntries (List.range 15)

/-- `eax` = nibble `esi` of the input whose pointer is at `[esp + arg]`, from its byte `add`
on: the high nibble of byte `esi / 2` if `esi` is odd, and its low nibble if it is even. -/
def digitNibble (arg add : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.reg .esi), .shift .shr .eax 1, .alu .add .eax (.mem (at_ .esp arg)),
      .movzx8 .eax (at_ .eax add), .alu .test .esi (.imm 1)])
    (.ite .ne (.block [.shift .shr .eax 4]) (.block [.alu .and .eax (.imm 15)]))

/-- `edx` = entry `eax - 1` of the table at byte `o`. -/
def entryAddr (o : Nat) : List Instr :=
  [.alu .sub .eax (.imm 1), .mov .edx (.imm 128), .mul .edx, .alu .add .eax (.reg .edi),
    .alu .add .eax (.imm (BitVec.ofNat 32 o)), .mov .edx (.reg .eax)]

/-- Add entry `eax - 1` of the table at byte `o` to slots 0–3, unless `eax` is zero. -/
def addDigit (o : Nat) : Prog isa :=
  .seq (.block [.alu .test .eax (.reg .eax)])
    (.ite .ne (.seq (.block (entryAddr o ++ pointFromTableQ)) pointAdd) (.block []))

/-- `k`'s nibble `esi` (`k` is the third argument, at `[esp + 12]`), added from the table at
byte 1024. -/
def addK : Prog isa := .seq (digitNibble 12 0) (addDigit 1024)

/-- `S`'s nibble `esi` (the signature's second half, the second argument at `[esp + 8]`),
added from the table at byte 3072, if `esi` is below 64 (`S` has 32 bytes). -/
def addS : Prog isa :=
  .seq (.block [.alu .cmp .esi (.imm 64)]) (.ite .b (.seq (digitNibble 8 32) (addDigit 3072)) (.block []))

/-- A window of the nibble below `esi` (the nibbles left of the scalars): the counter moved
down, four doublings, then `k`'s nibble added and `S`'s; ZF is clear while another nibble
follows. -/
def nibbleStep : Prog isa :=
  .seq (.block [.alu .sub .esi (.imm 1)])
    (.seq doubleWindow (.seq addK (.seq addS (.block [.alu .test .esi (.reg .esi)]))))

/-- `eax` = byte `esi - 1` of `k`, and `edx = esi - 1`. -/
def skipLoad : List Instr :=
  [.mov .edx (.reg .esi), .alu .sub .edx (.imm 1), .mov .eax (.mem (at_ .esp 12)),
    .alu .add .eax (.reg .edx), .movzx8 .eax (at_ .eax 0), .alu .test .eax (.reg .eax)]

/-- Below a zero byte, the counter moves down; ZF is clear while another byte of `k` alone may
be skipped. -/
def skipBody : Prog isa :=
  .seq (.block skipLoad) (.ite .ne (.block [.alu .cmp .esi (.reg .esi)])
    (.block [.mov .esi (.reg .edx), .alu .cmp .esi (.imm 32)]))

/-- Skip the leading zero bytes of `k` above its low 32. -/
def skipZero : Prog isa := .loop skipBody .ne

/-- `-R` from byte 7808 into slots 4–7. -/
def negR : List Instr := pointTableQ 7808 ++ fieldCode [.const 8 0, .sub 4 8 4, .sub 7 8 7]

/-- `d` in slot 16. -/
def windowSetup : List Instr := fieldCode [.const 16 Spec.Ed25519.d]

/-- The sum at the identity, and the counter at all 64 bytes of `k`. -/
def windowInit : List Instr := constPoint Spec.Ed25519.identity ++ [.mov .esi (.imm 64)]

/-- The tables, and the sum at the identity. -/
def windowPrep : Prog isa := .seq (.block windowSetup) (.seq aTable (.seq bTable (.block windowInit)))

/-- `[k]A - [S]B` in slots 0–3: the nibbles left after `skipZero`, two per byte. -/
def windowMultiply : Prog isa :=
  .seq windowPrep (.seq skipZero (.seq (.block [.alu .add .esi (.reg .esi)]) (.loop nibbleStep .ne)))

end VG.Impl.Ed25519.X86
