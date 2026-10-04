import VerifiedGarbage.Impl.Ed25519.BaseMultiples
import VerifiedGarbage.Impl.Ed25519.X86.PointTable

/-!
# Verification's equation with 4-bit windows

Verification may leak its inputs, so its scalars `S` and `k` are public. It
computes `[k]A - [S]B` with one chain of doublings (`dblOps`, `dbl-2008-hwcd`),
four per 4-bit window of the scalars, from the top: each window adds `[a]A`
for `k`'s digit `a` from a table of `[1]A … [15]A` built at run time (byte
1024), and `[-b]B` for `S`'s digit `b` from a table of constants
(`baseMultiples`, negated, byte 3072), both with the specification's
addition. A zero digit adds nothing. The digits are read from the inputs, byte
by byte (the counter `esi` is the number of bytes left), high nibble first:
`k`'s 64 bytes, of which only the low 32 have a byte of `S` beside them. The
leading zero bytes of `k` above its low 32 are skipped (`skipZero`): before
them the sum is zero, which doubles to itself. The equation
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
def dbl : Prog isa := .block (fieldCode dblOps)

/-- Four doublings. -/
def doubleWindow : Prog isa := .seq dbl (.seq dbl (.seq dbl dbl))

/-- `A` from byte 7680 into slots 0–3 and into the table's entry 0; the counter `esi` = 1. -/
def aTableInit : List Instr := pointTableRead 7680 ++ pointTableWrite 1024 ++ [.mov .esi (.imm 1)]

/-- Entry `esi` = entry `esi - 1` (in slots 0–3) + `A`; ZF is clear while another follows. -/
def aTableBody : List Instr :=
  pointTableQ 7680 ++ pointAdd ++ tableAddr 1024 ++ pointToTable ++
    [.alu .add .esi (.imm 1), .alu .cmp .esi (.imm 15)]

/-- Entries `j < 15` of the table at byte 1024 are `[j + 1]A`. -/
def aTable : Prog isa := .seq (.block aTableInit) (.loop (.block aTableBody) .ne)

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

/-- `eax` = byte `esi + add` of the input whose pointer is at `[esp + arg]`. -/
def digitByte (arg add : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esp arg)), .alu .add .eax (.reg .esi), .movzx8 .eax (at_ .eax add)]

/-- The byte's high nibble. -/
def digitHigh (arg add : Nat) : List Instr := digitByte arg add ++ [.shift .shr .eax 4]

/-- The byte's low nibble. -/
def digitLow (arg add : Nat) : List Instr :=
  digitByte arg add ++ [.alu .and .eax (.imm 15)]

/-- `edx` = entry `eax - 1` of the table at byte `o`. -/
def entryAddr (o : Nat) : List Instr :=
  [.alu .sub .eax (.imm 1), .mov .edx (.imm 128), .mul .edx, .alu .add .eax (.reg .edi),
    .alu .add .eax (.imm (BitVec.ofNat 32 o)), .mov .edx (.reg .eax)]

/-- Add entry `eax - 1` of the table at byte `o` to slots 0–3, unless `eax` is zero. -/
def addDigit (o : Nat) : Prog isa :=
  .seq (.block [.alu .test .eax (.reg .eax)])
    (.ite .ne (.block (entryAddr o ++ pointFromTableQ ++ pointAdd)) (.block []))

/-- Four doublings, then the digit computed by `digit` added from the table at byte `o`. -/
def windowWith (o : Nat) (digit : List Instr) : Prog isa :=
  .seq doubleWindow (.seq (.block digit) (addDigit o))

/-- A window of `k` alone (`k` is the third argument, at `[esp + 12]`). -/
def windowA (digit : List Instr) : Prog isa := windowWith 1024 digit

/-- A window of `k` and of `S` (the signature's second half, the second argument at
`[esp + 8]`): the doublings, `k`'s digit, then `S`'s. -/
def windowAB (digitA digitB : List Instr) : Prog isa :=
  .seq (windowA digitA) (.seq (.block digitB) (addDigit 3072))

/-- A byte of `k` alone (bytes 63 down to 32); ZF is clear while another follows. -/
def byteStepA : Prog isa :=
  .seq (.block [.alu .sub .esi (.imm 1)]) (.seq (windowA (digitHigh 12 0))
    (.seq (windowA (digitLow 12 0)) (.block [.alu .cmp .esi (.imm 32)])))

/-- A byte of `k` and of `S` (bytes 31 down to 0); ZF is clear while another follows. -/
def byteStepAB : Prog isa :=
  .seq (.block [.alu .sub .esi (.imm 1)]) (.seq (windowAB (digitHigh 12 0) (digitHigh 8 32))
    (.seq (windowAB (digitLow 12 0) (digitLow 8 32)) (.block [.alu .test .esi (.reg .esi)])))

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

/-- The bytes of `k` alone that are left after `skipZero`. -/
def windowsA : Prog isa :=
  .seq (.block [.alu .cmp .esi (.imm 32)]) (.ite .ne (.loop byteStepA .ne) (.block []))

/-- `-R` from byte 7808 into slots 4–7. -/
def negR : List Instr := pointTableQ 7808 ++ fieldCode [.const 8 0, .sub 4 8 4, .sub 7 8 7]

/-- `d` in slot 16. -/
def windowSetup : List Instr := fieldCode [.const 16 Spec.Ed25519.d]

/-- The sum at the identity, and the counter at all 64 bytes of `k`. -/
def windowInit : List Instr := constPoint Spec.Ed25519.identity ++ [.mov .esi (.imm 64)]

/-- The tables, and the sum at the identity. -/
def windowPrep : Prog isa := .seq (.block windowSetup) (.seq aTable (.seq bTable (.block windowInit)))

/-- `[k]A - [S]B` in slots 0–3. -/
def windowMultiply : Prog isa :=
  .seq windowPrep (.seq skipZero (.seq windowsA (.loop byteStepAB .ne)))

end VG.Impl.Ed25519.X86
