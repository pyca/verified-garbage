module
public import VerifiedGarbage.TCB.PPC64LE.Isa


/-!
# ML-DSA on PPC64LE: packing and unpacking `d`-bit fields

As on 32-bit ARM (`Impl/MlDsa/Arm/Pack/Stream.lean`), with 64-bit registers:
the encodings of FIPS 204 §7.1 write each coefficient as a `d`-bit
little-endian field, and each width `d` is handled by the same loops,
parametrized by `d`: a group of `c` coefficients is `nb` bytes
(`d · c = 8 · nb`), and a loop runs over the `256 / c` groups, counting
`r12` down to zero. Within a group, the fields stream through the
accumulator `r8`, in a schedule that depends only on `d`:

* `packBody ld d c nb` (coefficients at `r10`, bytes to `r11`): the value of
  coefficient `j` (`ld j`, into `r9`, at most `d` bits; it may use `r0`) is
  added to `r8` shifted left by the `d·j mod 8` bits `r8` holds, and then
  each byte it completes, the low byte of `r8`, is stored and shifted out.
* `unpackBody fin d c nb` (bytes at `r10`, coefficients to `r11`): before
  field `j`, each byte it needs (into `r9`) is added to `r8` shifted left by
  the bits `r8` holds; the field is then the low `d` bits of `r8` (into `r9`,
  by two shifts; `r8` shifted right by `d`), which `fin j` turns into the
  coefficient and stores (it may use `r0`).

`r8` never holds more than `d + 7 ≤ 27` bits. The model has no masking
instructions: fields are extracted with pairs of shifts. Every address and
branch depends only on the pointers and `d`.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.Pack

open VG.PPC64LE

/-- `r8 ← r8 + r9 · 2^sh` (`r9` overwritten). -/
def shiftAdd (sh : Nat) : List Instr :=
  if sh = 0 then [.add .r8 .r8 .r9] else [.lsl .r9 .r9 sh, .add .r8 .r8 .r9]

/-! ## Packing -/

/-- Byte `t` of the group, the low byte of `r8`, to `r11 + t`. -/
def packByte (t : Nat) : List Instr := [.stb .r8 .r11 t, .lsr .d .r8 .r8 8]

/-- Coefficient `j` of the group: its value (`ld j`, in `r9`) added to `r8`,
then the bytes it completes. -/
def packCoef (ld : Nat → List Instr) (d j : Nat) : List Instr :=
  ld j ++ shiftAdd (d * j % 8) ++
    (List.range (d * (j + 1) / 8 - d * j / 8)).flatMap fun u => packByte (d * j / 8 + u)

def packBody (ld : Nat → List Instr) (d c nb : Nat) : List Instr :=
  ([.li .r8 0] : List Instr) ++ (List.range c).flatMap (packCoef ld d) ++
    ([.addi .r10 .r10 (4 * c), .addi .r11 .r11 nb, .subi .r12 .r12 1] : List Instr)

/-- All the groups. -/
def packLoop (ld : Nat → List Instr) (d c nb : Nat) : Prog isa :=
  .seq (.block [.li .r12 (256 / c)]) (.loop (.block (packBody ld d c nb)) (.nonzero .d .r12))

/-! ## Unpacking -/

/-- The number of bytes of the group that the first `j` fields need. -/
def need (d j : Nat) : Nat := (d * j + 7) / 8

/-- Byte `t` of the group into `r8`, above the `8t - d·j` bits it holds. -/
def unpackByte (d j t : Nat) : List Instr := .lbz .r9 .r10 t :: shiftAdd (8 * t - d * j)

/-- The low `d` bits of `r8` into `r9`, and `r8` shifted right by `d`. -/
def extract (d : Nat) : List Instr := [.lsl .r9 .r8 (64 - d), .lsr .d .r9 .r9 (64 - d), .lsr .d .r8 .r8 d]

/-- Field `j` of the group: the bytes it needs into `r8`, then its value
into `r9`, and `fin j`. -/
def unpackCoef (fin : Nat → List Instr) (d j : Nat) : List Instr :=
  (List.range (need d (j + 1) - need d j)).flatMap (fun u => unpackByte d j (need d j + u)) ++ extract d ++
    fin j

def unpackBody (fin : Nat → List Instr) (d c nb : Nat) : List Instr :=
  ([.li .r8 0] : List Instr) ++ (List.range c).flatMap (unpackCoef fin d) ++
    ([.addi .r10 .r10 nb, .addi .r11 .r11 (4 * c), .subi .r12 .r12 1] : List Instr)

/-- All the groups. -/
def unpackLoop (fin : Nat → List Instr) (d c nb : Nat) : Prog isa :=
  .seq (.block [.li .r12 (256 / c)]) (.loop (.block (unpackBody fin d c nb)) (.nonzero .d .r12))

/-! ## Reduction modulo `q` -/

/-- `q` in `r7`. -/
def loadQ : List Instr := [.lis .r7 0x7F, .ori .r7 .r7 0xE001]

/-- `B` in `r`: `li` below `2¹⁵`, else `lis` of its high half (`B` a multiple
of `2¹⁶` below `2³¹`). -/
def loadB (r : Reg) (B : Nat) : List Instr :=
  if B < 2 ^ 15 then [.li r B] else [.lis r (BitVec.ofNat 16 (B / 2 ^ 16))]

/-- `v ← v + q` if `v` is negative (as a 64-bit number), with `r0` the sign
bit and `q` in `r7`. -/
def addQNeg (v : Reg) : List Instr := [.lsr .d .r0 v 63, .mul .r0 .r0 .r7, .add v v .r0]

/-- `r9 ← B - r9` modulo `q`, for `B` in `r4` and `r9` at most `q - 1 + B`:
`B - x`, plus `q` if it is negative. -/
def bMinus : List Instr := ([.sub .r9 .r4 .r9] : List Instr) ++ addQNeg .r9

end VG.Impl.MlDsa.PPC64LE.Pack
