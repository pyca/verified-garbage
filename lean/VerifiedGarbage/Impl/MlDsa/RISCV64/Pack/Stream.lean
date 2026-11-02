module
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Arith


/-!
# ML-DSA on RISC-V: packing and unpacking `d`-bit fields

As on PPC64LE (`Impl/MlDsa/PPC64LE/Pack/Stream.lean`), with 64-bit registers:
the encodings of FIPS 204 §7.1 write each coefficient as a `d`-bit
little-endian field, and each width `d` is handled by the same loops,
parametrized by `d`: a group of `c` coefficients is `nb` bytes
(`d · c = 8 · nb`), and a loop runs over the `256 / c` groups, counting
`t2` down to zero. Within a group, the fields stream through the
accumulator `a5`, in a schedule that depends only on `d`:

* `packBody ld d c nb` (coefficients at `a7`, bytes to `t1`): the value of
  coefficient `j` (`ld j`, into `a6`, at most `d` bits; it may use `t0`) is
  added to `a5` shifted left by the `d·j mod 8` bits `a5` holds, and then
  each byte it completes, the low byte of `a5`, is stored and shifted out.
* `unpackBody fin d c nb` (bytes at `a7`, coefficients to `t1`): before
  field `j`, each byte it needs (into `a6`) is added to `a5` shifted left by
  the bits `a5` holds; the field is then the low `d` bits of `a5` (into `a6`,
  by two shifts; `a5` shifted right by `d`), which `fin j` turns into the
  coefficient and stores (it may use `t0`).

`a5` never holds more than `d + 7 ≤ 27` bits. Fields are extracted with pairs of shifts, as on PPC64LE. Every address and
branch depends only on the pointers and `d`.
-/

@[expose] public section

namespace VG.Impl.MlDsa.RISCV64.Pack

open VG.RISCV64

/-- `a5 ← a5 + a6 · 2^sh` (`a6` overwritten). -/
def shiftAdd (sh : Nat) : List Instr :=
  if sh = 0 then [.add .a5 .a5 .a6] else [.shift .sll .d .a6 .a6 sh, .add .a5 .a5 .a6]

/-! ## Packing -/

/-- Byte `t` of the group, the low byte of `a5`, to `r11 + t`. -/
def packByte (t : Nat) : List Instr := [.store .b .a5 .t1 t, .shift .srl .d .a5 .a5 8]

/-- Coefficient `j` of the group: its value (`ld j`, in `a6`) added to `a5`,
then the bytes it completes. -/
def packCoef (ld : Nat → List Instr) (d j : Nat) : List Instr :=
  ld j ++ shiftAdd (d * j % 8) ++
    (List.range (d * (j + 1) / 8 - d * j / 8)).flatMap fun u => packByte (d * j / 8 + u)

def packBody (ld : Nat → List Instr) (d c nb : Nat) : List Instr :=
  ([.li .a5 0] : List Instr) ++ (List.range c).flatMap (packCoef ld d) ++
    ([.addi .a7 .a7 ((4 * c : Nat) : Int), .addi .t1 .t1 nb, .addi .t2 .t2 (-1)] : List Instr)

/-- All the groups. -/
def packLoop (ld : Nat → List Instr) (d c nb : Nat) : Prog isa :=
  .seq (.block [.li .t2 ((256 / c : Nat) : Int)]) (.loop (.block (packBody ld d c nb)) (.nonzero .t2))

/-! ## Unpacking -/

/-- The number of bytes of the group that the first `j` fields need. -/
def need (d j : Nat) : Nat := (d * j + 7) / 8

/-- Byte `t` of the group into `a5`, above the `8t - d·j` bits it holds. -/
def unpackByte (d j t : Nat) : List Instr := .load .b .a6 .a7 t :: shiftAdd (8 * t - d * j)

/-- The low `d` bits of `a5` into `a6`, and `a5` shifted right by `d`. -/
def extract (d : Nat) : List Instr := [.shift .sll .d .a6 .a5 (64 - d), .shift .srl .d .a6 .a6 (64 - d), .shift .srl .d .a5 .a5 d]

/-- Field `j` of the group: the bytes it needs into `a5`, then its value
into `a6`, and `fin j`. -/
def unpackCoef (fin : Nat → List Instr) (d j : Nat) : List Instr :=
  (List.range (need d (j + 1) - need d j)).flatMap (fun u => unpackByte d j (need d j + u)) ++ extract d ++
    fin j

def unpackBody (fin : Nat → List Instr) (d c nb : Nat) : List Instr :=
  ([.li .a5 0] : List Instr) ++ (List.range c).flatMap (unpackCoef fin d) ++
    ([.addi .a7 .a7 nb, .addi .t1 .t1 ((4 * c : Nat) : Int), .addi .t2 .t2 (-1)] : List Instr)

/-- All the groups. -/
def unpackLoop (fin : Nat → List Instr) (d c nb : Nat) : Prog isa :=
  .seq (.block [.li .t2 ((256 / c : Nat) : Int)]) (.loop (.block (unpackBody fin d c nb)) (.nonzero .t2))

/-! ## Reduction modulo `q` -/

/-- `q` in `a4`. -/
def loadQ : List Instr := VG.Impl.MlDsa.RISCV64.Arith.loadImm .a4 8380417

/-- `B` in `r` (`B < 2³¹ - 2048`). -/
def loadB (r : Reg) (B : Nat) : List Instr := VG.Impl.MlDsa.RISCV64.Arith.loadImm r B

/-- `a6 ← B - a6` modulo `q`, for `B` in `a1` and `a6` at most `q - 1 + B`:
`B - x`, plus `q` (in `a4`) if it is negative (`fixup`, through `t0`). -/
def bMinus : List Instr := ([.sub .a6 .a1 .a6] : List Instr) ++ VG.Impl.MlKem.RISCV64.fixup .a6 .t0 .a4

end VG.Impl.MlDsa.RISCV64.Pack
