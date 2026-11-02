module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.ScalarBase

/-!
# X25519 of the base point on RISC-V

`vg_x25519_base(out = a0, scalar = a1, scratch = a2)`: `X25519(k, 9)` as the
u-coordinate `(1 + y) / (1 - y) = (Z + Y) / (Z - Y)` of `[k] B` on edwards25519
(RFC 7748 §4.1), with Ed25519's fixed-base comb (`Impl/Ed25519/RISCV64/Comb.lean`)
rather than the ladder, as on AArch64 (`Impl/X25519/AArch64/Base.lean`).

* Ed25519's base-point multiplication, `scalarBase`, but for two steps: the
  scalar's copy (at `SCAL` of the working space) is clamped as
  `decodeScalar25519` clamps the scalar (`clampCopy`: bits 0–2 and 255 cleared,
  bit 254 set) before the comb reads it, and the result is encoded as a
  u-coordinate rather than as a point.
* The u-coordinate: `X := Z + Y` and `Z := Z - Y` in the point's slots, then
  `pointAffine` (one inversion) makes `X / Z` in slot 0, which is frozen into
  `FR`; `scalarBaseFinish` copies it to `out` and restores the callee-saved
  registers.
-/

@[expose] public section

namespace VG.Impl.X25519.RISCV64.Base

open VG.RISCV64
open VG.Impl.Ed25519.RISCV64

/-- Clamp the scalar's copy: byte 0 `&&& 248`, byte 31 `&&& 127 ||| 64`. -/
def clampCopy : List Instr :=
  [.load .b .a4 .a3 SCAL, .logicImm .and .a4 .a4 248, .store .b .a4 .a3 SCAL,
    .load .b .a4 .a3 (SCAL + 31), .logicImm .and .a4 .a4 127, .logicImm .or .a4 .a4 64,
    .store .b .a4 .a3 (SCAL + 31)]

/-- `[k]B` into slots 0–3 for the clamped scalar at `s0`. -/
def combClamped : Prog isa :=
  .seq (.block combCopy) (.seq (.block clampCopy) (.seq combInit (.loop combStep (.nonzero .a4))))

/-- `X := Z + Y`, `Z := Z - Y` (the point is `X, Y, Z, T` in slots 0–3). -/
def uOps : List FieldOp := [.add 0 2 1, .sub 2 2 1]

/-- The u-coordinate `(Z + Y) / (Z - Y)`, frozen at `FR`. -/
def uEncode : Prog isa := .seq (fieldCode uOps) (.seq pointAffine (.block (Impl.Ed25519.RISCV64.freeze 0)))

def engine : Prog isa := .seq (.block initFields) (.seq combClamped uEncode)

def x25519Base : Prog isa :=
  .seq (.block scalarBaseSetup) (.seq engine (.block scalarBaseFinish))

end VG.Impl.X25519.RISCV64.Base
