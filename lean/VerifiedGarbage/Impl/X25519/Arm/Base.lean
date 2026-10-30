module

public import VerifiedGarbage.Impl.Ed25519.Arm.ScalarBase

/-!
# X25519 of the base point on ARMv7

`vg_x25519_base(out = r0, scalar = r1, scratch = r2)`: `X25519(k, 9)` as the u-coordinate
`(1 + y) / (1 - y) = (Z + Y) / (Z - Y)` of `[k] B` on edwards25519 (RFC 7748 §4.1), with
Ed25519's fixed-base comb (`Impl/Ed25519/Arm/Comb.lean`) rather than the ladder.

* Ed25519's base-point multiplication, `scalarBase`, but for two steps: the scalar's copy in
  the workspace is clamped as `decodeScalar25519` clamps the scalar (byte 0 ANDed with 248,
  byte 31 with 127 and ORed with 64) before the comb reads it, and the result is encoded as a
  u-coordinate rather than as a point.
* The u-coordinate: `X := Z + Y` and `Z := Z - Y` in the point's slots, then `pointAffine`
  (one inversion) makes `X / Z`, which is frozen into `FR`; `scalarBaseFinish` stores it to
  `out` and restores the callee-saved registers.
-/

@[expose] public section

namespace VG.Impl.X25519.Arm.Base

open VG.Arm VG.Impl.Ed25519.Arm

/-- The scalar's copy at byte `SCAL` of the workspace clamped: byte 0 ANDed with 248, byte 31
ANDed with 127 and ORed with 64. -/
def clampBytes : List Instr :=
  [.ldrb .r1 .r0 SCAL, .dp .and .r1 .r1 (.imm 248), .strb .r1 .r0 SCAL,
    .ldrb .r1 .r0 (SCAL + 31), .dp .and .r1 .r1 (.imm 127), .dp .orr .r1 .r1 (.imm 64),
    .strb .r1 .r0 (SCAL + 31)]

/-- `X := Z + Y`, `Z := Z - Y` (the point is `X, Y, Z, T` in slots 0–3). -/
def uOps : List FieldOp := [.add 0 2 1, .sub 2 2 1]

/-- The u-coordinate `(Z + Y) / (Z - Y)`, frozen into `FR`. -/
def uEncode : Prog isa := .seq (fieldCode uOps) (.seq pointAffine (.block (VG.Impl.Ed25519.Arm.freeze 0)))

/-- The slots cleared, the scalar copied and clamped, the comb, and the u-coordinate. -/
def engine : Prog isa :=
  .seq (.block (initFields ++ combCopy ++ clampBytes))
    (.seq combInit (.seq (.loop combStep .ne) uEncode))

def x25519Base : Prog isa :=
  .seq (.block scalarBaseSetup) (.seq engine (.block scalarBaseFinish))

end VG.Impl.X25519.Arm.Base
