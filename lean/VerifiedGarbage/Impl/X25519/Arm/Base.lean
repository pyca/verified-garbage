module

public import VerifiedGarbage.Impl.Ed25519.Arm.ScalarBase
public import VerifiedGarbage.Impl.Residue.Arm

/-!
# X25519 of the base point on ARMv7

`vg_x25519_base(out = r0, scalar = r1, scratch = r2)`: `X25519(k, 9)` as the u-coordinate
`(1 + y) / (1 - y) = (Z + Y) / (Z - Y)` of `[k] B` on edwards25519 (RFC 7748 §4.1), with
Ed25519's fixed-base comb (`Impl/Ed25519/Arm/Comb.lean`) rather than the ladder. With the flag
`umaal` its field's products are by `umaal` (`Impl/Ed25519/Arm/MulFn.lean`):
`vg_x25519_base_umaal`.

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
def uEncode (umaal : Bool) : Prog isa :=
  .seq (fieldCode false uOps) (.seq (pointAffine umaal) (.block (VG.Impl.Ed25519.Arm.freeze 0)))

/-- The slots cleared, the scalar copied and clamped, the comb, and the u-coordinate. -/
def engine (umaal : Bool) : Prog isa :=
  .seq (.block (initFields ++ combCopy ++ clampBytes))
    (.seq combInit (.seq (.loop (combStep umaal) .ne) (uEncode umaal)))

def x25519Base (umaal : Bool) : Prog isa :=
  .seq (.block scalarBaseSetup) (.seq (engine umaal) (.block scalarBaseFinish))

end VG.Impl.X25519.Arm.Base

namespace VG.Impl.X25519.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_x25519_base`, with either product of the field (`umaal`):
`x25519Base umaal`, then the registers a callee may change
and the flags set to constants. -/
def x25519Base (umaal : Bool) : Prog isa := scrub 0 (Base.x25519Base umaal)

end VG.Impl.X25519.Arm.Fn
