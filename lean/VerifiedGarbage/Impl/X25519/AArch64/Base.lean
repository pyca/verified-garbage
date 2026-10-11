module

public import VerifiedGarbage.Impl.Ed25519.AArch64.ScalarBase

/-!
# X25519 of the base point on AArch64

`vg_x25519_base(out = x0, scalar = x1, scratch = x2)`: `X25519(k, 9)` as the
u-coordinate `(1 + y) / (1 - y) = (Z + Y) / (Z - Y)` of `[k] B` on edwards25519
(RFC 7748 §4.1), with Ed25519's fixed-base comb (`Impl/Ed25519/AArch64/Comb.lean`)
rather than the ladder.

* Ed25519's base-point multiplication, `scalarBase`, but for two steps: the
  scalar's expanded bits (one byte per bit, at `scratch + 768`) are clamped as
  `decodeScalar25519` clamps the scalar (bits 0–2 and 255 cleared, bit 254 set),
  and the result is encoded as a u-coordinate rather than as a point.
* The u-coordinate: `X := Z + Y` and `Z := Z - Y` in the point's slots, then
  `pointAffine` (one inversion) makes `X / Z`, which is frozen into `x4`–`x7`;
  `scalarFinish` restores the callee-saved registers and stores it to `out`.
* The working space and the saved registers are in `scratch`, as for Ed25519.
-/

@[expose] public section

namespace VG.Impl.X25519.AArch64.Base

open VG.AArch64
open VG.Impl.Ed25519.AArch64

/-- Clamp the expanded bits at `x0 + 768`: bits 0, 1, 2 and 255 cleared, bit 254 set. -/
def clampBits : List Instr :=
  [.movz .w .x9 0 0, .strb .x9 .x0 768, .strb .x9 .x0 769, .strb .x9 .x0 770,
    .strb .x9 .x0 1023, .movz .w .x9 1 0, .strb .x9 .x0 1022]

/-- `X := Z + Y`, `Z := Z - Y` (the point is `X, Y, Z, T` in slots 0–3). -/
def uOps : List FieldOp := [.add 0 2 1, .sub 2 2 1]

/-- The u-coordinate `(Z + Y) / (Z - Y)`, frozen into `x4`–`x7`. -/
def uEncode : Prog isa := .seq (.block (fieldCode uOps)) (.seq pointAffine (.block (freeze 64)))

def engine : Prog isa :=
  .seq scalarBasePrepare (.seq (.block clampBits) (.seq combMultiply uEncode))

def x25519Base : Prog isa :=
  .seq (.block (scalarSave ++ scalarBaseSetup)) (.seq engine scalarBaseFinish)

end VG.Impl.X25519.AArch64.Base
