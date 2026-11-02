module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.ScalarBase

/-!
# X25519 of the base point on PPC64LE

`vg_x25519_base(out = r3, scalar = r4, scratch = r5)`: `X25519(k, 9)` as the u-coordinate
`(1 + y) / (1 - y) = (Z + Y) / (Z - Y)` of `[k] B` on edwards25519 (RFC 7748 §4.1), with
Ed25519's fixed-base comb (`Impl/Ed25519/PPC64LE/Comb.lean`) rather than the ladder, as on
RISC-V (`Impl/X25519/RISCV64/Base.lean`).

* Ed25519's base-point multiplication, `scalarBase`, but for two steps: the scalar's nibbles
  (at `SCAL` of the working space, one a byte) are clamped as `decodeScalar25519` clamps the
  scalar (`clampCopy`: bits 0–2 and 255 cleared, bit 254 set, so nibble 0 ANDed with 8 and
  nibble 63 ANDed with 7 and ORed with 4) before the comb reads them, and the result is
  encoded as a u-coordinate rather than as a point.
* The u-coordinate: `X := Z + Y` and `Z := Z - Y` in the point's slots, then `pointAffine`
  (one inversion) makes `X / Z` in slot 0, which is frozen into `FR`; `scalarBaseFinish`
  copies it to `out` and restores the nonvolatile registers and `lr`.
-/

@[expose] public section

namespace VG.Impl.X25519.PPC64LE.Base

open VG.PPC64LE
open VG.Impl.Ed25519.PPC64LE

/-- Clamp the scalar's nibbles: nibble 0 `&&& 8`, nibble 63 `&&& 7 ||| 4`. -/
def clampCopy : List Instr :=
  [.lbz .r7 .r6 SCAL, .li .r8 8, .logic .and .r7 .r7 .r8, .stb .r7 .r6 SCAL,
    .lbz .r7 .r6 (SCAL + 63), .li .r8 7, .logic .and .r7 .r7 .r8, .ori .r7 .r7 4,
    .stb .r7 .r6 (SCAL + 63)]

/-- `[k]B` into slots 0–3 for the clamped scalar at `r14`. -/
def combClamped : Prog isa :=
  .seq (.block combCopy) (.seq (.block clampCopy) (.seq combInit (.loop combStep (.nonzero .d .r7))))

/-- `X := Z + Y`, `Z := Z - Y` (the point is `X, Y, Z, T` in slots 0–3). -/
def uOps : List FieldOp := [.add 0 2 1, .sub 2 2 1]

/-- The u-coordinate `(Z + Y) / (Z - Y)`, frozen at `FR`. -/
def uEncode : Prog isa := .seq (fieldCode uOps) (.seq pointAffine (.block (Impl.Ed25519.PPC64LE.freeze 0)))

def engine : Prog isa := .seq (.block initFields) (.seq combClamped uEncode)

def x25519Base : Prog isa :=
  .seq (.block scalarBaseSetup) (.seq engine (.block scalarBaseFinish))

end VG.Impl.X25519.PPC64LE.Base
