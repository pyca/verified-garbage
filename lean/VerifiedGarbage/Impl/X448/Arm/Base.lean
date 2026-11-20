module

public import VerifiedGarbage.Impl.Ed448.Arm.ScalarBase
public import VerifiedGarbage.Impl.Xdh.Arm
public import VerifiedGarbage.Impl.Residue.Arm

/-!
# X448 of the base point on ARMv7: a fixed-base multiplication on edwards448

`vg_x448_base(out = r0, scalar = r1, scratch = r2)` computes `X448(k, 5)` as
the u-coordinate `y² / x²` of `[k] B` on edwards448 (Ed448's curve), `B` its
base point (RFC 7748 §4.2's 4-isogeny; `Proof/X448/BaseAdd.lean`).

`[k] B` is Ed448's base-point multiplication on this target
(`Impl/Ed448/Arm/ScalarBase.lean`): its entry (`baseEntry`: the callee-saved
registers saved in the working space, and the slots initialized) and its
four-column comb (`combLoop`), which leaves `[k] B` as `(X : Y : Z)` in slots
0–2. The comb reads 456 bits, a byte each at `BITS`: X448's `bits` expands
the decoded (clamped) scalar's 448, and the eight above them are zeroed
(`zeroTop`).

Then `X448(k, 5) = Y² / X²`: the squares go to the ladder's `X2` and `Z2`,
inverted, multiplied, fully reduced and written as the ladder's result is
(`invert`, `finish`).

The only branches are on the loop counters, and every address is a pointer
plus a constant or a counter, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.X448.Arm

open VG.Arm

/-- The bytes of bits 448–455 at `BITS`, zeroed. -/
def zeroTop : List Instr :=
  .mov .r3 (.imm 0) :: (List.range 8).flatMap fun j => [.strb .r3 .r0 (BITS + 448 + j)]

/-- `X²` into `Z2` and `Y²` into `X2`, for `(X : Y : Z)` in slots 0–2. -/
def uOps : List Op := [.mul Z2 X1 X1, .mul X2 X2 X2]

/-- `vg_x448_base(out = r0, scalar = r1, scratch = r2)`. -/
def x448Base (u : Bool) : Prog isa :=
  .seq (.block (Impl.Ed448.Arm.baseEntry ++ zeroTop)) <| .seq bits <| .seq (Impl.Ed448.Arm.combLoop u) <|
  .seq (ops u uOps) <| .seq (invert u) (finish u)

end VG.Impl.X448.Arm

namespace VG.Impl.X448.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_x448_base`, with either multiplication of the field (`u`): `x448Base u`,
then the registers a callee may change and the flags set to constants. -/
def x448Base (u : Bool) : Prog isa := scrub 0 (Arm.x448Base u)

/-- `vg_x448_exchange`, with either multiplication of the field: `vg_x448`
called from frames of 8 bytes, then those bytes zeroed and the registers a
callee may change, but the result, and the flags set to constants. -/
def exchange (u : Bool) : Prog isa :=
  scrubF 32 8 (Impl.Xdh.Arm.exchange ("vg_x448" ++ suffix u) (Arm.x448 u) 56)

end VG.Impl.X448.Arm.Fn
