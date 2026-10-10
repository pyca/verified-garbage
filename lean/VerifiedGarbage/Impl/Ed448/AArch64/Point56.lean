import VerifiedGarbage.Impl.Ed448.AArch64.ScalarBase
import VerifiedGarbage.Impl.X448.AArch64.Fast
import VerifiedGarbage.Spec.Ed448.Point56

/-!
# Ed448's point addition, doubling and the square root's power on AArch64, as functions

`vg_ed448_r56_point_add(ws)`, `vg_ed448_r56_point_double(ws)`
(`Spec/Ed448/Point56.lean`) and `vg_gf448_r56_pow_p34(ws)`
(`Spec/X448/Field56.lean`; AAPCS64: `ws` in `x0`) run the register-resident
field code that `vg_ed448_verify_equation` inlined (`Base.addOps`, `dblOps`,
`root`) on the slots where it keeps their operands. Each copies `ws` to
`x3` and sets the products' mask in `x12`, as that code expects, and keeps the
callee-saved registers it changes (`x21`–`x28`, and `x19` for the squarings'
counter) in lanes of `v16`–`v20`, which are not callee-saved, so that it needs
no stack (`asFn`). A call (`fnCall`) passes `ws` from `x3`, and the function
leaves it there, with the mask in `x12`.

Every address is `ws` plus a constant, and the only branches are the
squarings' counted loops: only the pointer, which is public, may affect
timing.
-/

namespace VG.Impl.Ed448.AArch64

open VG.AArch64
open VG.Impl.X448.AArch64 (slot T0 T1 T2 T3 T4 T5 T6 T7)

/-! ## The square root's power -/

/-- `[T7] = [z]^((p-3)/4)`: X448's addition chain (`Fast.invert`) as far as
`z^(2^223 - 1)` in `T7` and `z^(2^222 - 1)` in `T6`, then
`(z^(2^223 - 1))^(2^223) · z^(2^222 - 1)`, with the register-resident products. -/
def root (z : Nat) : Prog isa :=
  .seq (X448.AArch64.Fast.ops [.copy T0 (slot z)]) <| .seq (X448.AArch64.Fast.sqn T0 1) <|
  .seq (X448.AArch64.Fast.ops [.mul T0 T0 (slot z), .copy T1 T0]) <|
  .seq (X448.AArch64.Fast.sqn T1 2) <| .seq (X448.AArch64.Fast.ops [.mul T1 T1 T0, .copy T2 T1]) <|
  .seq (X448.AArch64.Fast.sqn T2 4) <| .seq (X448.AArch64.Fast.ops [.mul T2 T2 T1, .copy T3 T2]) <|
  .seq (X448.AArch64.Fast.sqn T3 8) <| .seq (X448.AArch64.Fast.ops [.mul T3 T3 T2, .copy T4 T3]) <|
  .seq (X448.AArch64.Fast.sqn T4 16) <| .seq (X448.AArch64.Fast.ops [.mul T4 T4 T3, .copy T5 T4]) <|
  .seq (X448.AArch64.Fast.sqn T5 32) <| .seq (X448.AArch64.Fast.ops [.mul T5 T5 T4, .copy T6 T5]) <|
  .seq (X448.AArch64.Fast.sqn T6 64) <| .seq (X448.AArch64.Fast.ops [.mul T6 T6 T5]) <|
  .seq (X448.AArch64.Fast.sqn T6 64) <| .seq (X448.AArch64.Fast.ops [.mul T6 T6 T5]) <|
  .seq (X448.AArch64.Fast.sqn T6 16) <| .seq (X448.AArch64.Fast.ops [.mul T6 T6 T3]) <|
  .seq (X448.AArch64.Fast.sqn T6 8) <| .seq (X448.AArch64.Fast.ops [.mul T6 T6 T2]) <|
  .seq (X448.AArch64.Fast.sqn T6 4) <| .seq (X448.AArch64.Fast.ops [.mul T6 T6 T1]) <|
  .seq (X448.AArch64.Fast.sqn T6 2) <| .seq (X448.AArch64.Fast.ops [.mul T6 T6 T0, .copy T7 T6]) <|
  .seq (X448.AArch64.Fast.sqn T7 1) <| .seq (X448.AArch64.Fast.ops [.mul T7 T7 (slot z)]) <|
  .seq (X448.AArch64.Fast.sqn T7 223) (X448.AArch64.Fast.ops [.mul T7 T7 T6])

/-! ## Doubling -/

/-- `(X : Y : Z)` in slots `x y z` doubled in place (RFC 8032 §5.2.4, as
`double`): `P = XY`, `C = X²`, `D = Y²`, `2Z²` (`Z` times `Z + Z`), `E = C + D`
and `C - D`, `E` reduced (a product by 1, in slot 20), `J = E - 2Z²`, `2P`, and
`(2P J, E (C - D), E J)`. The temporaries are slots 10–18. -/
def dblOps (x y z : Nat) : List Impl.X448.AArch64.Fast.Op :=
  [.addSub (slot 16) (slot 17) z z, .mul (slot 10) x y, .mul (slot 11) x x, .mul (slot 12) y y,
   .mul (slot 18) z (slot 16), .addSub (slot 13) (slot 14) (slot 11) (slot 12),
   .mul (slot 15) (slot 13) (slot 20), .addSub (slot 16) (slot 17) (slot 10) (slot 10),
   .sub (slot 17) (slot 15) (slot 18), .mul y (slot 13) (slot 14), .mul x (slot 16) (slot 17),
   .mul z (slot 13) (slot 17)]

/-! ## Functions -/

/-- Where a function keeps each callee-saved register it changes: `x21`–`x28`
in the lanes of `v16`–`v19`, and `x19`, for the squarings' counter, in a lane of
`v20`. -/
def keptRegs (counter : Bool) : List (Reg × VReg × Nat) :=
  [(.x21, .v16, 0), (.x22, .v16, 1), (.x23, .v17, 0), (.x24, .v17, 1), (.x25, .v18, 0),
    (.x26, .v18, 1), (.x27, .v19, 0), (.x28, .v19, 1)] ++
  if counter then [(.x19, .v20, 0)] else []

/-- `body` as a function: `ws` to `x3`, the mask to `x12`, the registers kept,
`body`, and the registers restored. -/
def asFn (counter : Bool) (body : Prog isa) : Prog isa :=
  .seq (.block ([.addImm .x .x3 .x0 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] ++
      (keptRegs counter).map fun k => .vop (.ins .d2 k.2.1 k.2.2 k.1)))
    (.seq body (.block ((keptRegs counter).map fun k => .umov .x k.1 k.2.1 k.2.2)))

/-- A call of `fn`, named `name`, with `ws` from `x3`. -/
def fnCall (name : String) (fn : Prog isa) : Prog isa :=
  .seq (.block [.addImm .x .x0 .x3 0]) (.call name fn)

namespace Point56

/-- `vg_ed448_r56_point_add`: slots 6–8 added to slots 3–5. -/
def addFn : Prog isa :=
  asFn false (X448.AArch64.Fast.ops
    (Impl.X448.AArch64.Base.addOps (slot 3) (slot 4) (slot 5) (slot 6) (slot 7) (slot 8)))

/-- `vg_ed448_r56_point_double`: slots 3–5 doubled. -/
def doubleFn : Prog isa := asFn false (X448.AArch64.Fast.ops (dblOps (slot 3) (slot 4) (slot 5)))

/-- `vg_gf448_r56_pow_p34`: slot 12 to the power `(p - 3) / 4` into slot 21. -/
def powFn : Prog isa := asFn true (root 12)

def addCall : Prog isa := fnCall Spec.Ed448.Point56.addApi.name addFn
def doubleCall : Prog isa := fnCall Spec.Ed448.Point56.doubleApi.name doubleFn
def powCall : Prog isa := fnCall Spec.X448.Field56.powApi.name powFn

end Point56

end VG.Impl.Ed448.AArch64
