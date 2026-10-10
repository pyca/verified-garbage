import VerifiedGarbage.Impl.X448.AArch64.Fast
import VerifiedGarbage.Spec.X448.Field56

/-!
# Curve448's field on AArch64: the square root's power, and the inversion calling it

`vg_gf448_r56_pow_p34(ws)` (`Spec/X448/Field56.lean`; AAPCS64: `ws` in
`x0`) runs the register-resident addition chain `root` on slot 12 of the
working space, as a function (`asFn`): it copies `ws` to `x3` and sets the
products' mask in `x12`, as the field code expects, and keeps the callee-saved
registers it changes (`x21`–`x28`, and `x19` for the squarings' counter) in
lanes of `v16`–`v20`, which are not callee-saved, so that it needs no stack. A
call (`fnCall`) passes `ws` from `x3`, and the function leaves it there, with
the mask in `x12`. (The names are those Ed448's point functions,
`Impl/Ed448/AArch64/Point56.lean`, which are built the same way, gave them.)

X448's inversion (`Fast.invert`, which `vg_x448`, `vg_x448_base` and
`vg_ed448_scalar_base` run) calls it: `z^(p-2)` is `(z^((p-3)/4))^4 z`, so it
copies `z` (slot 2) to slot 12, free once the ladder is done, calls the
function, and squares its result twice and multiplies it by `z`. The return
address is kept across the call in a lane of `v8`, which the callers have
saved in the working space by then (`Fast.vsave`) and which the function does
not write; `Fast.x448` is X448's whole function with this inversion.

Every address is `ws` plus a constant, and the only branches are the
squarings' counted loops: only the pointer, which is public, may affect
timing.
-/

namespace VG.Impl.Ed448.AArch64

open VG.AArch64
open VG.Impl.X448.AArch64 (slot T0 T1 T2 T3 T4 T5 T6 T7)

/-! ## The power -/

/-- `[T7] = [z]^((p-3)/4)`: the addition chain of X448's inversion
(`Weak.invert`) as far as
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

/-! ## As a function -/

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

/-- `vg_gf448_r56_pow_p34`: slot 12 to the power `(p - 3) / 4` into slot 21. -/
def powFn : Prog isa := asFn true (root 12)

def powCall : Prog isa := fnCall Spec.X448.Field56.powApi.name powFn

end Point56

end VG.Impl.Ed448.AArch64

namespace VG.Impl.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64

/-- A call of `vg_gf448_r56_pow_p34`, with the return address kept in `v8`. -/
def powCallKeep : Prog isa :=
  .seq (.block [.vop (.ins .d2 .v8 0 .x30)]) <|
    .seq Ed448.AArch64.Point56.powCall (.block [.umov .x .x30 .v8 0])

/-- `z` (slot 2, `Z2`) inverted into `T7`: `z` copied to slot 12 (`DA`), the power
`z^((p-3)/4)` into `T7` (`powCallKeep`), squared twice and multiplied by `z`. -/
def invert : Prog isa :=
  .seq (ops [.copy DA Z2]) <| .seq powCallKeep <| .seq (sqn T7 2) (ops [.mul T7 T7 Z2])

def x448 : Prog isa :=
  .seq (.block setup) <| .seq AArch64.bits <| .seq (.block [.addImm .x .x1 .x20 0]) <|
    .seq ladder <| .seq (.block Weak.lastSwap) <| .seq invert finish

end VG.Impl.X448.AArch64.Fast
