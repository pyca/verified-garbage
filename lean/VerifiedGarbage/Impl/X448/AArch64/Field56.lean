module

public import VerifiedGarbage.Impl.X448.AArch64.Fast
public import VerifiedGarbage.Spec.X448

/-!
# Curve448's field on AArch64: the product and the square root's power as functions, and the inversion calling them

`vg_gf448_r56_mul(ws, o, a, b)` (`Proof/X448/Field56MulContract.lean`; AAPCS64: `ws` in `x0`, the byte
offsets in `x1`–`x3`) is `vg_x448`'s product (`Curve448.AArch64.Fast.mulAt`) with its operands
addressed by pointers: `ws + a` in `x10`, `ws + b` in the return address's register `x30` and
`ws + o` in `x1`, with `ws` in `x3` and the mask in `x12`. It keeps `x30` and `x21`–`x28` in
lanes of `v21`–`v25`, and writes neither `x19` nor `x20`, which its callers' taint tracking needs
public. A call (`mulCall`) passes the offsets as immediates and `ws` from `x3`, and keeps `x1` in
`x19` across the call; `mulCallK` also keeps `x19` and `x30` in the lanes of `v26`, so that it
replaces the inlined product (`opsK` does so in a list of operations). The products of distinct
operands outside loops call it: in the power below, X448's inversion and output, Ed448's
encoding of `[s]B`, and in verification the decoding of points and the final comparison.

`vg_gf448_r56_pow_p34(ws)` (`Proof/X448/Field56Contract.lean`; AAPCS64: `ws` in
`x0`) runs the register-resident addition chain `root` on slot 12 of the
working space, as a function (`asFn`): it copies `ws` to `x3` and sets the
products' mask in `x12`, as the field code expects, and keeps the callee-saved
registers it changes (`x21`–`x28`, `x19` for the squarings' counter, and `x30`, which
its calls of `vg_gf448_r56_mul` change) in lanes of `v16`–`v20`, which are not
callee-saved, so that it needs no stack. A
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

Every address is `ws` plus a constant or plus a public offset, and the only branches are the
squarings' counted loops: only the pointer and the offsets, which are public, may affect
timing.
-/

@[expose] public section

namespace VG.Impl.Ed448.AArch64

open VG.AArch64
open VG.Impl.X448.AArch64 (slot T0 T1 T2 T3 T4 T5 T6 T7)

/-! ## The product, as a function -/

namespace Point56

/-- Where `vg_gf448_r56_mul` keeps the registers it changes and restores: the return address
`x30` (the second operand's pointer while it runs) and `x21`–`x28`, in lanes of `v21`–`v25`,
which its callers do not use (the other functions keep registers in `v16`–`v20`, and the return
address in `v8`). It writes neither `x19` nor `x20`, so that a caller keeps public values there
(its registers kept in lanes are secret to taint tracking once restored). -/
def mulKept : List (Reg × VReg × Nat) :=
  [(.x30, .v21, 0), (.x21, .v21, 1), (.x22, .v22, 0), (.x23, .v22, 1), (.x24, .v23, 0),
    (.x25, .v23, 1), (.x26, .v24, 0), (.x27, .v24, 1), (.x28, .v25, 0)]

/-- The operands' pointers from the arguments (`ws` in `x0`, the offsets `o`, `a`, `b` in
`x1`–`x3`): `ws + a` in `x10`, `ws + b` in `x30`, `ws + o` in `x1`; then `ws` in `x3` and the mask
in `x12`, as the field code expects. -/
def mulSetup : List Instr :=
  [.add .x .x10 .x0 .x2, .add .x .x30 .x0 .x3, .add .x .x1 .x0 .x1, .addImm .x .x3 .x0 0,
    .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1]

/-- `vg_gf448_r56_mul`: the registers kept, the pointers set, the product of `vg_x448` with its
operands addressed by the pointers (`mulAt`), and the registers restored. -/
def mulFn : Prog isa :=
  .seq (.block (mulKept.map (fun k => .vop (.ins .d2 k.2.1 k.2.2 k.1)) ++ mulSetup)) <|
    .seq (.block (Curve448.AArch64.Fast.mulAt .x10 0 .x30 0 .x1 0))
      (.block (mulKept.map fun k => .umov .x k.1 k.2.1 k.2.2))

/-- A call of `vg_gf448_r56_mul`, `[o] := [a] * [b]` for offsets of the working space (in `x3`),
which the call leaves in `x3`. `x1`, which holds a public pointer in some callers, is kept in
`x19` across the call, which the function does not write. -/
def mulCall (o a b : Nat) : Prog isa :=
  .seq (.block [.addImm .x .x19 .x1 0, .addImm .x .x0 .x3 0, .movz .x .x1 (BitVec.ofNat 16 o) 0,
      .movz .x .x2 (BitVec.ofNat 16 a) 0, .movz .x .x3 (BitVec.ofNat 16 b) 0]) <|
    .seq (.call "vg_gf448_r56_mul" mulFn) (.block [.addImm .x .x1 .x19 0])

/-- `mulCall`, keeping `x19` and the return address in the lanes of `v26`, which the function
does not write: in place of the inlined product, for code that keeps them. -/
def mulCallK (o a b : Nat) : Prog isa :=
  .seq (.block [.vop (.ins .d2 .v26 0 .x19), .vop (.ins .d2 .v26 1 .x30)]) <|
    .seq (mulCall o a b) (.block [.umov .x .x19 .v26 0, .umov .x .x30 .v26 1])

end Point56

/-! ## The power -/

/-- `[T7] = [z]^((p-3)/4)`: the addition chain of X448's inversion
(`Weak.invert`) as far as
`z^(2^223 - 1)` in `T7` and `z^(2^222 - 1)` in `T6`, then
`(z^(2^223 - 1))^(2^223) · z^(2^222 - 1)`, with the register-resident products. -/
def root (z : Nat) : Prog isa :=
  .seq (X448.AArch64.Fast.ops [.copy T0 (slot z)]) <| .seq (X448.AArch64.Fast.sqn T0 1) <|
  .seq (Point56.mulCall T0 T0 (slot z)) <| .seq (X448.AArch64.Fast.ops [.copy T1 T0]) <|
  .seq (X448.AArch64.Fast.sqn T1 2) <|
  .seq (Point56.mulCall T1 T1 T0) <| .seq (X448.AArch64.Fast.ops [.copy T2 T1]) <|
  .seq (X448.AArch64.Fast.sqn T2 4) <|
  .seq (Point56.mulCall T2 T2 T1) <| .seq (X448.AArch64.Fast.ops [.copy T3 T2]) <|
  .seq (X448.AArch64.Fast.sqn T3 8) <|
  .seq (Point56.mulCall T3 T3 T2) <| .seq (X448.AArch64.Fast.ops [.copy T4 T3]) <|
  .seq (X448.AArch64.Fast.sqn T4 16) <|
  .seq (Point56.mulCall T4 T4 T3) <| .seq (X448.AArch64.Fast.ops [.copy T5 T4]) <|
  .seq (X448.AArch64.Fast.sqn T5 32) <|
  .seq (Point56.mulCall T5 T5 T4) <| .seq (X448.AArch64.Fast.ops [.copy T6 T5]) <|
  .seq (X448.AArch64.Fast.sqn T6 64) <| .seq (Point56.mulCall T6 T6 T5) <|
  .seq (X448.AArch64.Fast.sqn T6 64) <| .seq (Point56.mulCall T6 T6 T5) <|
  .seq (X448.AArch64.Fast.sqn T6 16) <| .seq (Point56.mulCall T6 T6 T3) <|
  .seq (X448.AArch64.Fast.sqn T6 8) <| .seq (Point56.mulCall T6 T6 T2) <|
  .seq (X448.AArch64.Fast.sqn T6 4) <| .seq (Point56.mulCall T6 T6 T1) <|
  .seq (X448.AArch64.Fast.sqn T6 2) <|
  .seq (Point56.mulCall T6 T6 T0) <| .seq (X448.AArch64.Fast.ops [.copy T7 T6]) <|
  .seq (X448.AArch64.Fast.sqn T7 1) <| .seq (Point56.mulCall T7 T7 (slot z)) <|
  .seq (X448.AArch64.Fast.sqn T7 223) (Point56.mulCall T7 T7 T6)

/-! ## As a function -/

/-- Where a function keeps each callee-saved register it changes: `x21`–`x28`
in the lanes of `v16`–`v19`; and for the power, `x19`, for the squarings' counter, and `x30`,
which its calls of `vg_gf448_r56_mul` change, in the lanes of `v20`. -/
def keptRegs (counter : Bool) : List (Reg × VReg × Nat) :=
  [(.x21, .v16, 0), (.x22, .v16, 1), (.x23, .v17, 0), (.x24, .v17, 1), (.x25, .v18, 0),
    (.x26, .v18, 1), (.x27, .v19, 0), (.x28, .v19, 1)] ++
  if counter then [(.x19, .v20, 0), (.x30, .v20, 1)] else []

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

def powCall : Prog isa := fnCall "vg_gf448_r56_pow_p34" powFn

end Point56

end VG.Impl.Ed448.AArch64

namespace VG.Impl.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64

/-- An operation, a product of distinct operands as a call of `vg_gf448_r56_mul`
(`mulCallK`). -/
def Op.progK : Op → Prog isa
  | .mul o a b => if a = b then .block (fmul o a b) else Ed448.AArch64.Point56.mulCallK o a b
  | .sub o a b => .block (Op.code (.sub o a b))
  | .addSub o₁ o₂ a b => .block (Op.code (.addSub o₁ o₂ a b))
  | .small o a e => .block (Op.code (.small o a e))
  | .copy o a => .block (Op.code (.copy o a))

/-- `ops`, with the products of distinct operands as calls of `vg_gf448_r56_mul`. -/
def opsK : List Op → Prog isa
  | [] => .block []
  | o :: os => .seq o.progK (opsK os)

/-- A call of `vg_gf448_r56_pow_p34`, with the return address kept in `v8`. -/
def powCallKeep : Prog isa :=
  .seq (.block [.vop (.ins .d2 .v8 0 .x30)]) <|
    .seq Ed448.AArch64.Point56.powCall (.block [.umov .x .x30 .v8 0])

/-- `z` (slot 2, `Z2`) inverted into `T7`: `z` copied to slot 12 (`DA`), the power
`z^((p-3)/4)` into `T7` (`powCallKeep`), squared twice and multiplied by `z` (a call of
`vg_gf448_r56_mul`). -/
def invert : Prog isa :=
  .seq (ops [.copy DA Z2]) <| .seq powCallKeep <| .seq (sqn T7 2)
    (Ed448.AArch64.Point56.mulCallK T7 T7 Z2)

/-- `x = X2 · z⁻¹` (a call of `vg_gf448_r56_mul`), written to the output, and the callee-saved
registers restored. -/
def finish : Prog isa :=
  .seq (Ed448.AArch64.Point56.mulCallK X2 X2 T7) <|
    .block (Curve448.AArch64.toLegacy X2 ++ (AArch64.freeze ++
      ((List.range 8).flatMap AArch64.packPair ++ ([ld .x19 0, ld .x20 8] ++ (restore ++ vrestore)))))

def x448 : Prog isa :=
  .seq (.block setup) <| .seq AArch64.bits <| .seq (.block [.addImm .x .x1 .x20 0]) <|
    .seq ladder <| .seq (.block Weak.lastSwap) <| .seq invert finish

end VG.Impl.X448.AArch64.Fast
