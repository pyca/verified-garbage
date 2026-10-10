import VerifiedGarbage.Impl.X448.AArch64.Base
import VerifiedGarbage.Impl.X448.AArch64.Field56
import VerifiedGarbage.Spec.Ed448.Point56

/-!
# Ed448's point addition and doubling on AArch64, as functions

`vg_ed448_r56_point_add(ws)` and `vg_ed448_r56_point_double(ws)`
(`Spec/Ed448/Point56.lean`; AAPCS64: `ws` in `x0`) run the register-resident
field code that `vg_ed448_verify_equation` inlined (`Base.addOps`, `dblOps`)
on the slots where it keeps their operands, as functions and calls of them
built as `vg_gf448_r56_pow_p34` is (`asFn`, `fnCall`,
`Impl/X448/AArch64/Field56.lean`): each copies `ws` to `x3` and sets the
products' mask in `x12`, as that code expects, and keeps the callee-saved
registers it changes (`x21`–`x28`) in lanes of `v16`–`v19`, so that it needs
no stack.

Every address is `ws` plus a constant, and there are no branches: only the
pointer, which is public, may affect timing.
-/

namespace VG.Impl.Ed448.AArch64

open VG.AArch64
open VG.Impl.X448.AArch64 (slot T0 T1 T2 T3 T4 T5 T6 T7)

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

namespace Point56

/-- `vg_ed448_r56_point_add`: slots 6–8 added to slots 3–5. -/
def addFn : Prog isa :=
  asFn false (X448.AArch64.Fast.ops
    (Impl.X448.AArch64.Base.addOps (slot 3) (slot 4) (slot 5) (slot 6) (slot 7) (slot 8)))

/-- `vg_ed448_r56_point_double`: slots 3–5 doubled. -/
def doubleFn : Prog isa := asFn false (X448.AArch64.Fast.ops (dblOps (slot 3) (slot 4) (slot 5)))

def addCall : Prog isa := fnCall Spec.Ed448.Point56.addApi.name addFn
def doubleCall : Prog isa := fnCall Spec.Ed448.Point56.doubleApi.name doubleFn

/-- The three slots from `a` copied to the three from `o`. -/
def copy3 (o a : Nat) : List Instr :=
  Curve448.AArch64.copy (slot o) (slot a) ++ Curve448.AArch64.copy (slot (o + 1)) (slot (a + 1)) ++
    Curve448.AArch64.copy (slot (o + 2)) (slot (a + 2))

/-- The comb's `A := 16 A + B` (`A` in slots 0–2 and `B` in 3–5) by calls of
`vg_ed448_r56_point_add`: `B` kept in slots 0–2 and `A` moved to slots 3–5; `A` added to itself
(a copy in slots 6–8) four times, counted by `x1`, which the calls keep; `B` added; and the sum moved
to slots 0–2. -/
def combineMid : Prog isa :=
  .seq (.block (copy3 6 0 ++ copy3 0 3 ++ copy3 3 6 ++ [.movz .w .x1 4 0])) <|
  .seq (.loop (.seq (.block (copy3 6 3)) (.seq addCall (.block [.subImm .x .x1 .x1 1]))) (.nonzero .x .x1)) <|
  .seq (.block (copy3 6 0)) <| .seq addCall (.block (copy3 0 3))

/-- `combineMid`, with the return address kept in a lane of `v8`, which the calls keep. -/
def combineCall : Prog isa :=
  .seq (.block [.vop (.ins .d2 .v8 0 .x30)]) <| .seq combineMid (.block [.umov .x .x30 .v8 0])

/-! ## The comb's additions -/

/-- Where `vg_ed448_r56_comb_add` keeps `v8`–`v15`, with `x21`–`x28` in their upper halves: bytes
3968 to 4095 of its own working space, which its products do not write. -/
def CSAVE : Nat := 3968

/-- `ws` into `x3` and the mask into `x12`, `x21`–`x28` into the upper halves of `v8`–`v15`
(whose lower halves are callee-saved), and `v8`–`v15` stored at `CSAVE`. -/
def csave : List Instr :=
  [.addImm .x .x3 .x0 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] ++
  (List.range 8).map (fun k => .vop (.ins .d2 (Curve448.AArch64.Neon.V (8 + k)) 1
    (Impl.X448.AArch64.Fast.saved k))) ++
  (List.range 8).map (fun k => Curve448.AArch64.Neon.stq (8 + k) (CSAVE + 16 * k))

/-- `v8`–`v15` loaded back, and `x21`–`x28` from their upper halves. -/
def crestore : List Instr :=
  (List.range 8).map (fun k => Curve448.AArch64.Neon.ldq (8 + k) (CSAVE + 16 * k)) ++
  (List.range 8).map (fun k => .umov .x (Impl.X448.AArch64.Fast.saved k) (Curve448.AArch64.Neon.V (8 + k)) 1)

/-- `vg_ed448_r56_comb_add`: the comb's two affine additions (`Base.addAffine`), slots 6–7 to slots
0–2 and slots 8–9 to slots 3–5, whose AdvSIMD products use every vector register. -/
def combAddFn : Prog isa :=
  .seq (.block csave) <|
  .seq (.block (Impl.X448.AArch64.Base.addAffine (slot 0) (slot 1) (slot 2) (slot 6) (slot 7) ++
    Impl.X448.AArch64.Base.addAffine (slot 3) (slot 4) (slot 5) (slot 8) (slot 9))) (.block crestore)

def combAddCall : Prog isa := fnCall Spec.Ed448.Point56.combAddApi.name combAddFn

/-- Step `x19 = j` of a comb of `n` tables: both digits' entries of table `j`, negated for negative
digits, added to their accumulators by one call of `vg_ed448_r56_comb_add`. `x9` is nonzero while
another step follows. -/
def combStep (n : Nat) : Prog isa :=
  .seq (.block Impl.X448.AArch64.Base.digits) <| .seq (.block Impl.X448.AArch64.Base.select) <|
  .seq (.block (Impl.X448.AArch64.Base.negate (slot 6) (Impl.X448.AArch64.BITS + 4) (slot 10) ++
    Impl.X448.AArch64.Base.negate (slot 8) Impl.X448.AArch64.BITS (slot 10))) <|
  .seq combAddCall <| .block [.addImm .x .x19 .x19 1, .subImm .x .x9 .x19 n]

/-- The comb's `n` steps, with the return address kept in a lane of `v8`, which the calls keep. -/
def combLoop (n : Nat) : Prog isa :=
  .seq (.block [.vop (.ins .d2 .v8 0 .x30)]) <|
  .seq (.loop (combStep n) (.nonzero .x .x9)) (.block [.umov .x .x30 .v8 0])

end Point56

end VG.Impl.Ed448.AArch64
