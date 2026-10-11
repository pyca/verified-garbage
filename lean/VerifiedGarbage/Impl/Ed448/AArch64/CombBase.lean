import VerifiedGarbage.Impl.Ed448.AArch64.Point56
import VerifiedGarbage.Spec.Ed448.Comb56

/-!
# Ed448's fixed-base comb on AArch64, as a function

`vg_ed448_r56_comb_base(ws = x0, n = x1)`: the comb's two sums, `A` in slots 0–2 and `C` in slots
3–5, for the scalar `k` whose `8 n` bits are bytes at `BITS`, by X448's comb
(`Impl/X448/AArch64/Base.lean`) of `n` tables, `n` 56 (X448) or 57 (Ed448): both accumulators at
`[G] B` for that `n` (`init`), and the `n` steps (`Base.stepR`, whose loop ends at the counter
`x19 = x30`, which holds `n`). X448's multiplication of the base point, Ed448's and Ed448's
verification call it (`call`), and compute `[k] B = 16 A + C` (`Point56.combineCall`).

The steps' AdvSIMD products use every vector register and `x21`–`x28` (the even digit's masks
and the products' scalar halves): so the function keeps `x21`–`x28` in the upper halves of
`v8`–`v15`, whose lower halves are callee-saved, stores those at `CSAVE` in the products' bytes,
which the steps do not store to, and loads them back at the end; and it keeps `x19`, the steps'
counter, and the return address, at `XSAVE`, after slot 21's element: the steps use every other
register, so `x30` holds `n` while they run, and is loaded back before the return.
-/

namespace VG.Impl.Ed448.AArch64.CombBase

open VG.AArch64
open VG.Impl.X448.AArch64 (st ld)
open VG.Impl.X448.AArch64.Base (accs stepR)

/-- Where `v8`–`v15` are stored while the steps run: in the products' bytes, which the steps do
not store to. -/
def CSAVE : Nat := 3968

/-- Where `x19` and the return address are stored while the steps run: after slot 21's element. -/
def XSAVE : Nat := 2816

/-- `ws` into `x3` and the mask into `x12`, `x21`–`x28` into the upper halves of `v8`–`v15`
(whose lower halves are callee-saved), `v8`–`v15` stored at `CSAVE`, `x19` and `x30` at `XSAVE`,
and `n` into `x30`. -/
def save : List Instr :=
  [.addImm .x .x3 .x0 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] ++
  (List.range 8).map (fun k => .vop (.ins .d2 (Curve448.AArch64.Neon.V (8 + k)) 1
    (Impl.X448.AArch64.Fast.saved k))) ++
  (List.range 8).map (fun k => Curve448.AArch64.Neon.stq (8 + k) (CSAVE + 16 * k)) ++
  [st .x19 XSAVE, st .x30 (XSAVE + 8), .addImm .x .x30 .x1 0]

/-- `v8`–`v15` loaded back, and `x21`–`x28` from their upper halves. -/
def restore : List Instr :=
  (List.range 8).map (fun k => Curve448.AArch64.Neon.ldq (8 + k) (CSAVE + 16 * k)) ++
  (List.range 8).map (fun k => .umov .x (Impl.X448.AArch64.Fast.saved k) (Curve448.AArch64.Neon.V (8 + k)) 1)

/-- Both accumulators at `[G] B` for `n = x30` (`baseG57` for 57, `baseG` for 56), and the
counter at 0. -/
def init : Prog isa :=
  .seq (.block [.subImm .x .x9 .x30 56])
    (.ite (.nonzero .x .x9) (.block (accs Impl.X448.baseG57)) (.block (accs Impl.X448.baseG)))

/-- `vg_ed448_r56_comb_base`. -/
def combBaseFn : Prog isa :=
  .seq (.block save) <| .seq init <| .seq (.loop stepR (.nonzero .x .x9)) <|
  .block (restore ++ [ld .x19 XSAVE, ld .x30 (XSAVE + 8)])

/-- A call of `vg_ed448_r56_comb_base` for `n` tables (from `ws` in `x3`), the return address kept
in a lane of `v8`, which the function keeps. -/
def call (n : Nat) : Prog isa :=
  .seq (.block [.vop (.ins .d2 .v8 0 .x30), .movz .x .x1 n 0]) <|
  .seq (fnCall Spec.Ed448.Comb56.combBaseApi.name combBaseFn)
    (.block [.umov .x .x30 .v8 0])

end VG.Impl.Ed448.AArch64.CombBase
