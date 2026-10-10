import VerifiedGarbage.Impl.Ed25519.Arm.Field
import VerifiedGarbage.Spec.Ed25519.Point16

/-!
# Ed25519's point addition and doubling on ARMv7, as functions

`vg_ed25519_r16_point_add(ws)` and `vg_ed25519_r16_point_double(ws)`
(`Spec/Ed25519/Point16.lean`; AAPCS: `ws` in `r0`) run the field code of the
inlined formulas (`pointAdd`, `pointDouble`) on the points where the callers
keep them, between saving the callee-saved registers that code changes
(`r4`–`r9`) at `SAVE` and restoring them (`asFn`), so that they need no
stack. They never write `r0`, `r10`, `r11` or `r12`.

Every address is `ws` plus a constant, and the only branches are the
products' row loops: only the pointer, which is public, may affect timing.
-/

namespace VG.Impl.Ed25519.Arm

open VG.Arm

/-- Where a function of point arithmetic saves each callee-saved register
it changes: `r4`–`r9`, and `r10` for the squaring loops' counter. -/
def regSlots (counter : Bool) : List (Reg × Nat) :=
  [(.r4, SAVE), (.r5, SAVE + 4), (.r6, SAVE + 8), (.r7, SAVE + 12), (.r8, SAVE + 16),
    (.r9, SAVE + 20)] ++ if counter then [(.r10, SAVE + 24)] else []

/-- `body` as a function: the registers saved, `body`, and the registers
restored. -/
def asFn (counter : Bool) (body : Prog isa) : Prog isa :=
  .seq (.block ((regSlots counter).map fun p => .str p.1 .r0 p.2))
    (.seq body (.block ((regSlots counter).map fun p => .ldr p.1 .r0 p.2)))

namespace Point16

/-- `vg_ed25519_r16_point_add`. -/
def addFn : Prog isa := asFn false pointAdd

/-- `vg_ed25519_r16_point_double`. -/
def doubleFn : Prog isa := asFn false pointDouble

/-- A call of `vg_ed25519_r16_point_add`. -/
def addCall : Prog isa := .call Spec.Ed25519.Point16.addApi.name addFn

/-- A call of `vg_ed25519_r16_point_double`. -/
def doubleCall : Prog isa := .call Spec.Ed25519.Point16.doubleApi.name doubleFn

end Point16

end VG.Impl.Ed25519.Arm
