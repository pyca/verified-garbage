module

import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym

/-!
# The addresses of statics, in the ARMv7 taint analysis

`taintSym L` makes the register `adrSym` puts the address of a static of `L`
in public, so code may load from the table through it; the address of any
other static stays secret, as in `taint`.
-/

namespace VG.Test.ArmTaintSym

open VG VG.Arm

/-- Forms the address of the static `T` and loads its first word. -/
def load : Prog isa := .block [.adrSym .r4 "T", .ldr .r5 .r4 0]

theorem load_ct : ConstantTime isa (fun _ => True) (Arm.Taint.AgreeS ["T"] (Taint.ofRegs [])) load :=
  VG.Taint.constantTime (A := taintSym ["T"]) (Taint.ofRegs []) (fun _ _ _ _ h => h) (by taint_decide)

/-- The taint after `is` under `taintSym L`, from nothing public. -/
def after (L : List String) (is : List Instr) : Option Arm.Taint.T :=
  is.foldl (fun τ i => τ.bind (Arm.Taint.stepS L · i)) (some (Taint.ofRegs []))

-- The address of a static of `L` is public, and the load through it is allowed.
example : (after ["T"] [.adrSym .r4 "T"]).map (Arm.Taint.pub · .r4) = some true := by decide
example : (after ["T"] [.adrSym .r4 "T", .ldr .r5 .r4 0]).isSome = true := by decide

-- The address of another static is not, and neither is the load through it.
example : (after ["U"] [.adrSym .r4 "T"]).map (Arm.Taint.pub · .r4) = some false := by decide
example : (after [] [.adrSym .r4 "T", .ldr .r5 .r4 0]).isSome = false := by decide

-- `taintSym` has an order for summaries (`LeFrame`): one that keeps `r0`.
taint_summary loadSum : (taintSym ["T"]) (Taint.ofRegs [.r0]) load keeping (Taint.ofRegs [.r0])

end VG.Test.ArmTaintSym
