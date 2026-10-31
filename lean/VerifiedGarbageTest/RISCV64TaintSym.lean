module

import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym

/-!
# The addresses of statics, in the RISC-V taint analysis

`taintSym L` makes the register `lla` puts the address of a static of `L` in
public, so code may load from the table through it; the address of any other
static stays secret, as in `taint`.
-/

namespace VG.Test.RISCV64TaintSym

open VG VG.RISCV64

/-- Forms the address of the static `T` and loads its second word. -/
def load : Prog isa := .block [.lla .a4 "T", .load .d .a5 .a4 8]

theorem load_ct :
    ConstantTime isa (fun _ => True) (RISCV64.Taint.AgreeS ["T"] (Taint.ofRegs [])) load :=
  VG.Taint.constantTime (A := taintSym ["T"]) (Taint.ofRegs []) (fun _ _ _ _ h => h) (by taint_decide)

/-- The taint after `is` under `taintSym L`, from nothing public. -/
def after (L : List String) (is : List Instr) : Option RISCV64.Taint.T :=
  is.foldl (fun τ i => τ.bind (RISCV64.Taint.stepS L · i)) (some (Taint.ofRegs []))

-- The address of a static of `L` is public, and the load through it is allowed.
example : (after ["T"] [.lla .a4 "T"]).map (RISCV64.Taint.pub · .a4) = some true := by decide
example : (after ["T"] [.lla .a4 "T", .load .d .a5 .a4 8]).isSome = true := by decide

-- The address of another static is not, and neither is the load through it.
example : (after ["U"] [.lla .a4 "T"]).map (RISCV64.Taint.pub · .a4) = some false := by decide
example : (after [] [.lla .a4 "T", .load .d .a5 .a4 8]).isSome = false := by decide

-- In `taint`, it is secret: it makes a public register secret.
example : (RISCV64.Taint.step (Taint.ofRegs [.a4]) (.lla .a4 "T")).map (RISCV64.Taint.pub · .a4) =
    some false := by decide

end VG.Test.RISCV64TaintSym
