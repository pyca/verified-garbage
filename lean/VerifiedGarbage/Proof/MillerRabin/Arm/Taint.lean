module

public import VerifiedGarbage.Impl.MillerRabin.Arm.Round
meta import VerifiedGarbage.Impl.MillerRabin.Arm.Round
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The Miller–Rabin round on ARMv7: the pieces the taint analysis checks

Each piece between the loads from the stack and the Montgomery products
computes its addresses and loop counts from `r0` (`ws`, for the context) or
from `r7`–`r9` (the key view's registers), which two runs agree on by
correctness; the load of a word of the exponent also from the count of
windows left in `r1`, which is public too.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm

/-- The key view's registers. -/
abbrev kRegs : List Reg := [.r7, .r8, .r9]

/-- A piece the taint analysis checks with `r7`–`r9` public. -/
abbrev Cert (c : Prog isa) : Prop := ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs kRegs) c hc).isSome = true

theorem ctx_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0]) (.block ctx) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cT0_taint : Cert (seqs (copyClr aT0 9)) := ⟨_, by taint_decide⟩
theorem cM1_taint : Cert (seqs (copyClr aM1 10)) := ⟨_, by taint_decide⟩
theorem clrX_taint : Cert (.block (Impl.Rsa.Arm.Recover.clrTop aX)) := ⟨_, by taint_decide⟩
theorem clrY_taint : Cert (.block (Impl.Rsa.Arm.Recover.clrTop aY)) := ⟨_, by taint_decide⟩
theorem cT1_taint : Cert (copy (aT0 + 1) aX) := ⟨_, by taint_decide⟩
theorem cYX_taint : Cert (copy aY aX) := ⟨_, by taint_decide⟩
theorem cY0_taint : Cert (copy aY aT0) := ⟨_, by taint_decide⟩

theorem tabCnt_taint : Cert (.block tabCnt) := ⟨_, by taint_decide⟩
theorem shift_taint : Cert tabShift := ⟨_, by taint_decide⟩
theorem cnt_taint : Cert (.block cntNext) := ⟨_, by taint_decide⟩

theorem winCnt_taint : Cert (.block winCnt) := ⟨_, by taint_decide⟩
theorem sqFour_taint : Cert (.block sqFour) := ⟨_, by taint_decide⟩
theorem eq1_taint : Cert (eqS sE1 aY aT0 aX) := ⟨_, by taint_decide⟩
theorem eq2_taint : Cert (eqS sE2 aY aM1 aX) := ⟨_, by taint_decide⟩
theorem sqFlag_taint : Cert (.block sqFlag) := ⟨_, by taint_decide⟩
theorem scan_taint : Cert scan := ⟨_, by taint_decide⟩
theorem winEnd_taint : Cert (.block winEnd) := ⟨_, by taint_decide⟩
theorem wordK_taint : Cert (.block wordK) := ⟨_, by taint_decide⟩

/-- The load of the word of the exponent, with the count in `r1` public too. -/
theorem wordLd_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r1, .r7, .r8, .r9]) (.block wordLd) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem wordEnd_taint : Cert (.block wordEnd) := ⟨_, by taint_decide⟩
theorem lowBits_taint : Cert (.block lowBits) := ⟨_, by taint_decide⟩
theorem ret_taint : Cert (.block [.ldr .r0 .r8 sF]) := ⟨_, by taint_decide⟩

end VG.Proof.MillerRabin.Arm
