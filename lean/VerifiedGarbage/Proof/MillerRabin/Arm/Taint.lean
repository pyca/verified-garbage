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
correctness.
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

theorem cE_taint : Cert (seqs (copyClr aE 0)) := ⟨_, by taint_decide⟩
theorem cB_taint : Cert (seqs (copyClr aB aX)) := ⟨_, by taint_decide⟩
theorem cOne_taint : Cert (seqs (copyClr aOne 9)) := ⟨_, by taint_decide⟩
theorem cM1_taint : Cert (seqs (copyClr aM1 10)) := ⟨_, by taint_decide⟩
theorem yOne_taint : Cert (copy aY aOne) := ⟨_, by taint_decide⟩

/-- The flag 0 and the count. -/
abbrev initBlock : List Instr :=
  [.mov .r1 (.imm 0), .str .r1 .r8 sF, .mov .r1 (.shifted .r9 .lsl 5), .dp .sub .r1 .r1 (.imm 65), .str .r1 .r8 sK]

theorem init_taint : Cert (.block initBlock) := ⟨_, by taint_decide⟩

/-- The pointer of `c`'s copy, the count of its words and the carry in. -/
abbrev bitHead : List Instr := ptr .r0 aE ++ [.dp .sub .lr .r9 (.imm 2), .mov .r11 (.imm 0)]

theorem bitHead_taint : Cert (.block bitHead) := ⟨_, by taint_decide⟩
theorem bitStore_taint : Cert (.block [.str .r11 .r8 sBit]) := ⟨_, by taint_decide⟩
theorem clrY_taint : Cert (.block (Impl.Rsa.Arm.Recover.clrTop aY)) := ⟨_, by taint_decide⟩
theorem sel_taint : Cert (sel aX aOne aB sBit) := ⟨_, by taint_decide⟩
theorem eq1_taint : Cert (eqS sE1 aY aOne aT) := ⟨_, by taint_decide⟩
theorem eq2_taint : Cert (eqS sE2 aY aM1 aT) := ⟨_, by taint_decide⟩
theorem flag_taint : Cert (.block (flagUpd ++ cntNext)) := ⟨_, by taint_decide⟩
theorem ret_taint : Cert (.block [.ldr .r0 .r8 sF]) := ⟨_, by taint_decide⟩

end VG.Proof.MillerRabin.Arm
