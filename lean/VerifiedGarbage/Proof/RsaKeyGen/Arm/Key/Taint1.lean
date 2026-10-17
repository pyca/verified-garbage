module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint0
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint0
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # An RSA key on ARMv7: the pieces of `p`, `q` and `lcm(p − 1, q − 1)` the taint analysis checks -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key

theorem ltPQ_taint : Cert (seqs (ltS sLt aP0 aQ0)) := ⟨_, by taint_decide⟩
theorem selP_taint : Cert (sel aP aP0 aQ0 sLt) := ⟨_, by taint_decide⟩
theorem selQ_taint : Cert (sel aQ aQ0 aP0 sLt) := ⟨_, by taint_decide⟩
theorem ltP1_taint : Cert (seqs (ltS sPz aP aOne)) := ⟨_, by taint_decide⟩
theorem selPm_taint : Cert (sel aPm aTmp aZero sPz) := ⟨_, by taint_decide⟩
theorem ltQ1_taint : Cert (seqs (ltS sQz aQ aOne)) := ⟨_, by taint_decide⟩
theorem selQm_taint : Cert (sel aQm aTmp aZero sQz) := ⟨_, by taint_decide⟩

theorem myQm_taint : Cert (copy aMy aQm) := ⟨_, by taint_decide⟩
theorem mxPm_taint : Cert (copy aMx aPm) := ⟨_, by taint_decide⟩
theorem maZero_taint : Cert (copy aMa aZero) := ⟨_, by taint_decide⟩
theorem fMa_taint : Cert (copy aF aMa) := ⟨_, by taint_decide⟩
theorem uPm_taint : Cert (copy aU aPm) := ⟨_, by taint_decide⟩
theorem vQm_taint : Cert (copy aV aQm) := ⟨_, by taint_decide⟩

/-- The tail of `bothEven`: `sH := ¬(sBu ∨ sBv)`. -/
abbrev norTail : List Instr :=
  [.ldr .r1 .r8 sBu, .ldr .r2 .r8 sBv, .dp .orr .r1 .r1 (.reg .r2), .dp .eor .r1 .r1 (.imm 1), .str .r1 .r8 sH]

theorem bothEven_eq : bothEven = bitOf sBu aU ++ (bitOf sBv aV ++ norTail) := by
  simp only [bothEven, List.append_assoc]

theorem bitU_taint : Cert (.block (bitOf sBu aU)) := ⟨_, by taint_decide⟩
theorem bitV_taint : Cert (.block (bitOf sBv aV)) := ⟨_, by taint_decide⟩
theorem nor_taint : Cert (.block norTail) := ⟨_, by taint_decide⟩
theorem tU_taint : Cert (copy aTmp aU) := ⟨_, by taint_decide⟩
theorem tV_taint : Cert (copy aTmp aV) := ⟨_, by taint_decide⟩
theorem tF_taint : Cert (copy aTmp aF) := ⟨_, by taint_decide⟩
theorem t2U_taint : Cert (copy aTmp2 aU) := ⟨_, by taint_decide⟩
theorem t2V_taint : Cert (copy aTmp2 aV) := ⟨_, by taint_decide⟩
theorem t2F_taint : Cert (copy aTmp2 aF) := ⟨_, by taint_decide⟩
theorem sU_taint : Cert (sel aU aTmp aTmp2 sH) := ⟨_, by taint_decide⟩
theorem sV_taint : Cert (sel aV aTmp aTmp2 sH) := ⟨_, by taint_decide⟩
theorem sF_taint : Cert (sel aF aTmp aTmp2 sH) := ⟨_, by taint_decide⟩

theorem cntDown_taint : Cert (.block cntDown) := ⟨_, by taint_decide⟩
theorem strHc_taint : Cert (.block [.str .r6 .r8 sHc]) := ⟨_, by taint_decide⟩

end VG.Proof.RsaKeyGen.Arm.Key
