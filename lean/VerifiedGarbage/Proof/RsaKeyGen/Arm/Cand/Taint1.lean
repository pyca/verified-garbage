module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint0
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint0
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A candidate on ARMv7: the taint analysis of the entry and the candidate's loads -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate

/-- The carry of `r1 − r2` made a value, then Z iff it is 0. -/
abbrev carryTail : List Instr := [.subs .r3 .r1 (.reg .r2), .mov .r3 (.imm 0), .adc .r3 .r3 (.imm 0), .cmp .r3 (.imm 0)]

theorem lenCheck_eq : lenCheck = ([.ldrSp .r1 aoRl, .ldrSp .r2 foL] : List Instr) ++ carryTail := rfl

theorem carryTail_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r1, .r2]) (.block carryTail) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `setupC` after the loads of `scratch` and `out_len`. -/
abbrev setupTail : List Instr :=
  [.mov .r9 (.shifted .r9 .lsr 2), .dp .add .r9 .r9 (.imm 2)] ++ stride ++
  [.str .r9 .r8 16, .dp .add .r0 .r8 (.imm (BitVec.ofNat 32 hdr)), .mov .lr (.imm (BitVec.ofNat 32 nArr)),
    .mul .lr .lr .r7, .mov .lr (.shifted .lr .lsr 2), .mov .r3 (.imm 0)]

theorem setupC_eq : setupC = ctxB ++ (([.ldrSp .r9 foL] : List Instr) ++ setupTail) := rfl

theorem setupTail_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8, .r9]) (.block setupTail) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A load with its pointer and length public. -/
abbrev LCert (j : Nat) : Prop := ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r6, .r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.CrtValues.load j) hc).isSome = true

theorem loadC_taint : LCert aC := ⟨_, by taint_decide⟩
theorem loadP_taint : LCert aPr := ⟨_, by taint_decide⟩
theorem loadE_taint : LCert aE := ⟨_, by taint_decide⟩
theorem loadX_taint : LCert aX := ⟨_, by taint_decide⟩

/-- The candidate's top bits. -/
abbrev topOps : List Instr := [.dp .orr .r1 .r1 (.imm 0xC0000000)]

theorem topBits_eq : topBits = ptr .r0 aC ++ .dp .add .r0 .r0 (.shifted .r9 .lsl 2) ::
    .dp .sub .r0 .r0 (.imm (BitVec.ofNat 32 12)) :: .ldr .r1 .r0 0 :: (topOps ++ ([.str .r1 .r0 0] : List Instr)) := rfl

theorem topBits_taint : Cert (.block topBits) := ⟨_, by taint_decide⟩
theorem orOneC_taint : Cert (.block (orOne aC)) := ⟨_, by taint_decide⟩
theorem one_taint : Cert (.block (VG.Impl.RsaKeyGen.Arm.Key.setWd aOne 0 1)) := ⟨_, by taint_decide⟩
theorem two_taint : Cert (.block (VG.Impl.RsaKeyGen.Arm.Key.setWd aTwo 0 2)) := ⟨_, by taint_decide⟩
theorem usedL_taint : Cert (.block [.str .r1 .r8 sUsed]) := ⟨_, by taint_decide⟩

theorem candBits_eq : candBits = ([.ldrSp .r1 foL] : List Instr) ++ (([.str .r1 .r8 sUsed] : List Instr) ++ (topBits ++ (orOne aC ++
    (VG.Impl.RsaKeyGen.Arm.Key.setWd aOne 0 1 ++ VG.Impl.RsaKeyGen.Arm.Key.setWd aTwo 0 2)))) := by
  simp only [candBits, List.append_assoc]; rfl

end VG.Proof.RsaKeyGen.Arm.Cand
