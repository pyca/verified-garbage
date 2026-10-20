module

public import VerifiedGarbage.Proof.Rsa.Arm.RvTaint2
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.Arm.RvTaint2
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # `vg_rsa_recover_primes` on ARMv7: the pieces of the candidates the taint analysis checks -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover

/-- `g := sCand + 2` into the low word of `[mG]`. -/
abbrev storeG : List Instr := ptr .r0 mG ++ [.ldr .r1 .r8 sCand, .dp .add .r1 .r1 (.imm 2), .str .r1 .r0 0]

/-- `cntBits` after the loads from the stack. -/
abbrev cntTail : List Instr := [.dp .add .r1 .r1 (.reg .r2), .mov .r1 (.shifted .r1 .lsl 3), .str .r1 .r8 sCnt]

theorem cntBits_eq : cntBits = ([(Reg.r1, aoEl), (Reg.r2, aoDl)].map fun p => Instr.ldrSp p.1 p.2) ++ cntTail := rfl

/-- `sqInit` before the count. -/
abbrev sqHead : List Instr :=
  [.ldr .r1 .r8 sE1, .ldr .r2 .r8 sE2, .dp .orr .r1 .r1 (.reg .r2), .str .r1 .r8 sDone,
    .mov .r1 (.imm 0), .str .r1 .r8 sOk, .str .r1 .r8 sK]

theorem sqInit_eq : sqInit = sqHead ++ cntBits := rfl

/-- The first block of a bit of `r`, after the context. -/
abbrev expTail : List Instr := bitOf sBit wRc ++ [.mov .r11 (.imm 0)]

theorem expHead_eq : ctxW ++ bitOf sBit wRc ++ ([.mov .r11 (.imm 0)] : List Instr) = ctxW ++ expTail := by
  simp only [List.append_assoc]

/-- `ok` into the mask. -/
abbrev okMask : List Instr := [.ldr .r1 .r8 sOk, .str .r1 .r8 sMask]

/-- The count of candidates to 0. -/
abbrev candZero : List Instr := [.mov .r1 (.imm 0), .str .r1 .r8 sCand]

theorem gZ_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (copy mG aZ) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem storeG_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (.block storeG) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem yO_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (copy mY aO) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem rcR_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (copy wRc wR) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cntTail_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (.block cntTail) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem expTail_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (.block expTail) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem halfRc_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (half wRc) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem selXm_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (sel mXm aO mG sBit) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cntNext_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (.block cntNext) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem eqY1_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (eqS sE1 mY aO aW) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem eqY2_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (eqS sE2 mY aNg aW) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem eqX1_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (eqS sE1 mX aO aW) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem eqX2_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (eqS sE2 mX aNg aW) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem sqHead_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (.block sqHead) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem sqMasks_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (.block sqMasks) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem uY_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (copy aU mY) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem selY_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (sel mY aU mX sLive) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem sqNext_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (.block sqNext) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem candNext_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (.block candNext) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem candZero_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (.block candZero) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem okMask_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (.block okMask) hc).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.Rsa.Arm.Recover
