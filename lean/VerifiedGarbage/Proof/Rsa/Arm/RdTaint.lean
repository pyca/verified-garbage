module

public import VerifiedGarbage.Impl.Rsa.Arm.RecoverDet
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Taint2
public import VerifiedGarbage.Proof.Rsa.Arm.KdDivCT
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.RecoverDet
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Rsa.Arm.Stage.Taint2
meta import VerifiedGarbage.Proof.Rsa.Arm.KdDivCT
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # `vg_rsa_recover_primes_det` on ARMv7: the pieces the taint analysis checks

Between the division, `inverse` and the loops, each piece computes its
addresses and counts from `r7`–`r9` (`ctxRegs`), and switches between the
narrow and wide arrays from `r9` alone; the loads of `w` from the header
after a division need only `r8`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.RecoverDet
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.RecoverDet
open VG.Proof.Rsa.Arm.Recover (ctxRegs)

/-- A piece the taint analysis checks with `r7`–`r9` public. -/
abbrev DCert (c : Prog isa) : Prop := ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) c hc).isSome = true

theorem toW_taint : DCert (.block toW) := ⟨_, by taint_decide⟩
theorem toN_taint : DCert (.block toN) := ⟨_, by taint_decide⟩
theorem rowsInit_taint : DCert (.block rowsInit) := ⟨_, by taint_decide⟩
theorem copyA_taint : DCert (copy wA wZ) := ⟨_, by taint_decide⟩
theorem pRowA_taint : DCert (.block (pRowA wA)) := ⟨_, by taint_decide⟩
/-- The rest of a row, from its offset in `r2` and `[o]`'s address in `r0`. -/
abbrev RowCert (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r0, .r2, .r7, .r8, .r9]) c hc).isSome = true
theorem pRowBA_taint : RowCert (pRowB wX3 17) := ⟨_, by taint_decide⟩
theorem pRowBB_taint : RowCert (pRowB wB 2) := ⟨_, by taint_decide⟩
theorem copyM_taint : DCert (copy VG.Impl.Rsa.Arm.Recover.wM wZ) := ⟨_, by taint_decide⟩
theorem pRowAM_taint : DCert (.block (pRowA VG.Impl.Rsa.Arm.Recover.wM)) := ⟨_, by taint_decide⟩
theorem pRowBE_taint : RowCert (pRowBG VG.Impl.Rsa.Arm.Recover.wD VG.Impl.Rsa.Arm.Recover.wE cntE) := ⟨_, by taint_decide⟩
/-- `4 ⌈e_len / 4⌉` at `sRows`, from `e_len` (public) in `r1`. -/
theorem rowsE_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r1, .r7, .r8, .r9])
    (.block [.dp .add .r1 .r1 (.imm 3), .mov .r1 (.shifted .r1 .lsr 2), .mov .r1 (.shifted .r1 .lsl 2),
      .str .r1 .r8 sRows]) hc).isSome = true := ⟨_, by taint_decide⟩
theorem deMinus_taint : DCert deMinus := ⟨_, by taint_decide⟩
theorem gcdCopy_taint : DCert (copy aGx aX2) := ⟨_, by taint_decide⟩
theorem gcdPost_taint : DCert gcdPost := ⟨_, by taint_decide⟩
theorem divAPre_taint : DCert divAPre := ⟨_, by taint_decide⟩
/-- `4 s` from `n_len` in `r1`. -/
theorem shiftAmtB_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r1, .r7, .r8, .r9]) (.block shiftAmtB) hc).isSome =
    true := ⟨_, by taint_decide⟩
theorem copy3_taint : DCert (copy 3 wZ) := ⟨_, by taint_decide⟩
theorem copy12_taint : DCert (copy 12 wZ) := ⟨_, by taint_decide⟩
theorem copy15_taint : DCert (copy 15 wZ) := ⟨_, by taint_decide⟩
theorem copy0_taint : DCert (copy 0 wZ) := ⟨_, by taint_decide⟩
theorem copyR_taint : DCert (copy wR wZ) := ⟨_, by taint_decide⟩
theorem upA3_taint : DCert (.block (ptr .r0 3 ++ ([.ldr .r1 .r8 sS] : List Instr))) := ⟨_, by taint_decide⟩
theorem upA15_taint : DCert (.block (ptr .r0 15 ++ ([.ldr .r1 .r8 sS] : List Instr))) := ⟨_, by taint_decide⟩
theorem downA3_taint : DCert (.block (ptr .r10 3 ++ ([.ldr .r1 .r8 sS] : List Instr))) := ⟨_, by taint_decide⟩
theorem downA12_taint : DCert (.block (ptr .r10 12 ++ ([.ldr .r1 .r8 sS] : List Instr))) := ⟨_, by taint_decide⟩
/-- A shift's copy, from `4 s` in `r1` and an address in `r0` or `r10`. -/
abbrev ShiftCert (r : Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (Taint.ofRegs [r, .r1, .r7, .r8, .r9]) c hc).isSome = true
theorem upBA_taint : ShiftCert .r0 (shiftUpB wA) := ⟨_, by taint_decide⟩
theorem upBN_taint : ShiftCert .r0 (shiftUpB wN) := ⟨_, by taint_decide⟩
theorem downB12_taint : ShiftCert .r10 (shiftDownB 12) := ⟨_, by taint_decide⟩
theorem downBR_taint : ShiftCert .r10 (shiftDownB wR) := ⟨_, by taint_decide⟩
theorem eqAok_taint : DCert (eqS sAok wA 12 18) := ⟨_, by taint_decide⟩
theorem hdrW_taint : DCert (.block [.str .r9 .r8 16]) := ⟨_, by taint_decide⟩
theorem subLt_taint : DCert (sub3 wT1 wA wN) := ⟨_, by taint_decide⟩
theorem ltAok_taint : DCert (.block (brw sLt ++ andS sLt sLt sAok ++ toN)) := ⟨_, by taint_decide⟩
theorem wlInit_taint : DCert (.block (wlInit aM1)) := ⟨_, by taint_decide⟩
/-- A step of the word length, from its pointer `r0` and count `lr`. -/
theorem wlStep_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r0, .lr, .r7, .r8, .r9]) (.block wlStep) hc).isSome =
    true := ⟨_, by taint_decide⟩
theorem shAmtW_taint : DCert (.block shAmtW) := ⟨_, by taint_decide⟩
theorem copy5_taint : DCert (copy 5 wZ) := ⟨_, by taint_decide⟩
theorem copy6_taint : DCert (copy 6 wZ) := ⟨_, by taint_decide⟩
theorem copy2_taint : DCert (copy 2 wZ) := ⟨_, by taint_decide⟩
theorem copy10_taint : DCert (copy 10 aM1) := ⟨_, by taint_decide⟩
theorem copy12d_taint : DCert (copy 12 aD) := ⟨_, by taint_decide⟩
theorem stBit_taint : DCert (.block [.ldr .r1 .r8 sTk, .dp .and .r1 .r1 (.imm 1), .str .r1 .r8 sBit]) :=
  ⟨_, by taint_decide⟩
theorem copy18_taint : DCert (copy 18 wZ) := ⟨_, by taint_decide⟩
theorem upA18_taint : DCert (.block (ptr .r0 18 ++ ([.ldr .r1 .r8 sWs] : List Instr))) := ⟨_, by taint_decide⟩
theorem upB5_taint : ShiftCert .r0 (shiftUpB 5) := ⟨_, by taint_decide⟩
theorem upB6_taint : ShiftCert .r0 (shiftUpB 6) := ⟨_, by taint_decide⟩
theorem sel5_taint : DCert (sel 3 5 18 sBit) := ⟨_, by taint_decide⟩
theorem sel6_taint : DCert (sel 3 6 18 sBit) := ⟨_, by taint_decide⟩
theorem copy53_taint : DCert (copy 5 3) := ⟨_, by taint_decide⟩
theorem copy63_taint : DCert (copy 6 3) := ⟨_, by taint_decide⟩
theorem stEnd_taint : DCert (.block [.ldr .r1 .r8 sTk, .mov .r1 (.shifted .r1 .lsr 1), .str .r1 .r8 sTk,
    .ldr .r1 .r8 sWs, .mov .r1 (.shifted .r1 .lsl 1), .str .r1 .r8 sWs,
    .dp .sub .r1 .r1 (.shifted .r9 .lsl 1), .mov .r1 (.shifted .r1 .lsr 31), .cmp .r1 (.imm 0)]) := ⟨_, by taint_decide⟩
theorem eqExactW_taint : DCert (eqS sExact 7 wZ 18) := ⟨_, by taint_decide⟩
theorem copyDB_taint : DCert (copy aD aB) := ⟨_, by taint_decide⟩
theorem divBPre_taint : DCert divBPre := ⟨_, by taint_decide⟩
theorem squarePre_taint : DCert squarePre := ⟨_, by taint_decide⟩
theorem minus4n_taint : DCert minus4n := ⟨_, by taint_decide⟩
theorem factors_taint : DCert factors := ⟨_, by taint_decide⟩

theorem restoreW_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r8]) (.block restoreW) hc).isSome = true := ⟨_, by taint_decide⟩
theorem divAW_taint : VG.Proof.Rsa.Arm.KeyDiv.DivTaint 3 12 15 18 10 11 none (some wA) :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩
theorem divBW_taint : VG.Proof.Rsa.Arm.KeyDiv.DivTaint 6 7 5 8 15 21 none (some 2) :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem ctzU_taint : DCert (ctz aU sTu) := ⟨_, by taint_decide⟩
theorem ctzX_taint : DCert (ctz aX2 sKx) := ⟨_, by taint_decide⟩

theorem bitToU_taint0 : DCert (.block (bitTo sTu 0)) := ⟨_, by taint_decide⟩
theorem bitToU_taint1 : DCert (.block (bitTo sTu 1)) := ⟨_, by taint_decide⟩
theorem bitToU_taint2 : DCert (.block (bitTo sTu 2)) := ⟨_, by taint_decide⟩
theorem bitToU_taint3 : DCert (.block (bitTo sTu 3)) := ⟨_, by taint_decide⟩
theorem bitToU_taint4 : DCert (.block (bitTo sTu 4)) := ⟨_, by taint_decide⟩
theorem bitToU_taint : ∀ i, i < 5 → DCert (.block (bitTo sTu i))
  | 0, _ => bitToU_taint0
  | 1, _ => bitToU_taint1
  | 2, _ => bitToU_taint2
  | 3, _ => bitToU_taint3
  | 4, _ => bitToU_taint4
  | _ + 5, h => absurd h (by omega_using [])
theorem bitToK_taint0 : DCert (.block (bitTo sKv 0)) := ⟨_, by taint_decide⟩
theorem bitToK_taint1 : DCert (.block (bitTo sKv 1)) := ⟨_, by taint_decide⟩
theorem bitToK_taint2 : DCert (.block (bitTo sKv 2)) := ⟨_, by taint_decide⟩
theorem bitToK_taint3 : DCert (.block (bitTo sKv 3)) := ⟨_, by taint_decide⟩
theorem bitToK_taint4 : DCert (.block (bitTo sKv 4)) := ⟨_, by taint_decide⟩
theorem bitToK_taint : ∀ i, i < 5 → DCert (.block (bitTo sKv i))
  | 0, _ => bitToK_taint0
  | 1, _ => bitToK_taint1
  | 2, _ => bitToK_taint2
  | 3, _ => bitToK_taint3
  | 4, _ => bitToK_taint4
  | _ + 5, h => absurd h (by omega_using [])
theorem halfKT1_taint0 : DCert (halfK VG.Impl.Rsa.Arm.RecoverDet.aT1 (2 ^ 0)) := ⟨_, by taint_decide⟩
theorem halfKT1_taint1 : DCert (halfK VG.Impl.Rsa.Arm.RecoverDet.aT1 (2 ^ 1)) := ⟨_, by taint_decide⟩
theorem halfKT1_taint2 : DCert (halfK VG.Impl.Rsa.Arm.RecoverDet.aT1 (2 ^ 2)) := ⟨_, by taint_decide⟩
theorem halfKT1_taint3 : DCert (halfK VG.Impl.Rsa.Arm.RecoverDet.aT1 (2 ^ 3)) := ⟨_, by taint_decide⟩
theorem halfKT1_taint4 : DCert (halfK VG.Impl.Rsa.Arm.RecoverDet.aT1 (2 ^ 4)) := ⟨_, by taint_decide⟩
theorem halfKT1_taint : ∀ i, i < 5 → DCert (halfK VG.Impl.Rsa.Arm.RecoverDet.aT1 (2 ^ i))
  | 0, _ => halfKT1_taint0
  | 1, _ => halfKT1_taint1
  | 2, _ => halfKT1_taint2
  | 3, _ => halfKT1_taint3
  | 4, _ => halfKT1_taint4
  | _ + 5, h => absurd h (by omega_using [])

theorem shlKT1_taint0 : DCert (shlK wT1 (2 ^ 0)) := ⟨_, by taint_decide⟩
theorem shlKT1_taint1 : DCert (shlK wT1 (2 ^ 1)) := ⟨_, by taint_decide⟩
theorem shlKT1_taint2 : DCert (shlK wT1 (2 ^ 2)) := ⟨_, by taint_decide⟩
theorem shlKT1_taint3 : DCert (shlK wT1 (2 ^ 3)) := ⟨_, by taint_decide⟩
theorem shlKT1_taint4 : DCert (shlK wT1 (2 ^ 4)) := ⟨_, by taint_decide⟩
theorem shlKT1_taint : ∀ i, i < 5 → DCert (shlK wT1 (2 ^ i))
  | 0, _ => shlKT1_taint0
  | 1, _ => shlKT1_taint1
  | 2, _ => shlKT1_taint2
  | 3, _ => shlKT1_taint3
  | 4, _ => shlKT1_taint4
  | _ + 5, h => absurd h (by omega_using [])
theorem copyT1U_taint : DCert (copy VG.Impl.Rsa.Arm.RecoverDet.aT1 aU) := ⟨_, by taint_decide⟩
theorem copyT1X_taint : DCert (copy VG.Impl.Rsa.Arm.RecoverDet.aT1 aX2) := ⟨_, by taint_decide⟩
theorem copyWT1_taint : DCert (copy wT1 wX3) := ⟨_, by taint_decide⟩
theorem selU_taint : DCert (sel VG.Impl.Rsa.Arm.RecoverDet.aT2 aU VG.Impl.Rsa.Arm.RecoverDet.aT1 sBit) := ⟨_, by taint_decide⟩
theorem selX_taint : DCert (sel VG.Impl.Rsa.Arm.RecoverDet.aT2 aX2 VG.Impl.Rsa.Arm.RecoverDet.aT1 sBit) := ⟨_, by taint_decide⟩
theorem selW_taint : DCert (sel wT2 wX3 wT1 sBit) := ⟨_, by taint_decide⟩
theorem copyUT2_taint : DCert (copy aU VG.Impl.Rsa.Arm.RecoverDet.aT2) := ⟨_, by taint_decide⟩
theorem copyXT2_taint : DCert (copy aX2 VG.Impl.Rsa.Arm.RecoverDet.aT2) := ⟨_, by taint_decide⟩
theorem copyWT2_taint : DCert (copy wX3 wT2) := ⟨_, by taint_decide⟩
theorem twosInit_taint : DCert twosInit := ⟨_, by taint_decide⟩
theorem kMin_taint : DCert (.block kMin) := ⟨_, by taint_decide⟩

theorem copyT1Z_taint : DCert (copy VG.Impl.Rsa.Arm.RecoverDet.aT1 aZN) := ⟨_, by taint_decide⟩
theorem ptrU_taint : DCert (.block (ptr .r10 aU ++ ([.ldr .r1 .r8 sWs] : List Instr))) := ⟨_, by taint_decide⟩
theorem ptrX_taint : DCert (.block (ptr .r10 aX2 ++ ([.ldr .r1 .r8 sWs] : List Instr))) := ⟨_, by taint_decide⟩
theorem downT1_taint : ShiftCert .r10 (shiftDownB VG.Impl.Rsa.Arm.RecoverDet.aT1) := ⟨_, by taint_decide⟩
theorem copyWT1Z_taint : DCert (copy wT1 wZ) := ⟨_, by taint_decide⟩
theorem ptrWT1_taint : DCert (.block (ptr .r0 wT1 ++ ([.ldr .r1 .r8 sWs] : List Instr))) := ⟨_, by taint_decide⟩
theorem upBX3_taint : ShiftCert .r0 (shiftUpB wX3) := ⟨_, by taint_decide⟩
theorem stBitK_taint : DCert (.block [.ldr .r1 .r8 sKk, .dp .and .r1 .r1 (.imm 1), .str .r1 .r8 sBit]) :=
  ⟨_, by taint_decide⟩
theorem wsEnd_taint : DCert (.block [.ldr .r1 .r8 sTk, .mov .r1 (.shifted .r1 .lsr 1), .str .r1 .r8 sTk,
    .ldr .r1 .r8 sKk, .mov .r1 (.shifted .r1 .lsr 1), .str .r1 .r8 sKk,
    .ldr .r1 .r8 sWs, .mov .r1 (.shifted .r1 .lsl 1), .str .r1 .r8 sWs,
    .dp .sub .r1 .r1 (.shifted .r9 .lsl 2), .mov .r1 (.shifted .r1 .lsr 31), .cmp .r1 (.imm 0)]) := ⟨_, by taint_decide⟩

/-! The square root's stages. -/
theorem bitToLz_taint1 : DCert (.block (bitTo sLz 1)) := ⟨_, by taint_decide⟩
theorem bitToLz_taint2 : DCert (.block (bitTo sLz 2)) := ⟨_, by taint_decide⟩
theorem bitToLz_taint3 : DCert (.block (bitTo sLz 3)) := ⟨_, by taint_decide⟩
theorem bitToLz_taint4 : DCert (.block (bitTo sLz 4)) := ⟨_, by taint_decide⟩
theorem bitToLz_taint : ∀ i, 1 ≤ i → i < 5 → DCert (.block (bitTo sLz i))
  | 1, _, _ => bitToLz_taint1
  | 2, _, _ => bitToLz_taint2
  | 3, _, _ => bitToLz_taint3
  | 4, _, _ => bitToLz_taint4
  | 0, h, _ => absurd h (by omega_using [])
  | _ + 5, _, h => absurd h (by omega_using [])
theorem shlKG_taint0 : DCert (shlK wG (2 ^ 0)) := ⟨_, by taint_decide⟩
theorem shlKG_taint1 : DCert (shlK wG (2 ^ 1)) := ⟨_, by taint_decide⟩
theorem shlKG_taint2 : DCert (shlK wG (2 ^ 2)) := ⟨_, by taint_decide⟩
theorem shlKG_taint3 : DCert (shlK wG (2 ^ 3)) := ⟨_, by taint_decide⟩
theorem shlKG_taint4 : DCert (shlK wG (2 ^ 4)) := ⟨_, by taint_decide⟩
theorem shlKG_taint : ∀ i, i < 5 → DCert (shlK wG (2 ^ i))
  | 0, _ => shlKG_taint0
  | 1, _ => shlKG_taint1
  | 2, _ => shlKG_taint2
  | 3, _ => shlKG_taint3
  | 4, _ => shlKG_taint4
  | _ + 5, h => absurd h (by omega_using [])

theorem halfKHG_taint0 : DCert (halfKH wG (2 ^ 0)) := ⟨_, by taint_decide⟩
theorem halfKHG_taint1 : DCert (halfKH wG (2 ^ 1)) := ⟨_, by taint_decide⟩
theorem halfKHG_taint2 : DCert (halfKH wG (2 ^ 2)) := ⟨_, by taint_decide⟩
theorem halfKHG_taint3 : DCert (halfKH wG (2 ^ 3)) := ⟨_, by taint_decide⟩
theorem halfKHG_taint4 : DCert (halfKH wG (2 ^ 4)) := ⟨_, by taint_decide⟩
theorem halfKHG_taint : ∀ i, i < 5 → DCert (halfKH wG (2 ^ i))
  | 0, _ => halfKHG_taint0
  | 1, _ => halfKHG_taint1
  | 2, _ => halfKHG_taint2
  | 3, _ => halfKHG_taint3
  | 4, _ => halfKHG_taint4
  | _ + 5, h => absurd h (by omega_using [])
theorem copyGR_taint : DCert (copy wG wR) := ⟨_, by taint_decide⟩
theorem selFRG_taint : DCert (sel wF wR wG sBit) := ⟨_, by taint_decide⟩
theorem copyRF_taint : DCert (copy wR wF) := ⟨_, by taint_decide⟩
theorem copyGSH_taint : DCert (copyH wG wS) := ⟨_, by taint_decide⟩
theorem selFSGH_taint : DCert (selH wF wS wG sBit) := ⟨_, by taint_decide⟩
theorem copySFH_taint : DCert (copyH wS wF) := ⟨_, by taint_decide⟩
theorem copyGZH_taint : DCert (copyH wG wZ) := ⟨_, by taint_decide⟩
theorem copyGZ_taint : DCert (copy wG wZ) := ⟨_, by taint_decide⟩
theorem ptrG_taint : DCert (.block (ptr .r0 wG ++ ([.ldr .r1 .r8 sWs] : List Instr))) := ⟨_, by taint_decide⟩
theorem upBR_taint : ShiftCert .r0 (shiftUpB wR) := ⟨_, by taint_decide⟩
theorem ptrS_taint : DCert (.block (ptr .r10 wS ++ ([.ldr .r1 .r8 sWs] : List Instr))) := ⟨_, by taint_decide⟩
theorem downGH_taint : ShiftCert .r10 (shiftDownBH wG) := ⟨_, by taint_decide⟩
theorem stageNextH_taint : DCert (.block stageNextH) := ⟨_, by taint_decide⟩
theorem stageNext_taint : DCert (.block stageNext) := ⟨_, by taint_decide⟩
theorem bitToTk_taint : DCert (.block (bitTo sTk 0)) := ⟨_, by taint_decide⟩

theorem eqSZ_taint : DCert (eqS sZ wR wZ 18) := ⟨_, by taint_decide⟩
theorem bumpZ_taint : DCert (.block (([.ldr .r2 .r8 sZ] : List Instr) ++ ptr .r0 wR ++
    ([.ldr .r1 .r0 0, .dp .orr .r1 .r1 (.reg .r2), .str .r1 .r0 0] : List Instr))) := ⟨_, by taint_decide⟩
theorem lzW_taint : DCert (lzW wR sLz) := ⟨_, by taint_decide⟩
theorem normMid_taint : DCert (.block [.ldr .r1 .r8 sLz, .mov .r1 (.shifted .r1 .lsr 5), .str .r1 .r8 sTk,
    .mov .r1 (.imm 4), .str .r1 .r8 sWs]) := ⟨_, by taint_decide⟩

theorem isqTop_taint : DCert isqTop := ⟨_, by taint_decide⟩
theorem recip_taint : DCert VG.Impl.Rsa.Arm.KeyDiv.recip := ⟨_, by taint_decide⟩
theorem subEZOne_taint : DCert (sub3 wE wZ wOne) := ⟨_, by taint_decide⟩

/-! The square root's digits. -/
theorem clr11_taint : DCert (.block clr11) := ⟨_, by taint_decide⟩
theorem cntNext_taint : DCert (.block cntNext) := ⟨_, by taint_decide⟩
/-- Pieces that add the offset in `r1` to the address in `r10`, the same in both runs. -/
abbrev OffCert (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r1, .r10, .r7, .r8, .r9]) c hc).isSome = true
theorem estPtr_taint : DCert (.block estPtr) := ⟨_, by taint_decide⟩
theorem estOff_taint : OffCert (.block estOff) := ⟨_, by taint_decide⟩
theorem estBody_taint : OffCert (.block estBody) := ⟨_, by taint_decide⟩
/-- A block from some registers the same in both runs. -/
abbrev PCert (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (Taint.ofRegs (rs ++ [.r7, .r8, .r9])) c hc).isSome = true
theorem ldCm3_taint : DCert (.block [.ldr .r3 .r8 sCm]) := ⟨_, by taint_decide⟩
theorem setQ_taint : PCert [.r3] (.block setQ) := ⟨_, by taint_decide⟩
theorem ptrsE_taint : DCert (.block (dPtrs wE)) := ⟨_, by taint_decide⟩
theorem ptrsD_taint : DCert (.block (dPtrs wD)) := ⟨_, by taint_decide⟩
/-- The row from `r0`, `r12` and `lr`, the same in both runs. -/
abbrev RowNCert (c : Prog isa) : Prop := PCert [.r0, .r12, .lr] c
theorem msRow_taint : RowNCert (.seq (.block [.ldr .r1 .r8 VG.Impl.Rsa.Arm.KeyDiv.sQ, .mov .r11 (.reg .r1)])
    (.seq VG.Impl.Bignum.Arm.row (.block (([.ldr .r2 .r0 0, .dp .add .r2 .r2 (.reg .r11),
    .dp .sub .r2 .r2 (.reg .r1), .str .r2 .r0 0] : List Instr) ++ VG.Impl.Rsa.Arm.Recover.ctxW)))) :=
  ⟨_, by taint_decide⟩
theorem corrRow_taint : RowNCert (.seq (.block corrPre) (.seq VG.Impl.Bignum.Arm.maskRow (.block corrPost))) :=
  ⟨_, by taint_decide⟩
theorem corrSet_taint : PCert [.r4] (.block corrSet) := ⟨_, by taint_decide⟩
theorem ldCm1_taint : DCert (.block [.ldr .r1 .r8 sCm]) := ⟨_, by taint_decide⟩
theorem finishQ_taint : PCert [.r1] (.block finishQ) := ⟨_, by taint_decide⟩
theorem finishD1_taint : DCert (.block finishD1) := ⟨_, by taint_decide⟩
theorem digNext_taint : DCert (.block digNext) := ⟨_, by taint_decide⟩

/-! The square root's prelude and finish. -/
theorem copyDZw_taint : DCert (copy wD wZ) := ⟨_, by taint_decide⟩
theorem copyFZw_taint : DCert (copy wF wZ) := ⟨_, by taint_decide⟩
theorem copySD_taint : DCert (copy wS wD) := ⟨_, by taint_decide⟩
theorem halfS_taint : DCert (half wS) := ⟨_, by taint_decide⟩
theorem sqInit_taint : DCert (.block sqInit) := ⟨_, by taint_decide⟩
theorem eqOk5W_taint : DCert (eqS sOk5 wR wZ 18) := ⟨_, by taint_decide⟩
theorem sqMid_taint : DCert (.block sqMid) := ⟨_, by taint_decide⟩
theorem selGSZH_taint : DCert (selH wG wS wZ sZ) := ⟨_, by taint_decide⟩
theorem copyY22_taint : DCert (copy aY 22) := ⟨_, by taint_decide⟩

end VG.Proof.Rsa.Arm.RecoverDet
