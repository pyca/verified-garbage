module

-- separate module: the proof of Appendix C.2's body is split in a chain of modules, so that a change rebuilds only the modules after it
import VerifiedGarbage.Proof.Rsa.ProductExact
import VerifiedGarbage.Proof.Rsa.Arm.Stage.MM
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.KS
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ctx
import VerifiedGarbage.Proof.Rsa.Arm.KcOps
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops2
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops
public import VerifiedGarbage.Proof.Rsa.Arm.RdOps
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Tools
import VerifiedGarbage.Proof.Rsa.TwosMath
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Loads
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont2
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Views
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

/-! ### `Rsa.Arm.RdTaint`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Rsa.Arm.Stage.Prod`, which this module and modules that import it used -/

section

/-! # The ARMv7 key stages: before `M = d e`

After the loads, the arrays read with `W` words hold `0`, `e`, `d` (`AW1`), and
`e` is the narrow array `2 wE` (`LS.ksE`), from which `RecoverDet.prodW` takes
its rows.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

theorem bytes_lt (m : Mem) (a : Addr) (k : Nat) : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m a k) < 2 ^ (8 * k) := by
  have := VG.Proof.Rsa.lt_of_os2ip (Spec.Rsa.bytesAt m a k)
  rwa [VG.Proof.Rsa.Arm.CrtValues.bytesAt_length, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this

/-- The arrays with `W` words after the loads. -/
def AW1 (P : RP) (σ : State) : Nat → Nat := upd (upd (fun _ => 0) wE P.e) wD (dv P σ)

/-- After the loads: `e` live as the narrow array `2 wE`, and the wide array 14 (`RecoverDet.wZ`) zero. -/
theorem LS.ksE {P : RP} {σ s : State} (h : LS P σ (Aload P σ) s) :
    KS P σ (Aload P σ) [aN, 2 * wE] (AW1 P σ)
      [wZ, wE, wD,
        wM, 14] (fun _ => 0) [] s := by
  have sz := h.bs.pre.sizes
  have kw := sz.kw
  have hn : P.n < 2 ^ (32 * P.w) := by
    have := h.bs.pre.nB ▸ bytes_lt σ.mem (State.addr P.nP) P.K
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega_using [kw]))
  have he : P.e < 2 ^ (32 * P.w) := by
    have hb := h.bs.pre.eB ▸ bytes_lt σ.mem (State.addr P.eP) P.el
    have := h.bs.pre.el2
    exact Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (n := 2) (by decide) (show 8 * P.el ≤ 32 * P.w by omega_using [kw, this]))
  have nw : ∀ j < nArr, Aload P σ j < 2 ^ (32 * P.w) → num s.mem P.B P.w j = Aload P σ j := fun j hj hl => by
    rw [← h.full j hj] at hl ⊢
    exact VG.Proof.Rsa.Arm.CrtValues.val32_low2 hl
  have z : ∀ j < nArr, j ≠ aN → j ≠ 2 * wE →
      j ≠ 2 * wD → num s.mem P.B P.w j = 0 := fun j hj a b c => by
    rw [nw j hj (by simp only [Aload, upd, a, b, c, ↓reduceIte]; exact Nat.two_pow_pos _)]
    simp only [Aload, upd, a, b, c, ↓reduceIte]
  refine ⟨h.bs, h.ws.r8, h.cnt, ?_, ?_, by simp, ?_, ?_, by simp⟩
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact nw _ (by decide) (by simp only [Aload, upd]; simp; exact hn)
    · exact nw _ (by decide) (by simp only [Aload, upd]; simp; exact he)
  · intro j hj
    have zz : ∀ i, i = 1 ∨ i = 3 ∨ i = 5 ∨ i = 7 ∨ i = 29 → num s.mem P.B P.w i = 0 := fun i hi => by
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact z _ (by decide) (by decide) (by decide) (by decide)
    have z28 : num s.mem P.B P.w 28 = 0 := z _ (by decide) (by decide) (by decide) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl
    all_goals refine (numW_of (h.full _ (by decide)) (zz _ (by decide))).trans ?_
    all_goals simp [Aload, AW1, upd, aN, wE, wD, wZ, wM]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro j (rfl | rfl) <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro j (rfl | rfl | rfl | rfl | rfl) <;> decide

end VG.Proof.Rsa.Arm.Recover

end

end

/-! # `vg_rsa_recover_primes_det` on ARMv7: `d e - 1` and the halvings

From the product `d e` (`RecoverDet.prodW`): `x = d e - 1` and whether `d e ≥ 2`
(`deMinus_vp`); then `u = n - 1` and the `32 w` halvings (`twos_vp`), whose
step is any `f` with the halvings' formula (Appendix C.2's model,
`Proof/Rsa/RecoverDet.lean`, calls it `twoStep`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

/-- `M = d e`. -/
abbrev Mv (P : RP) (σ : State) : Nat := dv P σ * P.e

/-- The arrays with `W` words after the product. -/
def AWp (P : RP) (σ : State) : Nat → Nat := upd (AW1 P σ) wM (Mv P σ)

end VG.Proof.Rsa.Arm.Recover

namespace VG.Proof.Rsa.Arm.RecoverDet
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Recover
open VG.Impl.Rsa.Arm.Keys hiding aT1 aT2 aT3 aT4
open VG.Proof.X25519.Arm
open VG.Impl.Rsa.Arm.RecoverDet
open VG.Impl.Rsa.Arm.Recover (nArr)
open VG.Proof.Rsa (sub32 b2n)

/-- A stage: `E`, the key working space, and its context with `v` words. -/
abbrev Dk (P : RP) (E : State → Prop) (A : State → Nat → Nat) (L : List Nat) (AW : State → Nat → Nat)
    (LW : List Nat) (V : State → Nat → Nat) (LS : List Nat) (v N : Nat) (σ s : State) : Prop :=
  E σ ∧ KS P σ (A σ) L (AW σ) LW (V σ) LS s ∧ Ws s P.B P.Z v N

/-- `d e`, `d e - 1` modulo `2^(32 W)`, and whether `d e ≥ 2`. -/
abbrev deV (P : RP) (σ : State) : Nat := Mv P σ
abbrev xV (P : RP) (σ : State) : Nat := sub32 P.W (deV P σ) 1
abbrev okDEv (P : RP) (σ : State) : Bool := !(decide (deV P σ < 1) || decide (xV P σ < 1))

/-- After `deMinus`. -/
def AN (P : RP) : Nat → Nat := upd (fun _ => 0) aN P.n
def AW1 (P : RP) (σ : State) : Nat → Nat := upd (upd (upd (fun _ => 0) wZ 0) wOne 1) wX (xV P σ)
def V1 (P : RP) (σ : State) : Nat → Nat := upd (fun _ => 0) sOkDE (b2n (okDEv P σ))

section
variable {P : RP}

theorem ws_regs' {s₁ s₂ : State} {v N : Nat} (h₁ : Ws s₁ P.B P.Z v N) (h₂ : Ws s₂ P.B P.Z v N) :
    ∀ r ∈ ctxRegs, s₁.gpr r = s₂.gpr r := by
  simp only [ctxRegs, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · rw [h₁.r7, h₂.r7]
  · rw [h₁.r8, h₂.r8]
  · rw [h₁.r9, h₂.r9]

/-- A piece the taint analysis checks with `r7`–`r9` public, between stages
with the working space's context. -/
theorem VP.dctx {F G : State → State → Prop} {c : Prog isa} {v N : Nat} (cert : DCert c)
    (hws : ∀ σ s, F σ s → Ws s P.B P.Z v N) (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G :=
  VP.taint _ cert (fun _ _ _ _ h₁ h₂ => ws_regs' (hws _ _ h₁) (hws _ _ h₂)) wp

theorem b2n_lt_one (p : Prop) [Decidable p] : b2n (decide p) ≤ 1 := by
  unfold b2n; split <;> omega_using []

theorem b2n_nor (p q : Prop) [Decidable p] [Decidable q] :
    (if b2n (decide p) = 0 ∧ b2n (decide q) = 0 then 1 else 0) = b2n (!(decide p || decide q)) := by
  unfold b2n; by_cases a : p <;> by_cases b : q <;> simp [a, b]

theorem deMinus_ok {σ s : State}
    (h : KS P σ (Aload P σ) [VG.Impl.Rsa.Arm.Recover.aN] (AWp P σ)
      [VG.Impl.Rsa.Arm.Recover.wM, VG.Impl.Rsa.Arm.Recover.wZ] (fun _ => 0) [] s)
    (hw : Ws s P.B P.Z P.W 22) :
    WP isa deMinus s fun t => KS P σ (AN P) [aN] (AW1 P σ) [wX, wOne, wZ] (V1 P σ) [sOkDE] t ∧
      Ws t P.B P.Z P.W 22 := by
  simp only [deMinus, seqs]
  refine WP.seq (WP.mono (h.sub_W hw (o := wZ) (a := VG.Impl.Rsa.Arm.Recover.wM)
    (b := VG.Impl.Rsa.Arm.Recover.wM) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s1 ⟨h1, hw1, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h1.copy_W hw1 (o := wOne) (a := wZ) (by decide) (by decide) (by decide) (by decide))
    fun s2 ⟨h2, hw2, _⟩ => ?_)
  refine WP.seq (h2.setOne_W hw2 (j := wOne) (by decide) (by decide) fun s3 h3 hw3 _ => WP.block_nil ?_)
  refine WP.seq (WP.mono (h3.sub_W hw3 (o := wX) (a := VG.Impl.Rsa.Arm.Recover.wM) (b := wOne) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s4 ⟨h4, hw4, _, c4⟩ => ?_)
  refine WP.seq (h4.brw hw4 (d := sB0) (by decide) fun s5 h5 hw5 _ => WP.block_nil ?_)
  refine WP.seq (WP.mono (h5.sub_W hw5 (o := wT1) (a := wX) (b := wOne) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s6 ⟨h6, hw6, _, c6⟩ => ?_)
  refine h6.brw hw6 (d := sB1) (by decide) fun s7 h7 hw7 _ => ?_
  refine h7.norS hw7 (d := sOkDE) (a := sB0) (b := sB1) (by decide) (by decide)
    (by rw [upd_ne _ _ (by decide), upd_self, c4]; exact b2n_lt_one _)
    (by rw [upd_self, c6]; exact b2n_lt_one _) (by decide) fun t ht hwt => WP.block_nil ⟨?_, hwt⟩
  refine ht.mono (fun j hj => ?_) (fun j hj => ?_) (fun d hd => ?_)
  · simp only [List.mem_singleton] at hj; subst hj
    exact ⟨by decide, by simp only [AN, Aload]; rd_ev⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;> simp only [AW1, AWp, xV, deV] <;> rd_ev <;> simp [sub32]
  · simp only [List.mem_singleton] at hd; subst hd
    refine ⟨by decide, ?_⟩
    rw [upd_self, V1, upd_self, upd_self, upd_ne _ _ (show sB0 ≠ sB1 by decide), upd_self, c4, c6, b2n_nor]
    simp only [okDEv, xV, deV, AWp]
    rd_ev

theorem deMinus_vp {E : State → Prop} :
    VP (fun σ s => E σ ∧ KS P σ (Aload P σ) [VG.Impl.Rsa.Arm.Recover.aN] (AWp P σ)
      [VG.Impl.Rsa.Arm.Recover.wM, VG.Impl.Rsa.Arm.Recover.wZ] (fun _ => 0) [] s ∧
      Ws s P.B P.Z P.W 22) deMinus
      (Dk P E (fun _ => AN P) [aN] (AW1 P) [wX, wOne, wZ] (V1 P) [sOkDE] P.W 22) :=
  VP.dctx deMinus_taint (fun _ _ h => h.2.2) fun _ _ ⟨e, h, hw⟩ =>
    WP.mono (deMinus_ok h hw) fun _ ⟨ht, hwt⟩ => ⟨e, ht, hwt⟩

/-! ## The halvings -/

/-- `(u, x / 2^k, 2^k x)` after `k` halvings from `(n - 1, x mod 2^(32 w), x)`. -/
abbrev ts (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) (k : Nat) : Nat × Nat × Nat :=
  f^[k] (sub32 P.w P.n 1, xV P σ % 2 ^ (32 * P.w), xV P σ)

def AT (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) (k : Nat) : Nat → Nat :=
  upd (upd (upd (upd (upd (fun _ => 0) aOneN 1) aZN 0) aN P.n) aX2 (ts P f σ k).2.1) aU (ts P f σ k).1
def AWT (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) (k : Nat) : Nat → Nat :=
  upd (upd (upd (fun _ => 0) wZ 0) wOne 1) wX3 (ts P f σ k).2.2
def VT (P : RP) (σ : State) (k : Nat) : Nat → Nat :=
  upd (upd (fun _ => 0) sOkDE (b2n (okDEv P σ))) sK (32 * P.w - k)

abbrev LT : List Nat := [aU, aX2, aN, aZN, aOneN]
abbrev LWT : List Nat := [wX3, wOne, wZ]
abbrev LST : List Nat := [sK, sOkDE]

/-- After `k` halvings. -/
def TI (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) (k : Nat) (s : State) : Prop :=
  KS P σ (AT P f σ k) LT (AWT P f σ k) LWT (VT P σ k) LST s ∧ Ws s P.B P.Z P.w nArr

/-- The step of the halvings. -/
abbrev TwoF (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) : Prop :=
  ∀ u x y, f (u, x, y) = if u % 2 = 0 then
    (if x % 2 = 0 then (u / 2, x / 2, 2 * y % 2 ^ (32 * P.W)) else (u / 2, x, y)) else (u, x, y)

/-- A loop of `K ≥ 1` iterations whose body takes the stage `I k` to `I (k + 1)`, with Z when
`K - (k + 1) = 0`. -/
theorem VP.count {E : State → Prop} {I : Nat → State → State → Prop} {body : Prog isa} {K : Nat}
    (pos : 0 < K) (hb : ∀ k, k < K → VP (fun σ s => E σ ∧ I k σ s) body
      (fun σ s => (E σ ∧ I (k + 1) σ s) ∧ s.z = decide (K - (k + 1) = 0))) :
    VP (fun σ s => E σ ∧ I 0 σ s) (.loop body .ne) (fun σ s => E σ ∧ I K σ s) := by
  let J := fun n σ s => E σ ∧ n ≤ K ∧ I (K - n) σ s
  have hl := VP.loop (I := J) (body := body) (c := .ne) (Q := fun σ s => E σ ∧ I K σ s) (fun n => ?_)
  · refine (hl (K - 1)).mono (fun σ s ⟨e, h⟩ => ⟨e, by omega_using [pos], by rw [show K - (K - 1 + 1) = 0 by omega_using []]; exact h⟩)
      fun _ _ h => h
  · refine (VP.of_imp (p := n + 1 ≤ K) (fun σ s h => h.2.1) fun hn => ?_)
    refine (hb (K - (n + 1)) (by omega_using [pos])).mono (fun σ s ⟨e, _, h⟩ => ⟨e, h⟩) fun σ s ⟨⟨e, h⟩, z⟩ => ⟨?_, ?_, ?_⟩
    · show some (!s.z) = some (decide (0 < n))
      rw [z, show K - (K - (n + 1) + 1) = n by omega_using [hn]]
      by_cases h0 : n = 0 <;> simp [h0, Nat.pos_iff_ne_zero]
    · intro h0; subst h0; refine ⟨e, ?_⟩; rw [show K - (0 + 1) + 1 = K by omega_using [pos]] at h; exact h
    · intro hp; refine ⟨e, by omega_using [hn], ?_⟩; rw [show K - (n + 1) + 1 = K - n by omega_using [hn]] at h; exact h

end

end VG.Proof.Rsa.Arm.RecoverDet
