module
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.AArch64
public import VerifiedGarbage.Proof.CmacTripleDes.AArch64.RoundLit
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Implies
public import VerifiedGarbage.Impl.StackScratch.AArch64

import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Verified
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

/-!
# Streaming TDEA-CMAC on AArch64, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackScratch`): 640 bytes, and 688 for `absorb`. Their code uses
no other stack: it calls nothing, and the return address stays in `x30`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.AArch64

open VG VG.AArch64 VG.Impl.CmacTripleDes.Stream.AArch64

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition,
without the working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 416⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesStreamInitContract AArch64.abi 640).pre s := by
  implies_sat [Spec.Cmac.tdesStreamInitContract, Spec.Cmac.tdesStreamInitSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, AArch64.abi, AArch64.argRegs] [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition, without
the working space (and with no data). -/
def absorbFrameSat : State := { absorbSat with wr := [⟨0x1000, 416⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.tdesAbsorbContract AArch64.abi 688).pre s := by
  implies_sat [Spec.Cmac.tdesAbsorbContract, Spec.Cmac.tdesAbsorbSig, Spec.Cmac.tdesAbsorbPost,
    AArch64.abi, AArch64.argRegs] [absorbFrameSat, absorbSat] using absorbFrameSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition, without
the working space. -/
def finishFrameSat : State := { finishSat with wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.tdesFinishContract AArch64.abi 640).pre s := by
  implies_sat [Spec.Cmac.tdesFinishContract, Spec.Cmac.tdesFinishSig, Spec.Cmac.tdesFinishPost,
    AArch64.abi, AArch64.argRegs] [finishFrameSat, finishSat] using finishFrameSat

theorem init_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 640 .x3 streamInit)
      (Spec.Cmac.tdesStreamInitContract AArch64.abi 640) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.tdesStreamInitSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesStreamInitPre AArch64.abi.ptrBits)
    (post := Spec.Cmac.tdesStreamInitPost AArch64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 640) init_verified (by decide) (by decide) initFrameSat_pre

theorem absorb_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 688 .x4 absorb)
      (Spec.Cmac.tdesAbsorbContract AArch64.abi 688) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.tdesAbsorbSig) (nm := "scratch") (e := .u64) (n := 86)
    (post := Spec.Cmac.tdesAbsorbPost AArch64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 688) absorb_verified (by decide) (by decide) absorbFrameSat_pre

theorem finish_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 640 .x3 finish)
      (Spec.Cmac.tdesFinishContract AArch64.abi 640) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.tdesFinishSig) (nm := "scratch") (e := .u64) (n := 80)
    (post := Spec.Cmac.tdesFinishPost AArch64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 640) finish_verified (by decide) (by decide) finishFrameSat_pre

end VG.Proof.CmacTripleDes.Stream.AArch64
