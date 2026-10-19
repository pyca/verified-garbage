module
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.Conv
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.Arm
public import VerifiedGarbage.Proof.CmacTripleDes.Arm.RoundLit
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Implies
public import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Impl.StackScratch.Arm

import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Verified
import VerifiedGarbage.Proof.Framework.Arm.RegScratch

/-!
# Streaming TDEA-CMAC on ARMv7, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame that allocates it. `stream_init`'s
working space is its fourth argument, in `r3`: its frame is the 640 bytes
of working space (`Verified.regScratch`). That of `absorb` and `finish` is
their last, on the stack: their frames hold the copies of their stack
arguments and `lr` too (`Verified.stackScratch`), 704 bytes for `absorb`
(688 of working space) and 656 for `finish`, below which their code pushes
the working space's address. The copies are read only where the pre- and
postconditions read the buffers (`Proof/CmacTripleDes/StreamScratch.lean`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Stream.Arm

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition,
without the working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 416⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesStreamInitContract Arm.abi 640).pre s := by
  implies_sat [Spec.Cmac.tdesStreamInitContract, Spec.Cmac.tdesStreamInitSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition, without
the working space: as `absorbSat`. -/
def absorbFrameSat : State :=
  { absorbSat with rd := [⟨0x3000, 0⟩, ⟨0x8000, 8⟩], wr := [⟨0x1000, 416⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.tdesAbsorbContract Arm.abi 708).pre s := by
  implies_sat [Spec.Cmac.tdesAbsorbContract, Spec.Cmac.tdesAbsorbSig, Spec.Cmac.tdesAbsorbPost, countArm,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [absorbFrameSat, absorbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using absorbFrameSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition, without
the working space: as `finishSat`. -/
def finishFrameSat : State :=
  { finishSat with rd := [⟨0x8000, 4⟩], wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.tdesFinishContract Arm.abi 660).pre s := by
  implies_sat [Spec.Cmac.tdesFinishContract, Spec.Cmac.tdesFinishSig, Spec.Cmac.tdesFinishPost, countArm,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finishFrameSat, finishSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using finishFrameSat

theorem init_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 640 .r3 streamInit)
    (Spec.Cmac.tdesStreamInitContract Arm.abi 640) :=
  Arm.Verified.regScratch (sig := Spec.Cmac.tdesStreamInitSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesStreamInitPre Arm.abi.ptrBits) (post := Spec.Cmac.tdesStreamInitPost Arm.abi.ptrBits)
    (wa := false) (stack := 0) init_verified (by decide) (by decide) (by decide) initFrameSat_pre

theorem absorb_framed : Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 704 2 absorb)
    (Spec.Cmac.tdesAbsorbContract Arm.abi 708) :=
  Arm.Verified.stackScratch (sig := Spec.Cmac.tdesAbsorbSig) (nm := "scratch") (e := .u64) (n := 86)
    (post := Spec.Cmac.tdesAbsorbPost Arm.abi.ptrBits)
    (wa := false) (stack := 4) (m := 2) absorb_verified (by decide) (by decide) (by decide)
    (by decide) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (absorbPost_local _)
    absorbFrameSat_pre

theorem finish_framed : Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 656 1 finish)
    (Spec.Cmac.tdesFinishContract Arm.abi 660) :=
  Arm.Verified.stackScratch (sig := Spec.Cmac.tdesFinishSig) (nm := "scratch") (e := .u64) (n := 80)
    (post := Spec.Cmac.tdesFinishPost Arm.abi.ptrBits)
    (wa := false) (stack := 4) (m := 1) finish_verified (by decide) (by decide) (by decide)
    (by decide) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (finishPost_local _)
    finishFrameSat_pre

end VG.Proof.CmacTripleDes.Stream.Arm
