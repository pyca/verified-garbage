import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Verified
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
import VerifiedGarbage.Proof.Framework.Arm.RegScratch

/-!
# Streaming AES-CMAC on ARMv7, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame that allocates it. `init`'s working
space is its fourth argument, in `r3`: its frame is the 2304 bytes of
working space (`Verified.regScratch`). That of `absorb` and `finish` follows
their arguments on the stack (`data` and `len`, `out`): their frames copy
those and hold the saved registers too, 2320 bytes (`Verified.stackScratch`).
The copies are read only where the pre- and postconditions read the buffers
(`Proof/CmacAes/Stream/Scratch.lean`).
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm

/-- A state satisfying `vg_cmac_aes_init`'s precondition, without the
working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 304⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.aesInitContract Arm.abi 2312).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, without the
working space: as `absorbSat`. -/
def absorbFrameSat : State :=
  { absorbSat with rd := [⟨0x3000, 0⟩, ⟨0x8000, 8⟩], wr := [⟨0x1000, 304⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.aesAbsorbContract Arm.abi 2336).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [absorbFrameSat, absorbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using absorbFrameSat

/-- A state satisfying `vg_cmac_aes_finish`'s precondition, without the
working space: as `finishSat`. -/
def finishFrameSat : State :=
  { finishSat with rd := [⟨0x8000, 4⟩], wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.aesFinishContract Arm.abi 2336).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [finishFrameSat, finishSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finishFrameSat

theorem init_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 2304 .r3 init)
    (Spec.Cmac.aesInitContract Arm.abi 2312) :=
  Arm.Verified.regScratch (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64) (n := 288)
    (pre := Spec.Cmac.aesInitPre Arm.abi.ptrBits) (post := Spec.Cmac.aesInitPost Arm.abi.ptrBits)
    (wa := false) (stack := 8) init_verified (by decide) (by decide) (by decide) initFrameSat_pre

theorem absorb_framed : Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2320 2 absorb)
    (Spec.Cmac.aesAbsorbContract Arm.abi 2336) :=
  Arm.Verified.stackScratch (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64) (n := 288)
    (pre := Spec.Cmac.aesAbsorbPre Arm.abi.ptrBits) (post := Spec.Cmac.aesAbsorbPost Arm.abi.ptrBits)
    (wa := false) (stack := 16) (m := 2) absorb_verified (by decide) (by decide) (by decide)
    (by decide) (absorbPre_local _) (absorbPost_local _) absorbFrameSat_pre

theorem finish_framed : Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2320 1 finish)
    (Spec.Cmac.aesFinishContract Arm.abi 2336) :=
  Arm.Verified.stackScratch (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64) (n := 288)
    (pre := Spec.Cmac.aesFinishPre Arm.abi.ptrBits) (post := Spec.Cmac.aesFinishPost Arm.abi.ptrBits)
    (wa := false) (stack := 16) (m := 1) finish_verified (by decide) (by decide) (by decide)
    (by decide) (finishPre_local _) (finishPost_local _) finishFrameSat_pre

end VG.Proof.CmacAes.Stream.Arm
