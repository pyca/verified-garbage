import VerifiedGarbage.Proof.CmacTripleDes.Arm.Verified
import VerifiedGarbage.Proof.CmacTripleDes.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
import VerifiedGarbage.Proof.Framework.Arm.RegScratch

/-!
# TDEA-CMAC on ARMv7, with its working space on the stack

The functions run their code, proved with the working space as an argument
(`Verified.lean`), in a frame that allocates it. Their other arguments are
all in registers. `init`'s working space is its fourth argument, in `r3`: its
frame is the 640 bytes of working space (`Verified.regScratch`). That of
`update` and `finalize` is their fifth, on the stack: their frames hold the
saved registers too, 648 bytes (`Verified.stackScratch`).
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Arm

/-- A state satisfying `vg_cmac_triple_des_init`'s precondition, without the
working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 400⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesInitContract Arm.abi 640).pre s := by
  implies_sat [Spec.Cmac.tdesInitContract, Spec.Cmac.tdesInitSig, Spec.Cmac.tdesInitPre,
    Spec.Cmac.tdesInitPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_triple_des_update`'s precondition, without
the working space (and with no blocks). -/
def updFrameSat : State :=
  { updSat with rd := [⟨0x1000, 384⟩, ⟨0x3000, 0⟩], wr := [⟨0x2000, 8⟩] }

theorem updFrameSat_pre : ∃ s, (Spec.Cmac.tdesUpdateContract Arm.abi 648).pre s := by
  implies_sat [Spec.Cmac.tdesUpdateContract, Spec.Cmac.tdesUpdateSig, Spec.Cmac.tdesUpdatePost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [updFrameSat, updSat] using updFrameSat

/-- A state satisfying `vg_cmac_triple_des_finalize`'s precondition, without
the working space (and with no last bytes). -/
def finFrameSat : State :=
  { finSat with rd := [⟨0x1000, 400⟩, ⟨0x3000, 0⟩], wr := [⟨0x2000, 8⟩] }

theorem finFrameSat_pre : ∃ s, (Spec.Cmac.tdesFinalizeContract Arm.abi 648).pre s := by
  implies_sat [Spec.Cmac.tdesFinalizeContract, Spec.Cmac.tdesFinalizeSig, Spec.Cmac.tdesFinalizePre,
    Spec.Cmac.tdesFinalizePost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [finFrameSat, finSat] using finFrameSat

theorem init_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 640 .r3 init)
    (Spec.Cmac.tdesInitContract Arm.abi 640) :=
  Arm.Verified.regScratch (sig := Spec.Cmac.tdesInitSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesInitPre Arm.abi.ptrBits) (post := Spec.Cmac.tdesInitPost Arm.abi.ptrBits)
    (wa := false) (stack := 0) init_verified (by decide) (by decide) (by decide) initFrameSat_pre

theorem update_framed : Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 648 0 update)
    (Spec.Cmac.tdesUpdateContract Arm.abi 648) :=
  Arm.Verified.stackScratch (sig := Spec.Cmac.tdesUpdateSig) (nm := "scratch") (e := .u64) (n := 80)
    (post := Spec.Cmac.tdesUpdatePost Arm.abi.ptrBits)
    (wa := false) (stack := 0) (m := 0) update_verified (by decide) (by decide) (by decide)
    (by decide) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (updatePost_local _)
    updFrameSat_pre

theorem finalize_framed : Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 648 0 finalize)
    (Spec.Cmac.tdesFinalizeContract Arm.abi 648) :=
  Arm.Verified.stackScratch (sig := Spec.Cmac.tdesFinalizeSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesFinalizePre Arm.abi.ptrBits)
    (post := Spec.Cmac.tdesFinalizePost Arm.abi.ptrBits)
    (wa := false) (stack := 0) (m := 0) finalize_verified (by decide) (by decide) (by decide)
    (by decide) (finalizePre_local _) (finalizePost_local _) finFrameSat_pre

end VG.Proof.CmacTripleDes.Arm
