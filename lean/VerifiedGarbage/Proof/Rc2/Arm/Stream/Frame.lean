import VerifiedGarbage.Proof.Rc2.Arm.Stream.Verified
import VerifiedGarbage.Proof.Rc2.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe

/-!
# RC2-CBC's streaming functions on ARMv7, with their working space on the stack

`init` and the updates run their code, proved with the working space as an
argument (`Verified.lean`), in a frame of 592 bytes that allocates it and
copies their two other stack arguments (`Verified.stackScratchWiped`), and
zero it before returning.
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm

/-- A state satisfying `vg_rc2_cbc_init`'s precondition, without the working
space. -/
def initFrameSat : State :=
  { initSatState with rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩, ⟨0x6000, 8⟩], wr := [⟨0x3000, 144⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Rc2.cbcInitContract Arm.abi 600).pre s := by
  implies_sat [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, Spec.Rc2.cbcInitPost, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, initSatState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using initFrameSat

theorem init_framed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.init)
      (Spec.Rc2.cbcInitContract Arm.abi 600) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Rc2.cbcInitSig) (nm := "scratch") (e := .u64)
    (n := 72) (post := Spec.Rc2.cbcInitPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 592) (m := 2) (words := 144) init_verified (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (cbcInitPost_local _) (cbcInitPostOut_local _) initFrameSat_pre

/-- A state satisfying the update functions' precondition, without the
working space. -/
def updateFrameSat : State :=
  { updateSatState with rd := [⟨0x2000, 0⟩, ⟨0x6000, 8⟩], wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩] }

theorem updateFrameSat_pre (d : Spec.Rc2.Direction) :
    ∃ s, (Spec.Rc2.cbcUpdateContract Arm.abi d 600).pre s := by
  implies_sat [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, Spec.Rc2.cbcUpdatePre,
    Spec.Rc2.cbcUpdatePost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr]
    [updateFrameSat, updateSatState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using updateFrameSat

theorem encryptUpdate_framed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.encryptUpdate)
      (Spec.Rc2.cbcEncryptUpdateContract Arm.abi 600) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64)
    (n := 72) (pre := Spec.Rc2.cbcUpdatePre Arm.abi.ptrBits)
    (post := Spec.Rc2.cbcUpdatePost .encrypt Arm.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 592) (m := 2) (words := 144) encryptUpdate_verified (by decide) (by decide)
    (by decide) (by decide) (by decide) (cbcUpdatePre_local _) (cbcUpdatePost_local _ _)
    (cbcUpdatePostOut_local _ _) (updateFrameSat_pre .encrypt)

theorem decryptUpdate_framed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.decryptUpdate)
      (Spec.Rc2.cbcDecryptUpdateContract Arm.abi 600) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64)
    (n := 72) (pre := Spec.Rc2.cbcUpdatePre Arm.abi.ptrBits)
    (post := Spec.Rc2.cbcUpdatePost .decrypt Arm.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 592) (m := 2) (words := 144) decryptUpdate_verified (by decide) (by decide)
    (by decide) (by decide) (by decide) (cbcUpdatePre_local _) (cbcUpdatePost_local _ _)
    (cbcUpdatePostOut_local _ _) (updateFrameSat_pre .decrypt)

end VG.Proof.Rc2.Arm.Stream
