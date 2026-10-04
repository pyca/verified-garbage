import VerifiedGarbage.Proof.Rc2.AArch64.Stream.Verified
import VerifiedGarbage.Proof.Rc2.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe

/-!
# RC2-CBC's streaming functions on AArch64, with their working space on the stack

`init` and the updates run their code, proved with the working space as an
argument (`Verified.lean`), in a frame of 576 bytes that allocates it
(`Verified.stackScratchWiped`), and zero it before returning.
-/

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64 VG.Impl.Rc2.AArch64.Stream

/-- A state satisfying `vg_rc2_cbc_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x3000, 144⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Rc2.cbcInitContract AArch64.abi 592).pre s := by
  implies_sat [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, Spec.Rc2.cbcInitPost, AArch64.abi,
    AArch64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 576 .x6 72 init)
      (Spec.Rc2.cbcInitContract AArch64.abi 592) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcInitSig) (nm := "scratch") (e := .u64)
    (n := 72) (post := Spec.Rc2.cbcInitPost AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 576) (words := 72) init_verified (by decide) (by decide) (by decide)
    (cbcInitPostOut_local _) initFrameSat_pre

/-- A state satisfying the update functions' precondition, without the
working space. -/
def updateFrameSat : State := { updateSat with wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩] }

theorem updateFrameSat_pre (d : Spec.Rc2.Direction) :
    ∃ s, (Spec.Rc2.cbcUpdateContract AArch64.abi d 592).pre s := by
  implies_sat [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, Spec.Rc2.cbcUpdatePre,
    Spec.Rc2.cbcUpdatePost, AArch64.abi, AArch64.argRegs] [updateFrameSat, updateSat]
    using updateFrameSat

theorem encryptUpdate_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 576 .x6 72 encryptUpdate)
      (Spec.Rc2.cbcEncryptUpdateContract AArch64.abi 592) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64)
    (n := 72) (pre := Spec.Rc2.cbcUpdatePre AArch64.abi.ptrBits)
    (post := Spec.Rc2.cbcUpdatePost .encrypt AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 576) (words := 72) encryptUpdate_verified (by decide) (by decide) (by decide)
    (cbcUpdatePostOut_local _ _) (updateFrameSat_pre .encrypt)

theorem decryptUpdate_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 576 .x6 72 decryptUpdate)
      (Spec.Rc2.cbcDecryptUpdateContract AArch64.abi 592) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64)
    (n := 72) (pre := Spec.Rc2.cbcUpdatePre AArch64.abi.ptrBits)
    (post := Spec.Rc2.cbcUpdatePost .decrypt AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 576) (words := 72) decryptUpdate_verified (by decide) (by decide) (by decide)
    (cbcUpdatePostOut_local _ _) (updateFrameSat_pre .decrypt)

end VG.Proof.Rc2.AArch64.Stream
