module

public import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Verified
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Verified
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Streaming RC2-CBC on RISC-V, with its working space on the stack

`init` and the updates run their code, proved with the working space as an
argument (`Verified.lean`), in a frame of 608 bytes that allocates it
(`Verified.stackScratchWiped`), and zero its 576 bytes before returning.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Stream

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64.Stream

/-- A state satisfying `vg_rc2_cbc_init`'s precondition, without the working
space. -/
noncomputable def initFrameSat : State := { initSat with wr := [⟨0x3000, 144⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Rc2.cbcInitContract RISCV64.abi 608).pre s := by
  implies_sat [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, Spec.Rc2.cbcInitPost, RISCV64.abi,
    RISCV64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchWiped 608 .a6 72 init)
      (Spec.Rc2.cbcInitContract RISCV64.abi 608) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcInitSig) (nm := "scratch") (e := .u64) (n := 72)
    (post := Spec.Rc2.cbcInitPost RISCV64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 608) (words := 72)
    init_verified (by decide) (by decide) (by decide) (Proof.Rc2.cbcInitPostOut_local _) initFrameSat_pre

/-- A state satisfying the update functions' precondition, without the
working space. -/
noncomputable def updateFrameSat : State := { updateSat with wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩] }

theorem updateFrameSat_pre (d : Spec.Rc2.Direction) :
    ∃ s, (Spec.Rc2.cbcUpdateContract RISCV64.abi d 608).pre s := by
  implies_sat [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, Spec.Rc2.cbcUpdatePre,
    Spec.Rc2.cbcUpdatePost, RISCV64.abi, RISCV64.argRegs] [updateFrameSat, updateSat] using updateFrameSat

theorem encryptUpdate_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchWiped 608 .a6 72 encryptUpdate)
      (Spec.Rc2.cbcEncryptUpdateContract RISCV64.abi 608) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64) (n := 72)
    (pre := Spec.Rc2.cbcUpdatePre RISCV64.abi.ptrBits)
    (post := Spec.Rc2.cbcUpdatePost .encrypt RISCV64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 608)
    (words := 72) encryptUpdate_verified (by decide) (by decide) (by decide)
    (Proof.Rc2.cbcUpdatePostOut_local _ _) (updateFrameSat_pre .encrypt)

theorem decryptUpdate_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchWiped 608 .a6 72 decryptUpdate)
      (Spec.Rc2.cbcDecryptUpdateContract RISCV64.abi 608) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64) (n := 72)
    (pre := Spec.Rc2.cbcUpdatePre RISCV64.abi.ptrBits)
    (post := Spec.Rc2.cbcUpdatePost .decrypt RISCV64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 608)
    (words := 72) decryptUpdate_verified (by decide) (by decide) (by decide)
    (Proof.Rc2.cbcUpdatePostOut_local _ _) (updateFrameSat_pre .decrypt)

end VG.Proof.Rc2.RISCV64.Stream
