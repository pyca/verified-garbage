module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Verified
public import VerifiedGarbage.Impl.StackScratch.RISCV64
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Streaming TDEA-CMAC on RISC-V, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument and the 944 bytes of stack below it that ECB uses (`Verified.lean`),
in a frame that allocates the working space (`Verified.stackScratchL`): 640
bytes for `stream_init` and `finish`, 688 for `absorb`, so 1584 and 1632
bytes of stack in all.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.Impl.CmacTripleDes.Stream.RISCV64

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition,
without the working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 416⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesStreamInitContract RISCV64.abi 1584).pre s := by
  implies_sat [Spec.Cmac.tdesStreamInitContract, Spec.Cmac.tdesStreamInitSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, RISCV64.abi, RISCV64.argRegs] [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition, without
the working space (and with no data). -/
def absorbFrameSat : State := { absorbSat with wr := [⟨0x1000, 416⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.tdesAbsorbContract RISCV64.abi 1632).pre s := by
  implies_sat [Spec.Cmac.tdesAbsorbContract, Spec.Cmac.tdesAbsorbSig, Spec.Cmac.tdesAbsorbPost,
    RISCV64.abi, RISCV64.argRegs] [absorbFrameSat, absorbSat] using absorbFrameSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition, without
the working space. -/
def finishFrameSat : State := { finishSat with wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.tdesFinishContract RISCV64.abi 1584).pre s := by
  implies_sat [Spec.Cmac.tdesFinishContract, Spec.Cmac.tdesFinishSig, Spec.Cmac.tdesFinishPost,
    RISCV64.abi, RISCV64.argRegs] [finishFrameSat, finishSat] using finishFrameSat

theorem init_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 640 .a3 streamInit)
      (Spec.Cmac.tdesStreamInitContract RISCV64.abi 1584) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Cmac.tdesStreamInitSig) (nm := "scratch") (e := .u64)
    (n := 80) (pre := Spec.Cmac.tdesStreamInitPre RISCV64.abi.ptrBits)
    (post := Spec.Cmac.tdesStreamInitPost RISCV64.abi.ptrBits) (wa := false) (stack := 944)
    (bytes := 640) init_verified (by decide) (by decide) initFrameSat_pre

theorem absorb_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 688 .a4 absorb)
      (Spec.Cmac.tdesAbsorbContract RISCV64.abi 1632) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Cmac.tdesAbsorbSig) (nm := "scratch") (e := .u64)
    (n := 86) (post := Spec.Cmac.tdesAbsorbPost RISCV64.abi.ptrBits) (wa := false) (stack := 944)
    (bytes := 688) absorb_verified (by decide) (by decide) absorbFrameSat_pre

theorem finish_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 640 .a3 finish)
      (Spec.Cmac.tdesFinishContract RISCV64.abi 1584) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Cmac.tdesFinishSig) (nm := "scratch") (e := .u64)
    (n := 80) (post := Spec.Cmac.tdesFinishPost RISCV64.abi.ptrBits) (wa := false) (stack := 944)
    (bytes := 640) finish_verified (by decide) (by decide) finishFrameSat_pre

end VG.Proof.CmacTripleDes.Stream.RISCV64
