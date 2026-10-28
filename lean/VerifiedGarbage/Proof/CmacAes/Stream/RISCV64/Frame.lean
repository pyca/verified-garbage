module

public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Verified
public import VerifiedGarbage.Impl.StackScratch.RISCV64
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Streaming AES-CMAC on RISC-V, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame of 2304 bytes that allocates it
(`Verified.stackScratchL`), all working space. Their code uses no other
stack: a call (`jal`) keeps the return address in `ra`, which they save in
the working space.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.RISCV64

open VG VG.RISCV64 VG.Impl.CmacAes.Stream.RISCV64

/-- A state satisfying `vg_cmac_aes_init`'s precondition, without the
working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 304⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.aesInitContract RISCV64.abi 2304).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, RISCV64.abi, RISCV64.argRegs] [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, without the
working space (and with no data). -/
def absorbFrameSat : State := { absorbSat with wr := [⟨0x1000, 304⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.aesAbsorbContract RISCV64.abi 2304).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, RISCV64.abi, RISCV64.argRegs] [absorbFrameSat, absorbSat]
    using absorbFrameSat

/-- A state satisfying `vg_cmac_aes_finish`'s precondition, without the
working space. -/
def finishFrameSat : State := { finishSat with wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.aesFinishContract RISCV64.abi 2304).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, RISCV64.abi, RISCV64.argRegs] [finishFrameSat, finishSat]
    using finishFrameSat

theorem init_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2304 .a3 init)
      (Spec.Cmac.aesInitContract RISCV64.abi 2304) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesInitPre RISCV64.abi.ptrBits)
    (post := Spec.Cmac.aesInitPost RISCV64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 2304) init_verified (by decide) (by decide) initFrameSat_pre

theorem absorb_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2304 .a5 absorb)
      (Spec.Cmac.aesAbsorbContract RISCV64.abi 2304) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesAbsorbPre RISCV64.abi.ptrBits)
    (post := Spec.Cmac.aesAbsorbPost RISCV64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 2304) absorb_verified (by decide) (by decide) absorbFrameSat_pre

theorem finish_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2304 .a4 finish)
      (Spec.Cmac.aesFinishContract RISCV64.abi 2304) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesFinishPre RISCV64.abi.ptrBits)
    (post := Spec.Cmac.aesFinishPost RISCV64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 2304) finish_verified (by decide) (by decide) finishFrameSat_pre

end VG.Proof.CmacAes.Stream.RISCV64
