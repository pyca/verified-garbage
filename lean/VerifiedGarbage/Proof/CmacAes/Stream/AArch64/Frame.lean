import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Verified
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

/-!
# Streaming AES-CMAC on AArch64, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame of 2304 bytes that allocates it
(`Verified.stackScratch`). Their code uses no other stack: their calls keep
the return address in `x30`, which they save in the working space.
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.Stream.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- A state satisfying `vg_cmac_aes_init`'s precondition, without the
working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 304⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.aesInitContract AArch64.abi 2304).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, AArch64.abi, AArch64.argRegs] [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, without the
working space (and with no data). -/
def absorbFrameSat : State := { absorbSat with wr := [⟨0x1000, 304⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.aesAbsorbContract AArch64.abi 2304).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, AArch64.abi, AArch64.argRegs] [absorbFrameSat, absorbSat]
    using absorbFrameSat

/-- A state satisfying `vg_cmac_aes_finish`'s precondition, without the
working space. -/
def finishFrameSat : State := { finishSat with wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.aesFinishContract AArch64.abi 2304).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, AArch64.abi, AArch64.argRegs] [finishFrameSat, finishSat]
    using finishFrameSat

theorem init_framed (v : Ctr32Impl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2304 .x3 (init v.expand v.callee v.suffix))
      (Spec.Cmac.aesInitContract AArch64.abi 2304) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesInitPre AArch64.abi.ptrBits)
    (post := Spec.Cmac.aesInitPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 2304) (init_verified v) (by decide) (by decide) initFrameSat_pre

theorem absorb_framed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2304 .x5 (absorb v.callee))
      (Spec.Cmac.aesAbsorbContract AArch64.abi 2304) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesAbsorbPre AArch64.abi.ptrBits)
    (post := Spec.Cmac.aesAbsorbPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 2304) (absorb_verified v) (by decide) (by decide) absorbFrameSat_pre

theorem finish_framed (v : Ctr32Impl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2304 .x4 (finish v.callee v.suffix))
      (Spec.Cmac.aesFinishContract AArch64.abi 2304) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesFinishPre AArch64.abi.ptrBits)
    (post := Spec.Cmac.aesFinishPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 2304) (finish_verified v) (by decide) (by decide) finishFrameSat_pre

end VG.Proof.CmacAes.Stream.AArch64
