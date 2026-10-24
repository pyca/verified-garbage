module

public import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Verified
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Streaming AES-CMAC on PPC64LE, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame of 2336 bytes that allocates it
(`Verified.stackScratch`): the frame's 32-byte header and the 2304 bytes of
working space. Their code uses no other stack: a call (`bl`) keeps the
return address in the link register, which they save in the working space.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.Stream.PPC64LE

/-- A state satisfying `vg_cmac_aes_init`'s precondition, without the
working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 304⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.aesInitContract PPC64LE.abi 2336).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, PPC64LE.abi, PPC64LE.argRegs] [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, without the
working space (and with no data). -/
def absorbFrameSat : State := { absorbSat with wr := [⟨0x1000, 304⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.aesAbsorbContract PPC64LE.abi 2336).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, PPC64LE.abi, PPC64LE.argRegs] [absorbFrameSat, absorbSat]
    using absorbFrameSat

/-- A state satisfying `vg_cmac_aes_finish`'s precondition, without the
working space. -/
def finishFrameSat : State := { finishSat with wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.aesFinishContract PPC64LE.abi 2336).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, PPC64LE.abi, PPC64LE.argRegs] [finishFrameSat, finishSat]
    using finishFrameSat

theorem init_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2336 .r6 init)
      (Spec.Cmac.aesInitContract PPC64LE.abi 2336) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesInitPre PPC64LE.abi.ptrBits)
    (post := Spec.Cmac.aesInitPost PPC64LE.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 2336) init_verified (by decide) (by decide) (initPre_local _) (initPost_local _)
    initFrameSat_pre

theorem absorb_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2336 .r8 absorb)
      (Spec.Cmac.aesAbsorbContract PPC64LE.abi 2336) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesAbsorbPre PPC64LE.abi.ptrBits)
    (post := Spec.Cmac.aesAbsorbPost PPC64LE.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 2336) absorb_verified (by decide) (by decide) (absorbPre_local _) (absorbPost_local _)
    absorbFrameSat_pre

theorem finish_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2336 .r7 finish)
      (Spec.Cmac.aesFinishContract PPC64LE.abi 2336) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesFinishPre PPC64LE.abi.ptrBits)
    (post := Spec.Cmac.aesFinishPost PPC64LE.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 2336) finish_verified (by decide) (by decide) (finishPre_local _) (finishPost_local _)
    finishFrameSat_pre

end VG.Proof.CmacAes.Stream.PPC64LE
