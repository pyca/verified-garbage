module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Verified
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch

/-!
# Streaming TDEA-CMAC on PPC64LE, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackScratch`): the frame's 32-byte header and 640 bytes, 688 for
`absorb`. Their code uses no other stack: it and the functions it calls keep
the return address in the link register.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition,
without the working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 416⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesStreamInitContract PPC64LE.abi (0 + 672)).pre s := by
  implies_sat [Spec.Cmac.tdesStreamInitContract, Spec.Cmac.tdesStreamInitSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, PPC64LE.abi, PPC64LE.argRegs] [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition, without
the working space (and with no data). -/
def absorbFrameSat : State := { absorbSat with wr := [⟨0x1000, 416⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.tdesAbsorbContract PPC64LE.abi (0 + 720)).pre s := by
  implies_sat [Spec.Cmac.tdesAbsorbContract, Spec.Cmac.tdesAbsorbSig, Spec.Cmac.tdesAbsorbPost,
    PPC64LE.abi, PPC64LE.argRegs] [absorbFrameSat, absorbSat] using absorbFrameSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition, without
the working space. -/
def finishFrameSat : State := { finishSat with wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.tdesFinishContract PPC64LE.abi (0 + 672)).pre s := by
  implies_sat [Spec.Cmac.tdesFinishContract, Spec.Cmac.tdesFinishSig, Spec.Cmac.tdesFinishPost,
    PPC64LE.abi, PPC64LE.argRegs] [finishFrameSat, finishSat] using finishFrameSat

theorem init_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 672 .r6 streamInit)
      (Spec.Cmac.tdesStreamInitContract PPC64LE.abi 672) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Cmac.tdesStreamInitSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesStreamInitPre PPC64LE.abi.ptrBits)
    (post := Spec.Cmac.tdesStreamInitPost PPC64LE.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 672) init_verified (by decide) (by decide)
    (streamInitPre_local _) (streamInitPost_local _) initFrameSat_pre

theorem absorb_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 720 .r7 absorb)
      (Spec.Cmac.tdesAbsorbContract PPC64LE.abi 720) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Cmac.tdesAbsorbSig) (nm := "scratch") (e := .u64) (n := 86)
    (post := Spec.Cmac.tdesAbsorbPost PPC64LE.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 720) absorb_verified (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (absorbPost_local _) absorbFrameSat_pre

theorem finish_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 672 .r6 finish)
      (Spec.Cmac.tdesFinishContract PPC64LE.abi 672) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Cmac.tdesFinishSig) (nm := "scratch") (e := .u64) (n := 80)
    (post := Spec.Cmac.tdesFinishPost PPC64LE.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 672) finish_verified (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (finishPost_local _) finishFrameSat_pre

end VG.Proof.CmacTripleDes.Stream.PPC64LE
