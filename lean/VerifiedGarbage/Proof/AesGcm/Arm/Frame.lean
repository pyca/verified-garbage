import VerifiedGarbage.Proof.AesGcm.Arm.Verified
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
import VerifiedGarbage.Proof.Framework.Arm.RegScratch

/-!
# AES-GCM's key setup and streaming start on ARMv7, with their working space on the stack

`init`, `stream_init` and `stream_aad` run their code, proved with the
working space as an argument (`Verified.lean`), in a frame that allocates it.
`init`'s working space is its fourth argument, in `r3`: its frame is the 2560
bytes of working space (`Verified.regScratch`). That of `stream_init` and
`stream_aad` is passed on the stack: their frames of 2576 bytes hold the
copies of the other arguments passed on the stack (none for `stream_init`,
`data` and `len` for `stream_aad`), the buffer's address and the saved `lr`
too (`Verified.stackScratch`). The copies are read only where the
postconditions read the buffers (`Proof/AesGcm/Scratch.lean`).
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm

/-- A state satisfying `vg_aes_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 16 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 16⟩] [⟨0x2000, 256⟩]

theorem initFrameSat_pre : ∃ s, (Spec.Gcm.initContract Arm.abi 2568).pre s := by
  implies_sat [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, mkSat] using initFrameSat

theorem init_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 2560 .r3 init)
    (Spec.Gcm.initContract Arm.abi 2568) :=
  Arm.Verified.regScratch (sig := Spec.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre Arm.abi.ptrBits) (post := Spec.Gcm.initPost Arm.abi.ptrBits)
    (wa := true) (stack := 8) init_verified (by decide) (by decide) (by decide) initFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩] [⟨0x3000, 80⟩]

theorem streamInitFrameSat_pre : ∃ s, (Spec.Gcm.streamInitContract Arm.abi 2584).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [streamInitFrameSat, mkSat] using streamInitFrameSat

theorem streamInit_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2576 0 streamInit)
      (Spec.Gcm.streamInitContract Arm.abi 2584) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamInitPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 0) streamInit_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (streamInitPost_local _)
    streamInitFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0x8000, 8⟩] [⟨0x3000, 80⟩]

theorem streamAadFrameSat_pre : ∃ s, (Spec.Gcm.streamAadContract Arm.abi 2584).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [streamAadFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using streamAadFrameSat

theorem streamAad_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2576 2 streamAad)
      (Spec.Gcm.streamAadContract Arm.abi 2584) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamAadPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 2) streamAad_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (streamAadPost_local _)
    streamAadFrameSat_pre

end VG.Proof.AesGcm.Arm
