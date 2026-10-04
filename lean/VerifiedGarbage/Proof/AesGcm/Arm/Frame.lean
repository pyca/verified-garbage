import VerifiedGarbage.Proof.AesGcm.Arm.Verified
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
import VerifiedGarbage.Proof.Framework.Arm.RegScratch

/-!
# AES-GCM on ARMv7, with its working space on the stack

Each function runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame that allocates it.
`init`'s working space is its fourth argument, in `r3`: its frame is the 2560
bytes of working space (`Verified.regScratch`). That of `stream_init` and
`stream_aad` is passed on the stack: their frames of 2576 bytes hold the
copies of the other arguments passed on the stack (none for `stream_init`,
`data` and `len` for `stream_aad`), the buffer's address and the saved `lr`
too (`Verified.stackScratch`); so do the frames of 2592 bytes of
`stream_encrypt` and `stream_decrypt`, with copies of their six words of
stack arguments (`aad_len`, `text_len`, `data` and `len`), and those of
`stream_finish` and `seal` (five words) and of `stream_verify` and `open`
(six). The copies are read only where the pre- and postconditions read the
buffers (`Proof/AesGcm/Scratch.lean`).
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

/-- A state satisfying the preconditions of `vg_aes_gcm_stream_encrypt` and
`vg_aes_gcm_stream_decrypt`, without the working space: their six words of
stack arguments at `0x8000`. -/
def crFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 24⟩] [⟨0x3000, 80⟩, ⟨0, 0⟩]

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Gcm.streamEncryptContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Gcm.streamEncryptContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Spec.Gcm.streamEncryptPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [crFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using crFrameSat

theorem streamEncrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 streamEncrypt)
      (Spec.Gcm.streamEncryptContract Arm.abi 2600) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre Arm.abi.ptrBits)
    (post := Spec.Gcm.streamEncryptPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 6) streamEncrypt_verified (by decide) (by decide) (by decide) (by decide)
    (streamTextPre_local _) (streamEncryptPost_local _) streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Gcm.streamDecryptContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Gcm.streamDecryptContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Spec.Gcm.streamDecryptPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [crFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using crFrameSat

theorem streamDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 streamDecrypt)
      (Spec.Gcm.streamDecryptContract Arm.abi 2600) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre Arm.abi.ptrBits)
    (post := Spec.Gcm.streamDecryptPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 6) streamDecrypt_verified (by decide) (by decide) (by decide) (by decide)
    (streamTextPre_local _) (streamDecryptPost_local _) streamDecryptFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition, without the
working space: its five words of stack arguments at `0x8000`. -/
def finFrameSat : State :=
  mkSat4 (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 20⟩] [⟨0x3000, 80⟩, ⟨0x4000, 16⟩]

theorem finFrameSat_pre : ∃ s, (Spec.Gcm.streamFinishContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre, Spec.Gcm.streamFinishPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, mkSat4, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat

theorem streamFinish_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 5 streamFinish)
      (Spec.Gcm.streamFinishContract Arm.abi 2600) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamFinishPre Arm.abi.ptrBits)
    (post := Spec.Gcm.streamFinishPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 5) streamFinish_verified (by decide) (by decide) (by decide) (by decide)
    (streamFinishPre_local _) (streamFinishPost_local _) finFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition, without the
working space: its six words of stack arguments at `0x8000`. -/
def verFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩] [⟨0x3000, 80⟩]

theorem verFrameSat_pre : ∃ s, (Spec.Gcm.streamVerifyContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Gcm.streamVerifyContract, Spec.Gcm.streamVerifySig, Spec.Gcm.streamVerifyPre, Spec.Gcm.streamVerifyPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [verFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using verFrameSat

theorem streamVerify_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 streamVerify)
      (Spec.Gcm.streamVerifyContract Arm.abi 2600) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamVerifyPre Arm.abi.ptrBits)
    (post := Spec.Gcm.streamVerifyPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 6) streamVerify_verified (by decide) (by decide) (by decide) (by decide)
    (streamVerifyPre_local _) (streamVerifyPost_local _) verFrameSat_pre

/-- A state satisfying `vg_aes_gcm_seal`'s precondition, without the working
space: its five words of stack arguments at `0x8000`. -/
def sealFrameSat : State :=
  mkSat4 (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 20⟩] [⟨0, 0⟩, ⟨0x4000, 16⟩]

theorem sealFrameSat_pre : ∃ s, (Spec.Gcm.sealContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, Spec.Gcm.sealPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [sealFrameSat, mkSat4, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 5 «seal»)
      (Spec.Gcm.sealContract Arm.abi 2600) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.sealPre Arm.abi.ptrBits)
    (post := Spec.Gcm.sealPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 5) seal_verified (by decide) (by decide) (by decide) (by decide)
    (sealPre_local _) (sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_open`'s precondition, without the working
space: its six words of stack arguments at `0x8000`. -/
def openFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩] [⟨0, 0⟩]

theorem openFrameSat_pre : ∃ s, (Spec.Gcm.openContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Gcm.openContract, Spec.Gcm.openSig, Spec.Gcm.openPre, Spec.Gcm.openPost, Spec.Gcm.openLeak,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using openFrameSat

theorem open_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 «open»)
      (Spec.Gcm.openContract Arm.abi 2600) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openPre Arm.abi.ptrBits)
    (post := Spec.Gcm.openPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.Gcm.openLeak Arm.abi.ptrBits))
    (m := 6) open_verified (by decide) (by decide) (by decide) (by decide)
    (openPre_local _) (openPost_local _) openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.AesGcm.Arm
