import VerifiedGarbage.Proof.AesGcm.Arm.Verified
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
import VerifiedGarbage.Proof.Framework.Arm.RegScratch
import VerifiedGarbage.Proof.Framework.Arm.TagScratch

/-!
# AES-GCM's key setup and streaming functions on ARMv7, with their working space on the stack

`init`, `stream_init`, `stream_aad`, `stream_encrypt` and `stream_decrypt` run
their code, proved with the working space as an argument (`Verified.lean`),
in a frame that allocates it.
`init`'s working space is its fourth argument, in `r3`: its frame is the 2560
bytes of working space (`Verified.regScratch`). That of `stream_init` and
`stream_aad` is passed on the stack: their frames of 2576 bytes hold the
copies of the other arguments passed on the stack (none for `stream_init`,
`data` and `len` for `stream_aad`), the buffer's address and the saved `lr`
too (`Verified.stackScratch`); so do the frames of 2592 bytes of
`stream_encrypt` and `stream_decrypt`, with copies of their six words of
stack arguments (`aad_len`, `text_len`, `data` and `len`). The copies are
read only where the pre- and postconditions read the buffers
(`Proof/AesGcm/Scratch.lean`).

`stream_finish`, `stream_verify`, `seal` and `open` run their code, proved
for working space that carries the tag in its first 16 bytes
(`Proof/AesGcm/Tag.lean`), in a frame of 2592 bytes that holds the copies of
their stack arguments (with the working space's address in place of the
tag pointer, their fifth word on the stack), the saved `lr` and the working
space, and copies the tag in and out (`Verified.tagScratch`).
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

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition, with a
16-byte tag at 0. -/
def finFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 20⟩] [⟨0x3000, 80⟩, ⟨0, 16⟩]

theorem finFrameSat_pre : ∃ s, (Spec.Gcm.streamFinishContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre,
    Spec.Gcm.streamFinishPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using finFrameSat

theorem streamFinish_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withTagScratch 2592 5 4 32 streamFinish)
      (Spec.Gcm.streamFinishContract Arm.abi 2600) :=
  Arm.Verified.tagScratch (sig := Spec.Gcm.streamFinishSig) (q := 5) (nm := "work") (e := .u64)
    (n := 320) (wa := true) (stack := 8) streamFinish_verified
    (Proof.AesGcm.streamFinish_tagFrame _) rfl (by decide) (by decide) (by decide) finFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition, with a
16-byte tag at 0. -/
def verFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 24⟩] [⟨0x3000, 80⟩, ⟨0, 16⟩]

theorem verFrameSat_pre : ∃ s, (Spec.Gcm.streamVerifyContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Gcm.streamVerifyContract, Spec.Gcm.streamVerifySig, Spec.Gcm.streamVerifyPre,
    Spec.Gcm.streamVerifyPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [verFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using verFrameSat

theorem streamVerify_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withTagScratch 2592 6 4 32 streamVerify)
      (Spec.Gcm.streamVerifyContract Arm.abi 2600) :=
  Arm.Verified.tagScratch (sig := Spec.Gcm.streamVerifySig) (q := 5) (nm := "work") (e := .u64)
    (n := 320) (wa := true) (stack := 8) streamVerify_verified
    (Proof.AesGcm.streamVerify_tagFrame _) rfl (by decide) (by decide) (by decide) verFrameSat_pre

/-- A state satisfying `vg_aes_gcm_seal`'s precondition (with no nonce,
additional data or data), with a 16-byte tag at 0. -/
def sealFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 20⟩] [⟨0, 0⟩, ⟨0, 16⟩]

theorem sealFrameSat_pre : ∃ s, (Spec.Gcm.sealContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, Spec.Gcm.sealPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [sealFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sealFrameSat

theorem seal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withTagScratch 2592 5 4 32 «seal»)
      (Spec.Gcm.sealContract Arm.abi 2600) :=
  Arm.Verified.tagScratch (sig := Spec.Gcm.sealSig) (q := 5) (nm := "work") (e := .u64)
    (n := 320) (wa := true) (stack := 8) seal_verified
    (Proof.AesGcm.seal_tagFrame _) rfl (by decide) (by decide) (by decide) sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_open`'s precondition (with no nonce,
additional data or data), with a 16-byte tag at 0. -/
def openFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩] [⟨0, 0⟩, ⟨0, 16⟩]

theorem openFrameSat_pre : ∃ s, (Spec.Gcm.openContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Gcm.openContract, Spec.Gcm.openSig, Spec.Gcm.openPre, Spec.Gcm.openPost,
    Spec.Gcm.openLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using openFrameSat

theorem open_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withTagScratch 2592 6 4 32 «open»)
      (Spec.Gcm.openContract Arm.abi 2600) :=
  Arm.Verified.tagScratch (sig := Spec.Gcm.openSig) (q := 5) (nm := "work") (e := .u64)
    (n := 320) (wa := true) (stack := 8) open_verified
    (Proof.AesGcm.open_tagFrame _) rfl (by decide) (by decide) (by decide) openFrameSat_pre

end VG.Proof.AesGcm.Arm
