module

public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Verified
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.Framework.Arm.RegScratch

/-!
# SM4-GCM on ARMv7, with its working space on the stack

Each function runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame that allocates it.
`init`'s working space is its third argument, in `r2`: its frame is the 768
bytes of working space (`Verified.regScratch`). That of the others is passed
on the stack: the frames of 784 bytes of `stream_init` and `stream_aad` hold
the copies of the other arguments passed on the stack (none for
`stream_init`, `data` and `len` for `stream_aad`), the buffer's address and
the saved `lr` too (`Verified.stackScratch`); so do the frames of 800 bytes
of `stream_encrypt` and `stream_decrypt`, with copies of their four words of
stack arguments (`text_len`, `data` and `len`), of `stream_finish` (three:
`text_len` and `tag`), of `stream_verify` and `seal` (four) and of `open`
(five). The copies are read only where the postconditions read the buffers
(`Proof/Sm4Gcm/Scratch.lean`). Each frame sits on the 1520 bytes of stack the
code needs below it.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Impl.Sm4Gcm.Arm

/-- A state satisfying `vg_sm4_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0)
    [⟨0x1000, 16⟩] [⟨0x2000, 144⟩]

theorem initFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.initContract Arm.abi 2288).pre s := by
  implies_sat [Spec.Sm4.Gcm.initContract, Spec.Sm4.Gcm.initSig, Spec.Sm4.Gcm.initPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, mkSat] using initFrameSat

theorem init_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 768 .r2 init)
    (Spec.Sm4.Gcm.initContract Arm.abi 2288) :=
  Arm.Verified.regScratch (sig := Spec.Sm4.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 96)
    (post := Spec.Sm4.Gcm.initPost Arm.abi.ptrBits)
    (wa := true) (stack := 1520) init_verified (by decide) (by decide) (by decide) initFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 144⟩, ⟨0x2000, 0⟩] [⟨0x3000, 80⟩]

theorem streamInitFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamInitContract Arm.abi 2304).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamInitContract, Spec.Sm4.Gcm.streamInitSig, Spec.Sm4.Gcm.streamInitPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [streamInitFrameSat, mkSat] using streamInitFrameSat

theorem streamInit_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 784 0 streamInit)
      (Spec.Sm4.Gcm.streamInitContract Arm.abi 2304) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.streamInitPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 0) streamInit_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (streamInitPost_local _)
    streamInitFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 144⟩, ⟨0, 0⟩, ⟨0x8000, 8⟩] [⟨0x3000, 80⟩]

theorem streamAadFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamAadContract Arm.abi 2304).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamAadContract, Spec.Sm4.Gcm.streamAadSig, Spec.Sm4.Gcm.streamAadPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [streamAadFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using streamAadFrameSat

theorem streamAad_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 784 2 streamAad)
      (Spec.Sm4.Gcm.streamAadContract Arm.abi 2304) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.streamAadPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 2) streamAad_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (streamAadPost_local _)
    streamAadFrameSat_pre

/-- A state satisfying the preconditions of `vg_sm4_gcm_stream_encrypt` and
`vg_sm4_gcm_stream_decrypt`, without the working space: their four words of
stack arguments at `0x8000`. -/
def crFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 144⟩, ⟨0x8000, 16⟩] [⟨0x3000, 80⟩, ⟨0, 0⟩]

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamEncryptContract Arm.abi 2320).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamEncryptContract, Spec.Sm4.Gcm.streamCryptSig,
    Spec.Sm4.Gcm.streamEncryptPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [crFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using crFrameSat

theorem streamEncrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 800 4 streamEncrypt)
      (Spec.Sm4.Gcm.streamEncryptContract Arm.abi 2320) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.streamEncryptPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 4) streamEncrypt_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (streamEncryptPost_local _)
    streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamDecryptContract Arm.abi 2320).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamDecryptContract, Spec.Sm4.Gcm.streamCryptSig,
    Spec.Sm4.Gcm.streamDecryptPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [crFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using crFrameSat

theorem streamDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 800 4 streamDecrypt)
      (Spec.Sm4.Gcm.streamDecryptContract Arm.abi 2320) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.streamDecryptPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 4) streamDecrypt_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (streamDecryptPost_local _)
    streamDecryptFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_finish`'s precondition, without the
working space: its three words of stack arguments at `0x8000`. -/
def finFrameSat : State :=
  mkSat2 (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 144⟩, ⟨0x8000, 12⟩] [⟨0x3000, 80⟩, ⟨0x4000, 16⟩]

theorem finFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamFinishContract Arm.abi 2320).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamFinishContract, Spec.Sm4.Gcm.streamFinishSig, Spec.Sm4.Gcm.streamFinishPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, mkSat2, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat

theorem streamFinish_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 800 3 streamFinish)
      (Spec.Sm4.Gcm.streamFinishContract Arm.abi 2320) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.streamFinishPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 3) streamFinish_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (streamFinishPost_local _) finFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_verify`'s precondition, without the
working space: its four words of stack arguments at `0x8000`. -/
def verFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 144⟩, ⟨0, 0⟩, ⟨0x8000, 16⟩] [⟨0x3000, 80⟩]

theorem verFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamVerifyContract Arm.abi 2320).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamVerifyContract, Spec.Sm4.Gcm.streamVerifySig, Spec.Sm4.Gcm.streamVerifyPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [verFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using verFrameSat

theorem streamVerify_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 800 4 streamVerify)
      (Spec.Sm4.Gcm.streamVerifyContract Arm.abi 2320) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.streamVerifyPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 4) streamVerify_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (streamVerifyPost_local _) verFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_seal`'s precondition, without the working
space: its four words of stack arguments at `0x8000`. -/
def sealFrameSat : State :=
  mkSat3 (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0)
    [⟨0x1000, 144⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 16⟩] [⟨0, 0⟩, ⟨0x4000, 16⟩]

theorem sealFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.sealContract Arm.abi 2320).pre s := by
  implies_sat [Spec.Sm4.Gcm.sealContract, Spec.Sm4.Gcm.sealSig, Spec.Sm4.Gcm.sealPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [sealFrameSat, mkSat3, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 800 4 «seal»)
      (Spec.Sm4.Gcm.sealContract Arm.abi 2320) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.sealSig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.sealPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 4) seal_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_open`'s precondition, without the working
space: its five words of stack arguments at `0x8000`. -/
def openFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0)
    [⟨0x1000, 144⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x8000, 20⟩] [⟨0, 0⟩]

theorem openFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.openContract Arm.abi 2320).pre s := by
  implies_sat [Spec.Sm4.Gcm.openContract, Spec.Sm4.Gcm.openSig, Spec.Sm4.Gcm.openPost,
    Spec.Sm4.Gcm.openLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using openFrameSat

theorem open_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 800 5 «open»)
      (Spec.Sm4.Gcm.openContract Arm.abi 2320) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.openSig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.openPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (leak := some (Spec.Sm4.Gcm.openLeak Arm.abi.ptrBits))
    (m := 5) open_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (openPost_local _) openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.Sm4Gcm.Arm
