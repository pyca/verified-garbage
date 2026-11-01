module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgs
import VerifiedGarbage.Proof.Framework.SigEval

/-!
# AES-GCM on RISC-V, with its working space on the stack

Each function runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame that allocates it: the functions whose
arguments all arrive in registers in a frame of 2560 bytes, the working
space in the next register (`Verified.stackScratchL`); `seal` and `open`,
whose last arguments arrive on the stack, in a frame that copies them and
then passes the working space's address (`Verified.stackScratchArgs`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

/-- A state satisfying `vg_aes_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Gcm.initContract RISCV64.abi 2560).pre s := by
  implies_sat [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
    RISCV64.abi, RISCV64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a3 init)
      (Spec.Gcm.initContract RISCV64.abi 2560) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre RISCV64.abi.ptrBits) (post := Spec.Gcm.initPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2560) init_verified (by decide) (by decide) initFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State := { streamInitSat with wr := [⟨0x3000, 80⟩] }

theorem streamInitFrameSat_pre : ∃ s, (Spec.Gcm.streamInitContract RISCV64.abi 4608).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    RISCV64.abi, RISCV64.argRegs] [streamInitFrameSat, streamInitSat] using streamInitFrameSat

theorem streamInit_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a4 streamInit)
      (Spec.Gcm.streamInitContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamInitPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamInit_verified (by decide) (by decide) streamInitFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State := { streamAadSat with wr := [⟨0x3000, 80⟩] }

theorem streamAadFrameSat_pre : ∃ s, (Spec.Gcm.streamAadContract RISCV64.abi 4608).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    RISCV64.abi, RISCV64.argRegs] [streamAadFrameSat, streamAadSat] using streamAadFrameSat

theorem streamAad_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a5 streamAad)
      (Spec.Gcm.streamAadContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamAadPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamAad_verified (by decide) (by decide) streamAadFrameSat_pre

/-- A state satisfying the preconditions of `vg_aes_gcm_stream_encrypt` and
`vg_aes_gcm_stream_decrypt`, without the working space. -/
def streamCryptFrameSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Gcm.streamEncryptContract RISCV64.abi 4608).pre s := by
  implies_sat [Spec.Gcm.streamEncryptContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Spec.Gcm.streamEncryptPost, RISCV64.abi, RISCV64.argRegs] [streamCryptFrameSat, streamCryptSat]
    using streamCryptFrameSat

theorem streamEncrypt_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a7 streamEncrypt)
      (Spec.Gcm.streamEncryptContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre RISCV64.abi.ptrBits)
    (post := Spec.Gcm.streamEncryptPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamEncrypt_verified (by decide) (by decide) streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Gcm.streamDecryptContract RISCV64.abi 4608).pre s := by
  implies_sat [Spec.Gcm.streamDecryptContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Spec.Gcm.streamDecryptPost, RISCV64.abi, RISCV64.argRegs] [streamCryptFrameSat, streamCryptSat]
    using streamCryptFrameSat

theorem streamDecrypt_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a7 streamDecrypt)
      (Spec.Gcm.streamDecryptContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre RISCV64.abi.ptrBits)
    (post := Spec.Gcm.streamDecryptPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamDecrypt_verified (by decide) (by decide) streamDecryptFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition, without
the working space. -/
def finFrameSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩] }

theorem finFrameSat_pre : ∃ s, (Spec.Gcm.streamFinishContract RISCV64.abi 4608).pre s := by
  implies_sat [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre,
    Spec.Gcm.streamFinishPost, RISCV64.abi, RISCV64.argRegs] [finFrameSat, finSat] using finFrameSat

theorem streamFinish_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a6 streamFinish)
      (Spec.Gcm.streamFinishContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamFinishPre RISCV64.abi.ptrBits)
    (post := Spec.Gcm.streamFinishPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamFinish_verified (by decide) (by decide) finFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition, without
the working space. -/
def verFrameSat : State := { verSat with wr := [⟨0x3000, 80⟩] }

theorem verFrameSat_pre : ∃ s, (Spec.Gcm.streamVerifyContract RISCV64.abi 4608).pre s := by
  implies_sat [Spec.Gcm.streamVerifyContract, Spec.Gcm.streamVerifySig, Spec.Gcm.streamVerifyPre,
    Spec.Gcm.streamVerifyPost, RISCV64.abi, RISCV64.argRegs] [verFrameSat, verSat] using verFrameSat

theorem streamVerify_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a7 streamVerify)
      (Spec.Gcm.streamVerifyContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamVerifyPre RISCV64.abi.ptrBits)
    (post := Spec.Gcm.streamVerifyPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamVerify_verified (by decide) (by decide) verFrameSat_pre

/-- A state satisfying `vg_aes_gcm_seal`'s precondition, without the working
space: `tag` alone on the stack. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x9000, 8⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Gcm.sealContract RISCV64.abi 4624).pre s := by
  implies_sat [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, Spec.Gcm.sealPost, RISCV64.abi,
    RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealFrameSat

/-- `seal`, whose `tag` arrives on the stack: the frame copies it, then the
working space's address, above its stack pointer (`Verified.stackScratchArgs`). -/
theorem seal_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2576 1 «seal»)
      (Spec.Gcm.sealContract RISCV64.abi 4624) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Gcm.sealPre RISCV64.abi.ptrBits) (post := Spec.Gcm.sealPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 2048) (bytes := 2576) (m := 1) seal_verified (by decide) (by decide)
    (Proof.AesGcm.sealPre_local _) (Proof.AesGcm.sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_open`'s precondition, without the working
space: `tag` and `tag_len` alone on the stack. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9000, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Gcm.openContract RISCV64.abi 4640).pre s := by
  implies_sat [Spec.Gcm.openContract, Spec.Gcm.openSig, Spec.Gcm.openPre, Spec.Gcm.openPost, Spec.Gcm.openLeak,
    RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [openFrameSat, openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openFrameSat

/-- `open`, whose `tag` and `tag_len` arrive on the stack, as `seal`'s `tag` does. -/
theorem open_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 «open»)
      (Spec.Gcm.openContract RISCV64.abi 4640) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Gcm.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Gcm.openPre RISCV64.abi.ptrBits) (post := Spec.Gcm.openPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 2048) (bytes := 2592) (m := 2) (leak := some (Spec.Gcm.openLeak RISCV64.abi.ptrBits))
    open_verified (by decide) (by decide) (Proof.AesGcm.openPre_local _) (Proof.AesGcm.openPost_local _)
    openFrameSat_pre (hleak := Proof.AesGcm.openLeak_local _)

end VG.Proof.AesGcm.RISCV64
