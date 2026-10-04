import VerifiedGarbage.Proof.AesGcm.AArch64.Verified
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/-!
# AES-GCM's key setup and streaming functions on AArch64, with their working space on the stack

Every function of AES-GCM runs its code, proved with the working space as
its last argument (`Verified.lean`), in a frame that allocates it: 2560 bytes
for the working space in a register (`Verified.stackScratch`); for `seal`
and `open`, whose working space is their second and third stack argument,
2576 and 2592 bytes that also hold copies of the stack arguments before it
(`Verified.stackArgScratch`).
-/

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64

/-- A state satisfying `vg_aes_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Gcm.initContract AArch64.abi 2560).pre s := by
  implies_sat [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
    AArch64.abi, AArch64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 2560 .x3 (init v.callees))
      (Spec.Gcm.initContract AArch64.abi 2560) :=
  AArch64.Verified.stackScratch (sig := Spec.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre AArch64.abi.ptrBits) (post := Spec.Gcm.initPost AArch64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2560) (init_verified v) (by decide) (by decide)
    initFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State := { streamInitSat with wr := [⟨0x3000, 80⟩] }

theorem streamInitFrameSat_pre : ∃ s, (Spec.Gcm.streamInitContract AArch64.abi 2560).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    AArch64.abi, AArch64.argRegs] [streamInitFrameSat, streamInitSat] using streamInitFrameSat

theorem streamInit_framed (v : GcmImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2560 .x4 (streamInit v.callees))
      (Spec.Gcm.streamInitContract AArch64.abi 2560) :=
  AArch64.Verified.stackScratch (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamInitPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2560) (streamInit_verified v) (by decide) (by decide) streamInitFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State := { streamAadSat with wr := [⟨0x3000, 80⟩] }

theorem streamAadFrameSat_pre : ∃ s, (Spec.Gcm.streamAadContract AArch64.abi 2560).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    AArch64.abi, AArch64.argRegs] [streamAadFrameSat, streamAadSat] using streamAadFrameSat

theorem streamAad_framed (v : GcmImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2560 .x5 (streamAad v.callees))
      (Spec.Gcm.streamAadContract AArch64.abi 2560) :=
  AArch64.Verified.stackScratch (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamAadPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2560) (streamAad_verified v) (by decide) (by decide) streamAadFrameSat_pre

/-- A state satisfying the preconditions of `vg_aes_gcm_stream_encrypt` and
`vg_aes_gcm_stream_decrypt`, without the working space. -/
def streamCryptFrameSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Gcm.streamEncryptContract AArch64.abi 2560).pre s := by
  implies_sat [Spec.Gcm.streamEncryptContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Spec.Gcm.streamEncryptPost, AArch64.abi, AArch64.argRegs] [streamCryptFrameSat, streamCryptSat]
    using streamCryptFrameSat

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Gcm.streamDecryptContract AArch64.abi 2560).pre s := by
  implies_sat [Spec.Gcm.streamDecryptContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Spec.Gcm.streamDecryptPost, AArch64.abi, AArch64.argRegs] [streamCryptFrameSat, streamCryptSat]
    using streamCryptFrameSat

theorem streamEncrypt_framed (v : GcmImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2560 .x7 (streamEncrypt v.callees))
      (Spec.Gcm.streamEncryptContract AArch64.abi 2560) :=
  AArch64.Verified.stackScratch (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre AArch64.abi.ptrBits)
    (post := Spec.Gcm.streamEncryptPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2560) (streamEncrypt_verified v) (by decide) (by decide) streamEncryptFrameSat_pre

theorem streamDecrypt_framed (v : GcmImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2560 .x7 (streamDecrypt v.callees))
      (Spec.Gcm.streamDecryptContract AArch64.abi 2560) :=
  AArch64.Verified.stackScratch (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre AArch64.abi.ptrBits)
    (post := Spec.Gcm.streamDecryptPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2560) (streamDecrypt_verified v) (by decide) (by decide) streamDecryptFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition, without
the working space. -/
def finFrameSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩] }

theorem finFrameSat_pre : ∃ s, (Spec.Gcm.streamFinishContract AArch64.abi 2560).pre s := by
  implies_sat [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre,
    Spec.Gcm.streamFinishPost, AArch64.abi, AArch64.argRegs] [finFrameSat, finSat] using finFrameSat

theorem streamFinish_framed (v : GcmImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2560 .x6 (streamFinish v.callees))
      (Spec.Gcm.streamFinishContract AArch64.abi 2560) :=
  AArch64.Verified.stackScratch (sig := Spec.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamFinishPre AArch64.abi.ptrBits)
    (post := Spec.Gcm.streamFinishPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2560) (streamFinish_verified v) (by decide) (by decide) finFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition, without
the working space. -/
def verFrameSat : State := { verSat with wr := [⟨0x3000, 80⟩] }

theorem verFrameSat_pre : ∃ s, (Spec.Gcm.streamVerifyContract AArch64.abi 2560).pre s := by
  implies_sat [Spec.Gcm.streamVerifyContract, Spec.Gcm.streamVerifySig, Spec.Gcm.streamVerifyPre,
    Spec.Gcm.streamVerifyPost, AArch64.abi, AArch64.argRegs] [verFrameSat, verSat] using verFrameSat

theorem streamVerify_framed (v : GcmImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2560 .x7 (streamVerify v.callees))
      (Spec.Gcm.streamVerifyContract AArch64.abi 2560) :=
  AArch64.Verified.stackScratch (sig := Spec.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamVerifyPre AArch64.abi.ptrBits)
    (post := Spec.Gcm.streamVerifyPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2560) (streamVerify_verified v) (by decide) (by decide) verFrameSat_pre

/-- A state satisfying `vg_aes_gcm_seal`'s precondition, without the working
space: `tag` at 0, its one stack argument. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x8000, 8⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Gcm.sealContract AArch64.abi 2576).pre s := by
  implies_sat [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, Spec.Gcm.sealPost,
    AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed (v : GcmImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2576 1 («seal» v.callees))
      (Spec.Gcm.sealContract AArch64.abi 2576) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.sealPre AArch64.abi.ptrBits)
    (post := Spec.Gcm.sealPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2576)
    (seal_verified v) (by decide) (by decide) (sealPre_local _) (sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_open`'s precondition, without the working
space: `tag` at 0 and `tag_len` 0, its two stack arguments. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Gcm.openContract AArch64.abi 2592).pre s := by
  implies_sat [Spec.Gcm.openContract, Spec.Gcm.openSig, Spec.Gcm.openPre, Spec.Gcm.openPost,
    Spec.Gcm.openLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
    List.getD, List.range, List.range.loop] [openFrameSat, openSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using openFrameSat

theorem open_framed (v : GcmImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 («open» v.callees))
      (Spec.Gcm.openContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Gcm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openPre AArch64.abi.ptrBits)
    (post := Spec.Gcm.openPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (leak := some (Spec.Gcm.openLeak AArch64.abi.ptrBits))
    (open_verified v) (by decide) (by decide) (openPre_local _) (openPost_local _) openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.AesGcm.AArch64
