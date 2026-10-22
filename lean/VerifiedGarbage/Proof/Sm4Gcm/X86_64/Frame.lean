module

public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Verified
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/-!
# SM4-GCM on x86-64, with its working space on the stack

Each function runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame that allocates it, as AES-GCM's
(`Proof/AesGcm/X86_64/Frame.lean`), below which its calls use the `stkN`
bytes that a call of `vg_sm4_ctr32` takes. `init` and `stream_finish`, whose
working space is their last argument in a register, have a frame of 2568
bytes (`Verified.stackScratch`): the 2560 bytes of working space, and 8 more
to keep `rsp` aligned. The working space of the others is their last
argument, passed on the stack after the six argument registers and their
other stack arguments: their frames (`Verified.stackArgScratch`) also hold a
copy of those, 2576 bytes for `stream_encrypt`, `stream_decrypt` and
`stream_verify` (none), 2592 for `seal` (two) and 2600 for `open` (three,
and a leak, whether it succeeds, which reads only its buffers:
`openLeak_local`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.Impl.Sm4Gcm.X86_64
open VG.Proof.AesGcm.X86_64 (GcmImpl)

variable (v : GcmImpl)

/-- A state satisfying `vg_sm4_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.initContract X86_64.abi 5792).pre s := by
  implies_sat [Spec.Sm4.Gcm.initContract, Spec.Sm4.Gcm.initSig, Spec.Sm4.Gcm.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 2568 .rdx init)
      (Spec.Sm4.Gcm.initContract X86_64.abi 5792) :=
  X86_64.Verified.stackScratch (sig := Spec.Sm4.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (post := Spec.Sm4.Gcm.initPost X86_64.abi.ptrBits) (wa := true) (stack := stkN) (bytes := 2568)
    init_verified (by decide) (by decide) (by decide) init_spSafe init_xdepth initFrameSat_pre

/-- A state satisfying the preconditions of `vg_sm4_gcm_stream_encrypt` and
`vg_sm4_gcm_stream_decrypt`, without the working space. -/
def crFrameSat : State := { crSat with rd := [⟨0x1000, 256⟩], wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamEncryptFrameSat_pre :
    ∃ s, (Spec.Sm4.Gcm.streamEncryptContract X86_64.abi 5800).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamEncryptContract, Spec.Sm4.Gcm.streamCryptSig,
    Spec.Sm4.Gcm.streamEncryptPost, X86_64.abi, X86_64.argRegs] [crFrameSat, crSat] using crFrameSat

theorem streamEncrypt_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2576 0 (streamEncrypt v.callees))
      (Spec.Sm4.Gcm.streamEncryptContract X86_64.abi 5800) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.streamEncryptPost X86_64.abi.ptrBits) (wa := true)
    (stack := stkN) (bytes := 2576) (streamEncrypt_verified v) (by decide) (by decide) (by decide)
    (streamEncrypt_spSafe v) (streamEncrypt_xdepth v) (Proof.Sm4Gcm.pre_local _ _)
    (Proof.Sm4Gcm.streamEncryptPost_local _) streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre :
    ∃ s, (Spec.Sm4.Gcm.streamDecryptContract X86_64.abi 5800).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamDecryptContract, Spec.Sm4.Gcm.streamCryptSig,
    Spec.Sm4.Gcm.streamDecryptPost, X86_64.abi, X86_64.argRegs] [crFrameSat, crSat] using crFrameSat

theorem streamDecrypt_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2576 0 (streamDecrypt v.callees))
      (Spec.Sm4.Gcm.streamDecryptContract X86_64.abi 5800) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.streamDecryptPost X86_64.abi.ptrBits) (wa := true)
    (stack := stkN) (bytes := 2576) (streamDecrypt_verified v) (by decide) (by decide) (by decide)
    (streamDecrypt_spSafe v) (streamDecrypt_xdepth v) (Proof.Sm4Gcm.pre_local _ _)
    (Proof.Sm4Gcm.streamDecryptPost_local _) streamDecryptFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_finish`'s precondition, without
the working space. -/
def finFrameSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩] }

theorem finFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamFinishContract X86_64.abi 5792).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamFinishContract, Spec.Sm4.Gcm.streamFinishSig,
    Spec.Sm4.Gcm.streamFinishPost, X86_64.abi, X86_64.argRegs] [finFrameSat, finSat] using finFrameSat

theorem streamFinish_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2568 .r9 (streamFinish v.callees))
      (Spec.Sm4.Gcm.streamFinishContract X86_64.abi 5792) :=
  X86_64.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.streamFinishPost X86_64.abi.ptrBits) (wa := true)
    (stack := stkN) (bytes := 2568) (streamFinish_verified v) (by decide) (by decide) (by decide)
    (streamFinish_spSafe v) (streamFinish_xdepth v) finFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_verify`'s precondition, without
the working space. -/
def verFrameSat : State := { verSat with rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩], wr := [⟨0x3000, 80⟩] }

theorem verFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamVerifyContract X86_64.abi 5800).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamVerifyContract, Spec.Sm4.Gcm.streamVerifySig,
    Spec.Sm4.Gcm.streamVerifyPost, X86_64.abi, X86_64.argRegs] [verFrameSat, verSat] using verFrameSat

theorem streamVerify_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2576 0 (streamVerify v.callees))
      (Spec.Sm4.Gcm.streamVerifyContract X86_64.abi 5800) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Sm4.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.streamVerifyPost X86_64.abi.ptrBits) (wa := true)
    (stack := stkN) (bytes := 2576) (streamVerify_verified v) (by decide) (by decide) (by decide)
    (streamVerify_spSafe v) (streamVerify_xdepth v) (Proof.Sm4Gcm.pre_local _ _)
    (Proof.Sm4Gcm.streamVerifyPost_local _) verFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_seal`'s precondition, without the working
space. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 16⟩],
                 wr := [⟨0, 0⟩, ⟨0x3000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.sealContract X86_64.abi 5816).pre s := by
  implies_sat [Spec.Sm4.Gcm.sealContract, Spec.Sm4.Gcm.sealSig, Spec.Sm4.Gcm.sealPost,
    X86_64.abi, X86_64.argRegs] [sealFrameSat, sealSat] using sealFrameSat

theorem seal_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2592 2 («seal» v.callees))
      (Spec.Sm4.Gcm.sealContract X86_64.abi 5816) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Sm4.Gcm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.sealPost X86_64.abi.ptrBits) (wa := true)
    (stack := stkN) (bytes := 2592) (seal_verified v) (by decide) (by decide) (by decide)
    (seal_spSafe v) (seal_xdepth v) (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.sealPost_local _)
    sealFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_open`'s precondition, without the working
space. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 24⟩],
                 wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.openContract X86_64.abi 5824).pre s := by
  implies_sat [Spec.Sm4.Gcm.openContract, Spec.Sm4.Gcm.openSig, Spec.Sm4.Gcm.openPost,
    Spec.Sm4.Gcm.openLeak, X86_64.abi, X86_64.argRegs] [openFrameSat, openSat] using openFrameSat

theorem open_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 («open» v.callees))
      (Spec.Sm4.Gcm.openContract X86_64.abi 5824) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Sm4.Gcm.openSig) (nm := "work") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.openPost X86_64.abi.ptrBits) (wa := true)
    (stack := stkN) (leak := some (Spec.Sm4.Gcm.openLeak X86_64.abi.ptrBits)) (bytes := 2600)
    (open_verified v) (by decide) (by decide) (by decide) (open_spSafe v) (open_xdepth v)
    (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.openPost_local _) openFrameSat_pre
    (hleak := Proof.Sm4Gcm.openLeak_local _)

end VG.Proof.Sm4Gcm.X86_64
