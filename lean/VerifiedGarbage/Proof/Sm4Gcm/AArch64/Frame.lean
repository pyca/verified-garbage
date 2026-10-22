module

public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Verified
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Sm4Gcm.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/-!
# SM4-GCM on AArch64, with its working space on the stack

Every function of SM4-GCM runs its code, proved with the working space as its
last argument (`Verified.lean`), in a frame that allocates it: 768 bytes for
the working space in a register (`Verified.stackScratch`); for `seal` and
`open`, whose working space is their first and second stack argument, 784
bytes that also hold a copy of the stack argument before it, if any
(`Verified.stackArgScratch`). Below the frame, the code's calls of
`vg_sm4_ctr32` and `vg_sm4_expand_key` use 3264 bytes of stack.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.Impl.Sm4Gcm.AArch64

/-- A state satisfying `vg_sm4_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.initContract AArch64.abi 4032).pre s := by
  implies_sat [Spec.Sm4.Gcm.initContract, Spec.Sm4.Gcm.initSig, Spec.Sm4.Gcm.initPost, AArch64.abi,
    AArch64.argRegs, stackBelow] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 768 .x2 (init))
      (Spec.Sm4.Gcm.initContract AArch64.abi 4032) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm4.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 96)
    (post := Spec.Sm4.Gcm.initPost AArch64.abi.ptrBits) (wa := true) (stack := 3264) (bytes := 768)
    (init_verified) (by decide) (by decide) initFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_encrypt`'s precondition, without the working
space. -/
def streamEncryptFrameSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamEncryptContract AArch64.abi 4032).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamEncryptContract, Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamEncryptPost, AArch64.abi,
    AArch64.argRegs, stackBelow] [streamEncryptFrameSat, streamCryptSat] using streamEncryptFrameSat

theorem streamEncrypt_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (streamEncrypt v.callees))
      (Spec.Sm4.Gcm.streamEncryptContract AArch64.abi 4032) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64) (n := 96)
    (post := Spec.Sm4.Gcm.streamEncryptPost AArch64.abi.ptrBits) (wa := true) (stack := 3264) (bytes := 768)
    (streamEncrypt_verified v) (by decide) (by decide) streamEncryptFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_decrypt`'s precondition, without the working
space. -/
def streamDecryptFrameSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamDecryptContract AArch64.abi 4032).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamDecryptContract, Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamDecryptPost, AArch64.abi,
    AArch64.argRegs, stackBelow] [streamDecryptFrameSat, streamCryptSat] using streamDecryptFrameSat

theorem streamDecrypt_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (streamDecrypt v.callees))
      (Spec.Sm4.Gcm.streamDecryptContract AArch64.abi 4032) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64) (n := 96)
    (post := Spec.Sm4.Gcm.streamDecryptPost AArch64.abi.ptrBits) (wa := true) (stack := 3264) (bytes := 768)
    (streamDecrypt_verified v) (by decide) (by decide) streamDecryptFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_finish`'s precondition, without the working
space. -/
def streamFinishFrameSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩] }

theorem streamFinishFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamFinishContract AArch64.abi 4032).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamFinishContract, Spec.Sm4.Gcm.streamFinishSig, Spec.Sm4.Gcm.streamFinishPost, AArch64.abi,
    AArch64.argRegs, stackBelow] [streamFinishFrameSat, finSat] using streamFinishFrameSat

theorem streamFinish_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 768 .x5 (streamFinish v.callees))
      (Spec.Sm4.Gcm.streamFinishContract AArch64.abi 4032) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamFinishSig) (nm := "work") (e := .u64) (n := 96)
    (post := Spec.Sm4.Gcm.streamFinishPost AArch64.abi.ptrBits) (wa := true) (stack := 3264) (bytes := 768)
    (streamFinish_verified v) (by decide) (by decide) streamFinishFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_verify`'s precondition, without the working
space. -/
def streamVerifyFrameSat : State := { verSat with wr := [⟨0x3000, 80⟩] }

theorem streamVerifyFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamVerifyContract AArch64.abi 4032).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamVerifyContract, Spec.Sm4.Gcm.streamVerifySig, Spec.Sm4.Gcm.streamVerifyPost, AArch64.abi,
    AArch64.argRegs, stackBelow] [streamVerifyFrameSat, verSat] using streamVerifyFrameSat

theorem streamVerify_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (streamVerify v.callees))
      (Spec.Sm4.Gcm.streamVerifyContract AArch64.abi 4032) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamVerifySig) (nm := "work") (e := .u64) (n := 96)
    (post := Spec.Sm4.Gcm.streamVerifyPost AArch64.abi.ptrBits) (wa := true) (stack := 3264) (bytes := 768)
    (streamVerify_verified v) (by decide) (by decide) streamVerifyFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_seal`'s precondition, without the working
space: no stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩], wr := [⟨0x4000, 0⟩, ⟨0x6000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.sealContract AArch64.abi 4048).pre s := by
  implies_sat [Spec.Sm4.Gcm.sealContract, Spec.Sm4.Gcm.sealSig, Spec.Sm4.Gcm.sealPost,
    AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
    List.range.loop, stackBelow] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed (v : GcmImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 784 0 («seal» v.callees))
      (Spec.Sm4.Gcm.sealContract AArch64.abi 4048) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Sm4.Gcm.sealSig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.sealPost AArch64.abi.ptrBits) (wa := true) (stack := 3264)
    (bytes := 784) (seal_verified v) (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _)
    (Proof.Sm4Gcm.sealPost_local (pb := AArch64.abi.ptrBits)) sealFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_open`'s precondition, without the working
space: `tag_len` 0, its one stack argument. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x6000, 0⟩, ⟨0x8000, 8⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.openContract AArch64.abi 4048).pre s := by
  implies_sat [Spec.Sm4.Gcm.openContract, Spec.Sm4.Gcm.openSig, Spec.Sm4.Gcm.openPost,
    Spec.Sm4.Gcm.openLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
    List.getD, List.range, List.range.loop, stackBelow] [openFrameSat, openSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using openFrameSat

theorem open_framed (v : GcmImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 784 1 («open» v.callees))
      (Spec.Sm4.Gcm.openContract AArch64.abi 4048) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Sm4.Gcm.openSig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.openPost AArch64.abi.ptrBits) (wa := true) (stack := 3264)
    (bytes := 784) (leak := some (Spec.Sm4.Gcm.openLeak AArch64.abi.ptrBits))
    (open_verified v) (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _)
    (Proof.Sm4Gcm.openPost_local (pb := AArch64.abi.ptrBits)) openFrameSat_pre
    (hleak := Proof.Sm4Gcm.openLeak_local (pb := AArch64.abi.ptrBits))

end VG.Proof.Sm4Gcm.AArch64
