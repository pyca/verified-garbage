import VerifiedGarbage.Proof.AesGcm.AArch64.Verified
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.TagScratch

/-!
# AES-GCM's key setup and streaming functions on AArch64, with their working space on the stack

`init`, `stream_init`, `stream_aad`, `stream_encrypt` and `stream_decrypt`
run their code, proved with the working space as an argument
(`Verified.lean`), in a frame of 2560 bytes that allocates it
(`Verified.stackScratch`).

`stream_finish`, `stream_verify`, `seal` and `open` run their code, proved
for working space that carries the tag in its first 16 bytes
(`Proof/AesGcm/Tag.lean`), in a frame that holds copies of their stack
arguments (with the working space's address in place of the tag pointer for
`seal` and `open`, whose tag is their first stack argument), the tag pointer
and the working space, and copies the tag in and out
(`Verified.tagScratch`): 2576 bytes, and 2592 for `open`, which has two
stack arguments. Their code uses no frames of its own, nor do the functions
it calls (`noFrames`), so no stack below the frame.
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

theorem depth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

section
variable (v : GcmImpl)

theorem tagFns_noFrames :
    (streamFinish v.callees).noFrames = true ∧ (streamVerify v.callees).noFrames = true ∧
      («seal» v.callees).noFrames = true ∧ («open» v.callees).noFrames = true := by
  simp [Code.noFrames, GcmImpl.callees, v.ctr.noFrames, v.gh.noFrames, copyLoop, copy, xorLoop,
    Impl.AesGcm.AArch64.xor, minK, ghCall, absSeg1, absTail, absorb, padSeg, flush, lens, ctrCall,
    crSeg1, crSeg2, crTail, crypt, tag, j0hash, j0, cmpSeg, tlTest, tagLenOk, finBody, streamFinish,
    streamVerify, oneAad, «seal», oneCrypt, openMain, «open», encBody, decAbs, textAbs, fo]

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition, with a
16-byte tag. -/
def finFrameSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x4000, 16⟩] }

theorem finFrameSat_pre : ∃ s, (Spec.Gcm.streamFinishContract AArch64.abi 2576).pre s := by
  implies_sat [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre,
    Spec.Gcm.streamFinishPost, AArch64.abi, AArch64.argRegs] [finFrameSat, finSat] using finFrameSat

theorem streamFinish_framed :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withTagScratch 2576 0 (.reg .x5) (streamFinish v.callees))
      (Spec.Gcm.streamFinishContract AArch64.abi 2576) :=
  AArch64.Verified.tagScratch (sig := Spec.Gcm.streamFinishSig) (q := 5) (nm := "work") (e := .u64)
    (n := 320) (wa := true) (stack := 0) (bytes := 2576) (streamFinish_verified v)
    (Proof.AesGcm.streamFinish_tagFrame _) rfl (by decide)
    (by rw [depth_of_noFrames (tagFns_noFrames v).1]) finFrameSat_pre

theorem verFrameSat_pre : ∃ s, (Spec.Gcm.streamVerifyContract AArch64.abi 2576).pre s := by
  implies_sat [Spec.Gcm.streamVerifyContract, Spec.Gcm.streamVerifySig, Spec.Gcm.streamVerifyPre,
    Spec.Gcm.streamVerifyPost, AArch64.abi, AArch64.argRegs] [finFrameSat, finSat] using finFrameSat

theorem streamVerify_framed :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withTagScratch 2576 0 (.reg .x5) (streamVerify v.callees))
      (Spec.Gcm.streamVerifyContract AArch64.abi 2576) :=
  AArch64.Verified.tagScratch (sig := Spec.Gcm.streamVerifySig) (q := 5) (nm := "work") (e := .u64)
    (n := 320) (wa := true) (stack := 0) (bytes := 2576) (streamVerify_verified v)
    (Proof.AesGcm.streamVerify_tagFrame _) rfl (by decide)
    (by rw [depth_of_noFrames (tagFns_noFrames v).2.1]) verFrameSat_pre

/-- A state satisfying `vg_aes_gcm_seal`'s precondition, with a 16-byte
tag. -/
def sealFrameSat : State := { sealSat with wr := [⟨0x4000, 0⟩, ⟨0, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Gcm.sealContract AArch64.abi 2576).pre s := by
  implies_sat [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, Spec.Gcm.sealPost,
    AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withTagScratch 2576 1 (.stack 0) («seal» v.callees))
      (Spec.Gcm.sealContract AArch64.abi 2576) :=
  AArch64.Verified.tagScratch (sig := Spec.Gcm.sealSig) (q := 5) (nm := "work") (e := .u64)
    (n := 320) (wa := true) (stack := 0) (bytes := 2576) (seal_verified v)
    (Proof.AesGcm.seal_tagFrame _) rfl (by decide)
    (by rw [depth_of_noFrames (tagFns_noFrames v).2.2.1]) sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_open`'s precondition, with a 16-byte
tag. -/
def openFrameSat : State := { openSat with wr := [⟨0x4000, 0⟩, ⟨0, 16⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Gcm.openContract AArch64.abi 2592).pre s := by
  implies_sat [Spec.Gcm.openContract, Spec.Gcm.openSig, Spec.Gcm.openPre, Spec.Gcm.openPost,
    Spec.Gcm.openLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
    List.getD, List.range, List.range.loop] [openFrameSat, openSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using openFrameSat

theorem open_framed :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withTagScratch 2592 2 (.stack 0) («open» v.callees))
      (Spec.Gcm.openContract AArch64.abi 2592) :=
  AArch64.Verified.tagScratch (sig := Spec.Gcm.openSig) (q := 5) (nm := "work") (e := .u64)
    (n := 320) (wa := true) (stack := 0) (bytes := 2592) (open_verified v)
    (Proof.AesGcm.open_tagFrame _) rfl (by decide)
    (by rw [depth_of_noFrames (tagFns_noFrames v).2.2.2]) openFrameSat_pre

end

end VG.Proof.AesGcm.AArch64
