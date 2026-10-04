import VerifiedGarbage.Proof.AesGcm.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.X86_64.TagScratch

/-!
# AES-GCM's key setup and streaming start on x86-64, with their working space on the stack

`init`, `stream_init` and `stream_aad` run their code, proved with the
working space as an argument (`Verified.lean`), in a frame of 2568 bytes that
allocates it (`Verified.stackScratch`): the 2560 bytes of working space, and
8 more to keep `rsp` aligned. Their own calls use 8 bytes below it, the
return address, as `vg_aes_expand_key`, `vg_aes_ctr32` and `vg_ghash` use no
stack (`KeyImpl.noStack`, `Ctr32Impl.noStack`, `GhashImpl.noStack`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

variable (v : GcmImpl)

theorem init_xdepth : (init v.callees).x86_64Depth ≤ 8 := by
  simp only [init, streamInit, streamAad, ghash1, absorbHead, absorbWhole, absorbTail, absorb,
    flush, lens, j0hash, j0, firstFlush, oneAad, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack,
    v.key.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

theorem streamInit_xdepth : (streamInit v.callees).x86_64Depth ≤ 8 := by
  simp only [init, streamInit, streamAad, ghash1, absorbHead, absorbWhole, absorbTail, absorb,
    flush, lens, j0hash, j0, firstFlush, oneAad, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack,
    v.key.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

theorem streamAad_xdepth : (streamAad v.callees).x86_64Depth ≤ 8 := by
  simp only [init, streamInit, streamAad, ghash1, absorbHead, absorbWhole, absorbTail, absorb,
    flush, lens, j0hash, j0, firstFlush, oneAad, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack,
    v.key.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

/-- A state satisfying `vg_aes_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Gcm.initContract X86_64.abi 2576).pre s := by
  implies_sat [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (init v.callees))
      (Spec.Gcm.initContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratch (sig := Spec.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre X86_64.abi.ptrBits) (post := Spec.Gcm.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 8) (bytes := 2568) (init_verified v) (by decide) (by decide)
    (by decide) (init_spSafe v) (init_xdepth v) initFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State := { siSat with wr := [⟨0x3000, 80⟩] }

theorem streamInitFrameSat_pre : ∃ s, (Spec.Gcm.streamInitContract X86_64.abi 2576).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    X86_64.abi, X86_64.argRegs] [streamInitFrameSat, siSat] using streamInitFrameSat

theorem streamInit_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2568 .r8 (streamInit v.callees))
      (Spec.Gcm.streamInitContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratch (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamInitPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 2568) (streamInit_verified v) (by decide) (by decide) (by decide)
    (streamInit_spSafe v) (streamInit_xdepth v) streamInitFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State := { saSat with wr := [⟨0x3000, 80⟩] }

theorem streamAadFrameSat_pre : ∃ s, (Spec.Gcm.streamAadContract X86_64.abi 2576).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    X86_64.abi, X86_64.argRegs] [streamAadFrameSat, saSat] using streamAadFrameSat

theorem streamAad_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2568 .r9 (streamAad v.callees))
      (Spec.Gcm.streamAadContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratch (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamAadPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 2568) (streamAad_verified v) (by decide) (by decide) (by decide)
    (streamAad_spSafe v) (streamAad_xdepth v) streamAadFrameSat_pre

theorem streamEncrypt_xdepth : (streamEncrypt v.callees).x86_64Depth ≤ 24 := by
  have e := encryptBlocks_xdepth v v.stitch
  have d := decryptBlocks_xdepth v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, oneAad, copyLoop, xorLoop, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

theorem streamDecrypt_xdepth : (streamDecrypt v.callees).x86_64Depth ≤ 24 := by
  have e := encryptBlocks_xdepth v v.stitch
  have d := decryptBlocks_xdepth v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, oneAad, copyLoop, xorLoop, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

/-- A state satisfying the preconditions of `vg_aes_gcm_stream_encrypt` and
`vg_aes_gcm_stream_decrypt`, without the working space: `len`, their one
stack argument, at `0x8008`. -/
def crFrameSat : State :=
  { crSat with rd := [⟨0x1000, 256⟩, ⟨0x8008, 8⟩], wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Gcm.streamEncryptContract X86_64.abi 2608).pre s := by
  implies_sat [Spec.Gcm.streamEncryptContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Spec.Gcm.streamEncryptPost, X86_64.abi, X86_64.argRegs] [crFrameSat, crSat] using crFrameSat

theorem streamEncrypt_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncrypt v.callees))
      (Spec.Gcm.streamEncryptContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.streamEncryptPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamEncrypt_verified v) (by decide) (by decide) (by decide)
    (streamEncrypt_spSafe v) (streamEncrypt_xdepth v) (streamTextPre_local _) (streamEncryptPost_local _)
    streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Gcm.streamDecryptContract X86_64.abi 2608).pre s := by
  implies_sat [Spec.Gcm.streamDecryptContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Spec.Gcm.streamDecryptPost, X86_64.abi, X86_64.argRegs] [crFrameSat, crSat] using crFrameSat

theorem streamDecrypt_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecrypt v.callees))
      (Spec.Gcm.streamDecryptContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.streamDecryptPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamDecrypt_verified v) (by decide) (by decide) (by decide)
    (streamDecrypt_spSafe v) (streamDecrypt_xdepth v) (streamTextPre_local _) (streamDecryptPost_local _)
    streamDecryptFrameSat_pre

theorem streamFinish_xdepth : (streamFinish v.callees).x86_64Depth ≤ 8 := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify,
    ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail,
    crypt, tag, j0hash, j0, firstFlush, finTag, tagLenOk, recv, cmp, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack,
    v.key.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

theorem streamVerify_xdepth : (streamVerify v.callees).x86_64Depth ≤ 8 := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify,
    ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail,
    crypt, tag, j0hash, j0, firstFlush, finTag, tagLenOk, recv, cmp, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack,
    v.key.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

theorem seal_xdepth : («seal» v.callees).x86_64Depth ≤ 24 := by
  have e := encryptBlocks_xdepth v v.stitch
  have d := decryptBlocks_xdepth v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, tagLenOk, recv, cmp, copyLoop, xorLoop, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

theorem open_xdepth : («open» v.callees).x86_64Depth ≤ 24 := by
  have e := encryptBlocks_xdepth v v.stitch
  have d := decryptBlocks_xdepth v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, tagLenOk, recv, cmp, copyLoop, xorLoop, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition, with a
16-byte tag. -/
def finFrameSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x4000, 16⟩] }

theorem finFrameSat_pre : ∃ s, (Spec.Gcm.streamFinishContract X86_64.abi 2584).pre s := by
  implies_sat [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre,
    Spec.Gcm.streamFinishPost, X86_64.abi, X86_64.argRegs] [finFrameSat, finSat] using finFrameSat

theorem streamFinish_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withTagScratch 2576 0 (.reg .r9) (streamFinish v.callees))
      (Spec.Gcm.streamFinishContract X86_64.abi 2584) :=
  X86_64.Verified.tagScratch (sig := Spec.Gcm.streamFinishSig) (q := 5) (nm := "work") (e := .u64)
    (n := 320) (wa := true) (stack := 8) (bytes := 2576) (streamFinish_verified v)
    (Proof.AesGcm.streamFinish_tagFrame _) rfl (by decide) (by decide) (by decide)
    (streamFinish_spSafe v) (streamFinish_xdepth v) finFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition, with a
16-byte tag. -/
def verFrameSat : State := { verSat with wr := [⟨0x3000, 80⟩, ⟨0x4000, 16⟩] }

theorem verFrameSat_pre : ∃ s, (Spec.Gcm.streamVerifyContract X86_64.abi 2592).pre s := by
  implies_sat [Spec.Gcm.streamVerifyContract, Spec.Gcm.streamVerifySig, Spec.Gcm.streamVerifyPre,
    Spec.Gcm.streamVerifyPost, X86_64.abi, X86_64.argRegs] [verFrameSat, verSat] using verFrameSat

theorem streamVerify_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withTagScratch 2584 1 (.reg .r9) (streamVerify v.callees))
      (Spec.Gcm.streamVerifyContract X86_64.abi 2592) :=
  X86_64.Verified.tagScratch (sig := Spec.Gcm.streamVerifySig) (q := 5) (nm := "work") (e := .u64)
    (n := 320) (wa := true) (stack := 8) (bytes := 2584) (streamVerify_verified v)
    (Proof.AesGcm.streamVerify_tagFrame _) rfl (by decide) (by decide) (by decide)
    (streamVerify_spSafe v) (streamVerify_xdepth v) verFrameSat_pre

/-- A state satisfying `vg_aes_gcm_seal`'s precondition, with a 16-byte
tag. -/
def sealFrameSat : State := { sealSat with wr := [⟨0, 0⟩, ⟨0, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Gcm.sealContract X86_64.abi 2624).pre s := by
  implies_sat [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, Spec.Gcm.sealPost,
    X86_64.abi, X86_64.argRegs] [sealFrameSat, sealSat] using sealFrameSat

theorem seal_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withTagScratch 2600 3 (.stack 2) («seal» v.callees))
      (Spec.Gcm.sealContract X86_64.abi 2624) :=
  X86_64.Verified.tagScratch (sig := Spec.Gcm.sealSig) (q := 5) (nm := "work") (e := .u64)
    (n := 320) (wa := true) (stack := 24) (bytes := 2600) (seal_verified v)
    (Proof.AesGcm.seal_tagFrame _) rfl (by decide) (by decide) (by decide)
    (seal_spSafe v) (seal_xdepth v) sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_open`'s precondition, with a 16-byte
tag. -/
def openFrameSat : State := { openSat with wr := [⟨0, 0⟩, ⟨0, 16⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Gcm.openContract X86_64.abi 2632).pre s := by
  implies_sat [Spec.Gcm.openContract, Spec.Gcm.openSig, Spec.Gcm.openPre, Spec.Gcm.openPost,
    Spec.Gcm.openLeak, X86_64.abi, X86_64.argRegs] [openFrameSat, openSat] using openFrameSat

theorem open_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withTagScratch 2608 4 (.stack 2) («open» v.callees))
      (Spec.Gcm.openContract X86_64.abi 2632) :=
  X86_64.Verified.tagScratch (sig := Spec.Gcm.openSig) (q := 5) (nm := "work") (e := .u64)
    (n := 320) (wa := true) (stack := 24) (bytes := 2608) (open_verified v)
    (Proof.AesGcm.open_tagFrame _) rfl (by decide) (by decide) (by decide)
    (open_spSafe v) (open_xdepth v) openFrameSat_pre

end VG.Proof.AesGcm.X86_64
