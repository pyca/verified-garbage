import VerifiedGarbage.Proof.AesGcm.X86.Verified
import VerifiedGarbage.Proof.Framework.X86.StackScratch

/-!
# AES-GCM's key setup and streaming functions on x86, with their working space on the stack

`init`, `stream_init`, `stream_aad`, `stream_encrypt` and `stream_decrypt` run
their code, proved with the working space as an argument (`Verified.lean`),
in a frame that allocates it and copies the arguments passed on the stack
(`Verified.stackScratch`): the return address, the copied argument slots
(three for `init`, four for `stream_init`, six for `stream_aad`, nine for
`stream_encrypt` and `stream_decrypt`) and the 2560 bytes of working space.
The copies are read only where the pre- and postconditions read the buffers
(`Proof/AesGcm/Scratch.lean`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.Impl.AesGcm.X86

private theorem noEsp_of {c : Prog isa} (h : NoSp c) :
    c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

/-- The frame of `withStackScratch` keeps the stack pointer for any `c` that
does, if it does for an empty body (decided for literal sizes). -/
theorem withStackScratch_spSafe {bytes n : Nat} {c : Prog isa}
    (hf : (Impl.StackScratch.X86.withStackScratch bytes n (.block [])).all
      (fun i => !isa.writesSp i) = true)
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (Impl.StackScratch.X86.withStackScratch bytes n c).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.StackScratch.X86.withStackScratch, Code.all, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at hf ⊢
  simp_all

variable (vg : GcmImpl)

theorem init_noEsp : (init vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbHead, absorbWhole, ctrCall, firstFlush, flush, ghCall, ghash1, init, j0,
    j0hash, keyCall, lens, oneAad, streamAad, streamInit, Code.allInstrs, GcmImpl.callees,
    noEsp_of vg.ctr.nosp, noEsp_of vg.ctr.expandNosp, noEsp_of vg.gh.nosp, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamInit_noEsp :
    (streamInit vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbHead, absorbWhole, ctrCall, firstFlush, flush, ghCall, ghash1, init, j0,
    j0hash, keyCall, lens, oneAad, streamAad, streamInit, Code.allInstrs, GcmImpl.callees,
    noEsp_of vg.ctr.nosp, noEsp_of vg.ctr.expandNosp, noEsp_of vg.gh.nosp, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamAad_noEsp :
    (streamAad vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbHead, absorbWhole, ctrCall, firstFlush, flush, ghCall, ghash1, init, j0,
    j0hash, keyCall, lens, oneAad, streamAad, streamInit, Code.allInstrs, GcmImpl.callees,
    noEsp_of vg.ctr.nosp, noEsp_of vg.ctr.expandNosp, noEsp_of vg.gh.nosp, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem init_stackUse : stackUse (init vg.callees) ≤ 28 := by
  simp only [absorb, absorbHead, absorbWhole, ctrCall, firstFlush, flush, ghCall, ghash1, init, j0,
    j0hash, keyCall, lens, oneAad, streamAad, streamInit, stackUse, GcmImpl.callees, vg.ctr.stack,
    vg.ctr.expandStack, vg.gh.stack, Nat.max_le]
  decide +kernel

theorem streamInit_stackUse : stackUse (streamInit vg.callees) ≤ 24 := by
  simp only [absorb, absorbHead, absorbWhole, ctrCall, firstFlush, flush, ghCall, ghash1, init, j0,
    j0hash, keyCall, lens, oneAad, streamAad, streamInit, stackUse, GcmImpl.callees, vg.ctr.stack,
    vg.ctr.expandStack, vg.gh.stack, Nat.max_le]
  decide +kernel

theorem streamAad_stackUse : stackUse (streamAad vg.callees) ≤ 24 := by
  simp only [absorb, absorbHead, absorbWhole, ctrCall, firstFlush, flush, ghCall, ghash1, init, j0,
    j0hash, keyCall, lens, oneAad, streamAad, streamInit, stackUse, GcmImpl.callees, vg.ctr.stack,
    vg.ctr.expandStack, vg.gh.stack, Nat.max_le]
  decide +kernel

/-- A state satisfying `vg_aes_gcm_init`'s precondition, without the working
space: a 16-byte key at `0x1000` and the context at `0x2000`, as stack
arguments at `0x8004`. -/
def initFrameSat : State :=
  { initSat with rd := [⟨0x1000, 16⟩], wr := [⟨0x2000, 256⟩, ⟨0x8004, 12⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Gcm.initContract X86.abi 2608).pre s := by
  implies_sat [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using initFrameSat

theorem init_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2580 3 (init vg.callees))
      (Spec.Gcm.initContract X86.abi 2608) :=
  X86.Verified.stackScratch (sig := Spec.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre X86.abi.ptrBits) (post := Spec.Gcm.initPost X86.abi.ptrBits)
    (wa := true) (stack := 28) (bytes := 2580) (init_verified (vg := vg)) (by decide)
    (init_noEsp vg) (init_stackUse vg) (initPre_local _) (initPost_local _) initFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State :=
  { siSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩], wr := [⟨0x3000, 80⟩, ⟨0x8004, 16⟩] }

theorem streamInitFrameSat_pre : ∃ s, (Spec.Gcm.streamInitContract X86.abi 2608).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [streamInitFrameSat, siSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using streamInitFrameSat

theorem streamInit_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2584 4 (streamInit vg.callees))
      (Spec.Gcm.streamInitContract X86.abi 2608) :=
  X86.Verified.stackScratch (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamInitPost X86.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamInit_verified (vg := vg)) (by decide) (streamInit_noEsp vg)
    (streamInit_stackUse vg) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (streamInitPost_local _) streamInitFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State :=
  { saSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩], wr := [⟨0x3000, 80⟩, ⟨0x8004, 24⟩] }

theorem streamAadFrameSat_pre : ∃ s, (Spec.Gcm.streamAadContract X86.abi 2616).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [streamAadFrameSat, saSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using streamAadFrameSat

theorem streamAad_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2592 6 (streamAad vg.callees))
      (Spec.Gcm.streamAadContract X86.abi 2616) :=
  X86.Verified.stackScratch (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamAadPost X86.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2592) (streamAad_verified (vg := vg)) (by decide) (streamAad_noEsp vg)
    (streamAad_stackUse vg) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (streamAadPost_local _) streamAadFrameSat_pre

theorem streamEncrypt_noEsp :
    (streamEncrypt vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, finTag, firstFlush, flush, ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneTag, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit, streamVerify, tag, textAbsorb, Code.allInstrs, GcmImpl.callees,
    noEsp_of vg.ctr.nosp, noEsp_of vg.ctr.expandNosp, noEsp_of vg.gh.nosp, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamEncrypt_stackUse : stackUse (streamEncrypt vg.callees) ≤ 28 := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, finTag, firstFlush, flush, ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneTag, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit, streamVerify, tag, textAbsorb, stackUse, GcmImpl.callees, vg.ctr.stack,
    vg.ctr.expandStack, vg.gh.stack, Nat.max_le]
  decide +kernel

theorem streamDecrypt_noEsp :
    (streamDecrypt vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, finTag, firstFlush, flush, ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneTag, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit, streamVerify, tag, textAbsorb, Code.allInstrs, GcmImpl.callees,
    noEsp_of vg.ctr.nosp, noEsp_of vg.ctr.expandNosp, noEsp_of vg.gh.nosp, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamDecrypt_stackUse : stackUse (streamDecrypt vg.callees) ≤ 28 := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, finTag, firstFlush, flush, ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneTag, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit, streamVerify, tag, textAbsorb, stackUse, GcmImpl.callees, vg.ctr.stack,
    vg.ctr.expandStack, vg.gh.stack, Nat.max_le]
  decide +kernel

/-- A state satisfying the preconditions of `vg_aes_gcm_stream_encrypt` and
`vg_aes_gcm_stream_decrypt`, without the working space: their nine argument
slots at `0x8004`. -/
def crFrameSat : State :=
  { crSat with rd := [⟨0x1000, 256⟩], wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x8004, 36⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Gcm.streamEncryptContract X86.abi 2632).pre s := by
  implies_sat [Spec.Gcm.streamEncryptContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Spec.Gcm.streamEncryptPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [crFrameSat, crSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using crFrameSat

theorem streamEncrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2604 9 (streamEncrypt vg.callees))
      (Spec.Gcm.streamEncryptContract X86.abi 2632) :=
  X86.Verified.stackScratch (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre X86.abi.ptrBits)
    (post := Spec.Gcm.streamEncryptPost X86.abi.ptrBits) (wa := true) (stack := 28)
    (bytes := 2604) (streamEncrypt_verified (vg := vg)) (by decide) (streamEncrypt_noEsp vg)
    (streamEncrypt_stackUse vg) (streamTextPre_local _) (streamEncryptPost_local _)
    streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Gcm.streamDecryptContract X86.abi 2632).pre s := by
  implies_sat [Spec.Gcm.streamDecryptContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Spec.Gcm.streamDecryptPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [crFrameSat, crSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using crFrameSat

theorem streamDecrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2604 9 (streamDecrypt vg.callees))
      (Spec.Gcm.streamDecryptContract X86.abi 2632) :=
  X86.Verified.stackScratch (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre X86.abi.ptrBits)
    (post := Spec.Gcm.streamDecryptPost X86.abi.ptrBits) (wa := true) (stack := 28)
    (bytes := 2604) (streamDecrypt_verified (vg := vg)) (by decide) (streamDecrypt_noEsp vg)
    (streamDecrypt_stackUse vg) (streamTextPre_local _) (streamDecryptPost_local _)
    streamDecryptFrameSat_pre

theorem streamFinish_noEsp :
    (streamFinish vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbHead, absorbWhole, absorbTail, cmp, cmpTail, copyLoop, crypt,
    cryptEntry, cryptHead, cryptTail, cryptWhole, ctrCall, finEntry, finTag, firstFlush, flush,
    ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneEntry, oneTag, recv,
    setData, setText, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit,
    streamVerify, tag, tagLenOk, tagOut, textAbsorb, «seal», «open», Code.allInstrs,
    GcmImpl.callees, noEsp_of vg.ctr.nosp, noEsp_of vg.ctr.expandNosp, noEsp_of vg.gh.nosp,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem streamFinish_stackUse : stackUse (streamFinish vg.callees) ≤ 28 := by
  simp only [absorb, absorbHead, absorbWhole, absorbTail, cmp, cmpTail, copyLoop, crypt,
    cryptEntry, cryptHead, cryptTail, cryptWhole, ctrCall, finEntry, finTag, firstFlush, flush,
    ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneEntry, oneTag, recv,
    setData, setText, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit,
    streamVerify, tag, tagLenOk, tagOut, textAbsorb, «seal», «open», stackUse, GcmImpl.callees,
    vg.ctr.stack, vg.ctr.expandStack, vg.gh.stack, Nat.max_le]
  decide +kernel

theorem streamVerify_noEsp :
    (streamVerify vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbHead, absorbWhole, absorbTail, cmp, cmpTail, copyLoop, crypt,
    cryptEntry, cryptHead, cryptTail, cryptWhole, ctrCall, finEntry, finTag, firstFlush, flush,
    ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneEntry, oneTag, recv,
    setData, setText, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit,
    streamVerify, tag, tagLenOk, tagOut, textAbsorb, «seal», «open», Code.allInstrs,
    GcmImpl.callees, noEsp_of vg.ctr.nosp, noEsp_of vg.ctr.expandNosp, noEsp_of vg.gh.nosp,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem streamVerify_stackUse : stackUse (streamVerify vg.callees) ≤ 28 := by
  simp only [absorb, absorbHead, absorbWhole, absorbTail, cmp, cmpTail, copyLoop, crypt,
    cryptEntry, cryptHead, cryptTail, cryptWhole, ctrCall, finEntry, finTag, firstFlush, flush,
    ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneEntry, oneTag, recv,
    setData, setText, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit,
    streamVerify, tag, tagLenOk, tagOut, textAbsorb, «seal», «open», stackUse, GcmImpl.callees,
    vg.ctr.stack, vg.ctr.expandStack, vg.gh.stack, Nat.max_le]
  decide +kernel

theorem seal_noEsp :
    («seal» vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbHead, absorbWhole, absorbTail, cmp, cmpTail, copyLoop, crypt,
    cryptEntry, cryptHead, cryptTail, cryptWhole, ctrCall, finEntry, finTag, firstFlush, flush,
    ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneEntry, oneTag, recv,
    setData, setText, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit,
    streamVerify, tag, tagLenOk, tagOut, textAbsorb, «seal», «open», Code.allInstrs,
    GcmImpl.callees, noEsp_of vg.ctr.nosp, noEsp_of vg.ctr.expandNosp, noEsp_of vg.gh.nosp,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem seal_stackUse : stackUse («seal» vg.callees) ≤ 28 := by
  simp only [absorb, absorbHead, absorbWhole, absorbTail, cmp, cmpTail, copyLoop, crypt,
    cryptEntry, cryptHead, cryptTail, cryptWhole, ctrCall, finEntry, finTag, firstFlush, flush,
    ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneEntry, oneTag, recv,
    setData, setText, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit,
    streamVerify, tag, tagLenOk, tagOut, textAbsorb, «seal», «open», stackUse, GcmImpl.callees,
    vg.ctr.stack, vg.ctr.expandStack, vg.gh.stack, Nat.max_le, X86.frameBytes, List.length_cons,
    List.length_nil, Nat.zero_le, true_and, and_true]
  decide +kernel

theorem open_noEsp :
    («open» vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbHead, absorbWhole, absorbTail, cmp, cmpTail, copyLoop, crypt,
    cryptEntry, cryptHead, cryptTail, cryptWhole, ctrCall, finEntry, finTag, firstFlush, flush,
    ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneEntry, oneTag, recv,
    setData, setText, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit,
    streamVerify, tag, tagLenOk, tagOut, textAbsorb, «seal», «open», Code.allInstrs,
    GcmImpl.callees, noEsp_of vg.ctr.nosp, noEsp_of vg.ctr.expandNosp, noEsp_of vg.gh.nosp,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem open_stackUse : stackUse («open» vg.callees) ≤ 28 := by
  simp only [absorb, absorbHead, absorbWhole, absorbTail, cmp, cmpTail, copyLoop, crypt,
    cryptEntry, cryptHead, cryptTail, cryptWhole, ctrCall, finEntry, finTag, firstFlush, flush,
    ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneEntry, oneTag, recv,
    setData, setText, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit,
    streamVerify, tag, tagLenOk, tagOut, textAbsorb, «seal», «open», stackUse, GcmImpl.callees,
    vg.ctr.stack, vg.ctr.expandStack, vg.gh.stack, Nat.max_le, X86.frameBytes, List.length_cons,
    List.length_nil, Nat.zero_le, true_and, and_true]
  decide +kernel

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition, without
the working space: its eight argument slots at `0x8004`. -/
def finFrameSat : State :=
  { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x8004, 32⟩] }

theorem finFrameSat_pre : ∃ s, (Spec.Gcm.streamFinishContract X86.abi 2628).pre s := by
  implies_sat [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre,
    Spec.Gcm.streamFinishPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finFrameSat

theorem streamFinish_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2600 8 (streamFinish vg.callees))
      (Spec.Gcm.streamFinishContract X86.abi 2628) :=
  X86.Verified.stackScratch (sig := Spec.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamFinishPre X86.abi.ptrBits)
    (post := Spec.Gcm.streamFinishPost X86.abi.ptrBits) (wa := true) (stack := 28)
    (bytes := 2600) (streamFinish_verified (vg := vg)) (by decide) (streamFinish_noEsp vg)
    (streamFinish_stackUse vg) (streamFinishPre_local _) (streamFinishPost_local _)
    finFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition, without
the working space: its nine argument slots at `0x8004`. -/
def verFrameSat : State :=
  { verSat with wr := [⟨0x3000, 80⟩, ⟨0x8004, 36⟩] }

theorem verFrameSat_pre : ∃ s, (Spec.Gcm.streamVerifyContract X86.abi 2632).pre s := by
  implies_sat [Spec.Gcm.streamVerifyContract, Spec.Gcm.streamVerifySig, Spec.Gcm.streamVerifyPre,
    Spec.Gcm.streamVerifyPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [verFrameSat, verSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using verFrameSat

theorem streamVerify_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2604 9 (streamVerify vg.callees))
      (Spec.Gcm.streamVerifyContract X86.abi 2632) :=
  X86.Verified.stackScratch (sig := Spec.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamVerifyPre X86.abi.ptrBits)
    (post := Spec.Gcm.streamVerifyPost X86.abi.ptrBits) (wa := true) (stack := 28)
    (bytes := 2604) (streamVerify_verified (vg := vg)) (by decide) (streamVerify_noEsp vg)
    (streamVerify_stackUse vg) (streamVerifyPre_local _) (streamVerifyPost_local _)
    verFrameSat_pre

/-- A state satisfying `vg_aes_gcm_seal`'s precondition, without the working
space: its nine argument slots at `0x8004`. -/
def sealFrameSat : State :=
  { sealSat with wr := [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x8004, 36⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Gcm.sealContract X86.abi 2632).pre s := by
  implies_sat [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, Spec.Gcm.sealPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [sealFrameSat, sealSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using sealFrameSat

theorem seal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2604 9 («seal» vg.callees))
      (Spec.Gcm.sealContract X86.abi 2632) :=
  X86.Verified.stackScratch (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.sealPre X86.abi.ptrBits)
    (post := Spec.Gcm.sealPost X86.abi.ptrBits) (wa := true) (stack := 28)
    (bytes := 2604) (seal_verified (vg := vg)) (by decide) (seal_noEsp vg)
    (seal_stackUse vg) (sealPre_local _) (sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_open`'s precondition, without the working
space: its ten argument slots at `0x8004`. -/
def openFrameSat : State :=
  { openSat with wr := [⟨0x3000, 0⟩, ⟨0x8004, 40⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Gcm.openContract X86.abi 2636).pre s := by
  implies_sat [Spec.Gcm.openContract, Spec.Gcm.openSig, Spec.Gcm.openPre, Spec.Gcm.openPost,
    Spec.Gcm.openLeak, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [openFrameSat, openSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using openFrameSat

theorem open_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2608 10 («open» vg.callees))
      (Spec.Gcm.openContract X86.abi 2636) :=
  X86.Verified.stackScratch (sig := Spec.Gcm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openPre X86.abi.ptrBits)
    (post := Spec.Gcm.openPost X86.abi.ptrBits) (wa := true) (stack := 28)
    (leak := some (Spec.Gcm.openLeak X86.abi.ptrBits))
    (bytes := 2608) (open_verified (vg := vg)) (by decide) (open_noEsp vg)
    (open_stackUse vg) (openPre_local _) (openPost_local _) openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.AesGcm.X86
