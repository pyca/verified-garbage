module

public import VerifiedGarbage.Proof.Sm4Gcm.X86.Verified
public import VerifiedGarbage.Proof.AesGcm.X86.Frame
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.X86.StackScratch

/-!
# SM4-GCM's functions on x86, with their working space on the stack

Every function runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame that allocates it and copies the arguments
passed on the stack (`Verified.stackScratch`): the return address, the
copied argument slots (two for `init`, seven for `stream_finish`, eight for
`stream_encrypt`, `stream_decrypt`, `stream_verify` and `seal`, nine for
`open`) and the 2560 bytes of working space. The copies are read only where
the postconditions read the buffers (`Proof/Sm4Gcm/Scratch.lean`).
`stream_init` and `stream_aad` are AES-GCM's (`Proof/AesGcm/X86/Frame.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

open VG VG.X86 VG.Impl.Sm4Gcm.X86 VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»

private theorem noEsp_of {c : Prog isa} (h : NoSp c) :
    c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

variable (vg : GcmImpl)

theorem init_noEsp : init.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [init, keyCall, ctrCall, entry, Code.allInstrs, noEsp_of ctr_nosp,
    noEsp_of key_nosp, Bool.true_and, Bool.and_true]
  decide +kernel

theorem init_stackUse : stackUse init ≤ 1536 := by
  simp only [init, keyCall, ctrCall, entry, stackUse, ctrFn, keyFn, ctr_stack', key_stack',
    Nat.max_le]
  decide +kernel

theorem streamEncrypt_noEsp :
    (streamEncrypt vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, firstFlush, flush, ghCall,
    ghash1, textAbsorb, streamEncrypt, Code.allInstrs, GcmImpl.callees, noEsp_of ctr_nosp,
    noEsp_of vg.gh.nosp, Bool.true_and, Bool.and_true]
  decide +kernel

theorem streamEncrypt_stackUse : stackUse (streamEncrypt vg.callees) ≤ 1536 := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, firstFlush, flush, ghCall,
    ghash1, textAbsorb, streamEncrypt, stackUse, GcmImpl.callees, ctrFn, ctr_stack', vg.gh.stack, Nat.max_le]
  decide +kernel

theorem streamDecrypt_noEsp :
    (streamDecrypt vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, firstFlush, flush, ghCall,
    ghash1, textAbsorb, streamDecrypt, Code.allInstrs, GcmImpl.callees, noEsp_of ctr_nosp,
    noEsp_of vg.gh.nosp, Bool.true_and, Bool.and_true]
  decide +kernel

theorem streamDecrypt_stackUse : stackUse (streamDecrypt vg.callees) ≤ 1536 := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, firstFlush, flush, ghCall,
    ghash1, textAbsorb, streamDecrypt, stackUse, GcmImpl.callees, ctrFn, ctr_stack', vg.gh.stack, Nat.max_le]
  decide +kernel

theorem streamFinish_noEsp :
    (streamFinish vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [ctrCall, finTag, flush, ghCall, ghash1, lens, tag, streamFinish, Code.allInstrs, GcmImpl.callees,
    noEsp_of ctr_nosp, noEsp_of vg.gh.nosp, Bool.true_and, Bool.and_true]
  decide +kernel

theorem streamFinish_stackUse : stackUse (streamFinish vg.callees) ≤ 1536 := by
  simp only [ctrCall, finTag, flush, ghCall, ghash1, lens, tag, streamFinish, stackUse, GcmImpl.callees, ctrFn,
    ctr_stack', vg.gh.stack, Nat.max_le]
  decide +kernel

theorem streamVerify_noEsp :
    (streamVerify vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [ctrCall, finTag, flush, ghCall, ghash1, lens, tag, streamVerify, Code.allInstrs, GcmImpl.callees,
    noEsp_of ctr_nosp, noEsp_of vg.gh.nosp, Bool.true_and, Bool.and_true]
  decide +kernel

theorem streamVerify_stackUse : stackUse (streamVerify vg.callees) ≤ 1536 := by
  simp only [ctrCall, finTag, flush, ghCall, ghash1, lens, tag, streamVerify, stackUse, GcmImpl.callees, ctrFn,
    ctr_stack', vg.gh.stack, Nat.max_le]
  decide +kernel

theorem seal_noEsp : («seal» vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, flush, ghCall, ghash1, j0,
    j0hash, lens, oneAad, oneCrypt, oneTag, tag, «seal», Code.allInstrs, GcmImpl.callees, noEsp_of ctr_nosp,
    noEsp_of vg.gh.nosp, Bool.true_and, Bool.and_true]
  decide +kernel

theorem seal_stackUse : stackUse («seal» vg.callees) ≤ 1536 := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, flush, ghCall, ghash1, j0,
    j0hash, lens, oneAad, oneCrypt, oneTag, tag, «seal», stackUse, GcmImpl.callees, ctrFn, ctr_stack',
    vg.gh.stack, Nat.max_le, X86.frameBytes, List.length_cons, List.length_nil, Nat.zero_le, true_and, and_true]
  decide +kernel

theorem open_noEsp : («open» vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, flush, ghCall, ghash1, j0,
    j0hash, lens, oneAad, oneCrypt, oneTag, tag, «open», Code.allInstrs, GcmImpl.callees, noEsp_of ctr_nosp,
    noEsp_of vg.gh.nosp, Bool.true_and, Bool.and_true]
  decide +kernel

theorem open_stackUse : stackUse («open» vg.callees) ≤ 1536 := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, flush, ghCall, ghash1, j0,
    j0hash, lens, oneAad, oneCrypt, oneTag, tag, «open», stackUse, GcmImpl.callees, ctrFn, ctr_stack',
    vg.gh.stack, Nat.max_le, X86.frameBytes, List.length_cons, List.length_nil, Nat.zero_le, true_and, and_true]
  decide +kernel

/-- A state satisfying `vg_sm4_gcm_init`'s precondition, without the working
space: a 16-byte key at `0x1000` and the context at `0x2000`, as stack
arguments at `0x8004`. -/
def initFrameSat : State :=
  { initSat with rd := [⟨0x1000, 16⟩], wr := [⟨0x2000, 256⟩, ⟨0x8004, 8⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.initContract X86.abi 4112).pre s := by
  implies_sat [Spec.Sm4.Gcm.initContract, Spec.Sm4.Gcm.initSig, Spec.Sm4.Gcm.initPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using initFrameSat

theorem init_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2576 2 init)
      (Spec.Sm4.Gcm.initContract X86.abi 4112) :=
  X86.Verified.stackScratch (sig := Spec.Sm4.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (post := Spec.Sm4.Gcm.initPost X86.abi.ptrBits) (wa := true) (stack := 1536) (bytes := 2576)
    init_verified (by decide) init_noEsp init_stackUse
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (initPost_local _) initFrameSat_pre

/-- A state satisfying the preconditions of `vg_sm4_gcm_stream_encrypt` and
`vg_sm4_gcm_stream_decrypt`, without the working space: their eight argument
slots at `0x8004`. -/
def crFrameSat : State :=
  { crSat with rd := [⟨0x1000, 256⟩], wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x8004, 32⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamEncryptContract X86.abi 4136).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamEncryptContract, Spec.Sm4.Gcm.streamCryptSig,
    Spec.Sm4.Gcm.streamEncryptPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [crFrameSat, crSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using crFrameSat

theorem streamEncrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2600 8 (streamEncrypt vg.callees))
      (Spec.Sm4.Gcm.streamEncryptContract X86.abi 4136) :=
  X86.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.streamEncryptPost X86.abi.ptrBits) (wa := true) (stack := 1536)
    (bytes := 2600) (streamEncrypt_verified (vg := vg)) (by decide) (streamEncrypt_noEsp vg)
    (streamEncrypt_stackUse vg) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (streamEncryptPost_local _) streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamDecryptContract X86.abi 4136).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamDecryptContract, Spec.Sm4.Gcm.streamCryptSig,
    Spec.Sm4.Gcm.streamDecryptPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [crFrameSat, crSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using crFrameSat

theorem streamDecrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2600 8 (streamDecrypt vg.callees))
      (Spec.Sm4.Gcm.streamDecryptContract X86.abi 4136) :=
  X86.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.streamDecryptPost X86.abi.ptrBits) (wa := true) (stack := 1536)
    (bytes := 2600) (streamDecrypt_verified (vg := vg)) (by decide) (streamDecrypt_noEsp vg)
    (streamDecrypt_stackUse vg) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (streamDecryptPost_local _) streamDecryptFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_finish`'s precondition, without
the working space: its seven argument slots at `0x8004`. -/
def finFrameSat : State :=
  { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x8004, 28⟩] }

theorem finFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamFinishContract X86.abi 4132).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamFinishContract, Spec.Sm4.Gcm.streamFinishSig,
    Spec.Sm4.Gcm.streamFinishPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finFrameSat

theorem streamFinish_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2596 7 (streamFinish vg.callees))
      (Spec.Sm4.Gcm.streamFinishContract X86.abi 4132) :=
  X86.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.streamFinishPost X86.abi.ptrBits) (wa := true) (stack := 1536)
    (bytes := 2596) (streamFinish_verified (vg := vg)) (by decide) (streamFinish_noEsp vg)
    (streamFinish_stackUse vg) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (streamFinishPost_local _) finFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_verify`'s precondition, without
the working space: its eight argument slots at `0x8004`. -/
def verFrameSat : State :=
  { verSat with wr := [⟨0x3000, 80⟩, ⟨0x8004, 32⟩] }

theorem verFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamVerifyContract X86.abi 4136).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamVerifyContract, Spec.Sm4.Gcm.streamVerifySig,
    Spec.Sm4.Gcm.streamVerifyPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [verFrameSat, verSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using verFrameSat

theorem streamVerify_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2600 8 (streamVerify vg.callees))
      (Spec.Sm4.Gcm.streamVerifyContract X86.abi 4136) :=
  X86.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.streamVerifyPost X86.abi.ptrBits) (wa := true) (stack := 1536)
    (bytes := 2600) (streamVerify_verified (vg := vg)) (by decide) (streamVerify_noEsp vg)
    (streamVerify_stackUse vg) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (streamVerifyPost_local _) verFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_seal`'s precondition, without the working
space: its eight argument slots at `0x8004`. -/
def sealFrameSat : State :=
  { sealSat with wr := [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x8004, 32⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.sealContract X86.abi 4136).pre s := by
  implies_sat [Spec.Sm4.Gcm.sealContract, Spec.Sm4.Gcm.sealSig, Spec.Sm4.Gcm.sealPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [sealFrameSat, sealSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using sealFrameSat

theorem seal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2600 8 («seal» vg.callees))
      (Spec.Sm4.Gcm.sealContract X86.abi 4136) :=
  X86.Verified.stackScratch (sig := Spec.Sm4.Gcm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.sealPost X86.abi.ptrBits) (wa := true) (stack := 1536)
    (bytes := 2600) (seal_verified (vg := vg)) (by decide) (seal_noEsp vg)
    (seal_stackUse vg) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (sealPost_local _)
    sealFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_open`'s precondition, without the working
space: its nine argument slots at `0x8004`. -/
def openFrameSat : State :=
  { openSat with wr := [⟨0x3000, 0⟩, ⟨0x8004, 36⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.openContract X86.abi 4140).pre s := by
  implies_sat [Spec.Sm4.Gcm.openContract, Spec.Sm4.Gcm.openSig, Spec.Sm4.Gcm.openPost,
    Spec.Sm4.Gcm.openLeak, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [openFrameSat, openSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using openFrameSat

theorem open_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2604 9 («open» vg.callees))
      (Spec.Sm4.Gcm.openContract X86.abi 4140) :=
  X86.Verified.stackScratch (sig := Spec.Sm4.Gcm.openSig) (nm := "work") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.openPost X86.abi.ptrBits) (wa := true) (stack := 1536)
    (leak := some (Spec.Sm4.Gcm.openLeak X86.abi.ptrBits))
    (bytes := 2604) (open_verified (vg := vg)) (by decide) (open_noEsp vg)
    (open_stackUse vg) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (openPost_local _)
    openFrameSat_pre (hleak := openLeak_local _)

end VG.Proof.Sm4Gcm.X86
