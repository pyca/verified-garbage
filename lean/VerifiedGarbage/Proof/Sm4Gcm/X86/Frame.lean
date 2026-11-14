module

import VerifiedGarbage.Proof.Sm4Gcm.X86.StreamDecrypt
import VerifiedGarbage.Proof.Sm4Gcm.X86.StreamVerify
import VerifiedGarbage.Proof.Sm4Gcm.X86.Seal
import VerifiedGarbage.Proof.Sm4Gcm.X86.Open
import VerifiedGarbage.Proof.Sm4Gcm.X86.Init
public import VerifiedGarbage.Proof.Sm4Gcm.Scratch
public import VerifiedGarbage.Proof.Sm4Gcm.X86.Callee
public import VerifiedGarbage.Proof.Sm4Gcm.X86.Contract
import VerifiedGarbage.Proof.Sm4Gcm.X86.StreamEncrypt
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sm4.X86.Lit
import VerifiedGarbage.Proof.Sm4.X86.Ctr32Lit
import VerifiedGarbage.Proof.Sm4.X86.LayersLit
public import VerifiedGarbage.Proof.AesGcm.X86.Frame
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.X86.StackScratch

/-! ### `Sm4Gcm.X86.Verified`, which only this module used -/

section

/-!
# SM4-GCM on x86: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, a state satisfying each precondition, and the shared contracts of
`Spec/Sm4/Gcm/Contract.lean` with the working space as an argument
(`Proof/Sm4Gcm/Scratch.lean`): with 1536 bytes of stack for the functions
that call `vg_sm4_ctr32` (which pushes four arguments and the return
address, and keeps its working space below them). `stream_init` and
`stream_aad` are AES-GCM's (`Proof/AesGcm/X86/Verified.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

variable {vg : VG.Proof.AesGcm.X86.GcmImpl}

open VG VG.X86 VG.Impl.Sm4Gcm.X86 VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»

/-- A state satisfying the precondition of `vg_sm4_gcm_stream_encrypt` and
`_decrypt` (with no data): the context at `0x1000`, the state at `0x3000`,
the data at `0x2000` and `scratch` at `0x4000`. -/
def crSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x30
    else if a = 0x801d then 0x20 else if a = 0x8025 then 0x40 else 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 36⟩]

theorem streamEncrypt_verified : Verified X86.target (streamEncrypt vg.callees) (Proof.Sm4Gcm.streamEncryptScratchContract X86.abi 1536) :=
  Verified.of_correct streamEncrypt_correct streamEncrypt_ct (by
    have a0 : arg crSat 0 = 0x1000 := by decide
    have a1 : arg crSat 1 = 0x3000 := by decide
    have a2 : arg crSat 2 = 0 := by decide
    have a3 : arg crSat 3 = 0 := by decide
    have a4 : arg crSat 4 = 0 := by decide
    have a5 : arg crSat 5 = 0 := by decide
    have a6 : arg crSat 6 = 0x2000 := by decide
    have a7 : arg crSat 7 = 0 := by decide
    have a8 : arg crSat 8 = 0x4000 := by decide
    have e : argAddr crSat 0 = 0x8004 := by decide
    have esp : crSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.Sm4Gcm.streamEncryptScratchContract, Proof.Sm4Gcm.streamCryptScratchSig, Spec.Sm4.Gcm.streamEncryptPost, Spec.Sm4.Gcm.streamDecryptPost, streamEncryptX86, streamCryptPre, pubN,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, e, esp] using crSat)

theorem streamDecrypt_verified : Verified X86.target (streamDecrypt vg.callees) (Proof.Sm4Gcm.streamDecryptScratchContract X86.abi 1536) :=
  Verified.of_correct streamDecrypt_correct streamDecrypt_ct (by
    have a0 : arg crSat 0 = 0x1000 := by decide
    have a1 : arg crSat 1 = 0x3000 := by decide
    have a2 : arg crSat 2 = 0 := by decide
    have a3 : arg crSat 3 = 0 := by decide
    have a4 : arg crSat 4 = 0 := by decide
    have a5 : arg crSat 5 = 0 := by decide
    have a6 : arg crSat 6 = 0x2000 := by decide
    have a7 : arg crSat 7 = 0 := by decide
    have a8 : arg crSat 8 = 0x4000 := by decide
    have e : argAddr crSat 0 = 0x8004 := by decide
    have esp : crSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.Sm4Gcm.streamDecryptScratchContract, Proof.Sm4Gcm.streamCryptScratchSig, Spec.Sm4.Gcm.streamEncryptPost, Spec.Sm4.Gcm.streamDecryptPost, streamDecryptX86, streamCryptPre, pubN,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, e, esp] using crSat)

/-- A state satisfying `vg_sm4_gcm_stream_finish`'s precondition: the
context at `0x1000`, the state at `0x3000`, the tag at `0x5000` and `work`
at `0x4000`. -/
def finSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x30
    else if a = 0x801d then 0x50 else if a = 0x8021 then 0x40 else 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 32⟩]

theorem streamFinish_verified :
    Verified X86.target (streamFinish vg.callees) (Proof.Sm4Gcm.streamFinishScratchContract X86.abi 1536) :=
  Verified.of_correct streamFinish_correct streamFinish_ct (by
    have a0 : arg finSat 0 = 0x1000 := by decide
    have a1 : arg finSat 1 = 0x3000 := by decide
    have a2 : arg finSat 2 = 0 := by decide
    have a3 : arg finSat 3 = 0 := by decide
    have a4 : arg finSat 4 = 0 := by decide
    have a5 : arg finSat 5 = 0 := by decide
    have a6 : arg finSat 6 = 0x5000 := by decide
    have a7 : arg finSat 7 = 0x4000 := by decide
    have e : argAddr finSat 0 = 0x8004 := by decide
    have esp : finSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.Sm4Gcm.streamFinishScratchContract, Proof.Sm4Gcm.streamFinishScratchSig,
      Spec.Sm4.Gcm.streamFinishPost, streamFinishX86, finPre, pubN,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, e, esp] using finSat)

/-- A state satisfying `vg_sm4_gcm_stream_verify`'s precondition: as
`finSat`, with a received tag of no bytes at `0x5000`. -/
def verSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x30
    else if a = 0x801d then 0x50 else if a = 0x8025 then 0x40 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 36⟩]

theorem streamVerify_verified :
    Verified X86.target (streamVerify vg.callees) (Proof.Sm4Gcm.streamVerifyScratchContract X86.abi 1536) :=
  Verified.of_correct streamVerify_correct streamVerify_ct (by
    have a0 : arg verSat 0 = 0x1000 := by decide
    have a1 : arg verSat 1 = 0x3000 := by decide
    have a2 : arg verSat 2 = 0 := by decide
    have a3 : arg verSat 3 = 0 := by decide
    have a4 : arg verSat 4 = 0 := by decide
    have a5 : arg verSat 5 = 0 := by decide
    have a6 : arg verSat 6 = 0x5000 := by decide
    have a7 : arg verSat 7 = 0 := by decide
    have a8 : arg verSat 8 = 0x4000 := by decide
    have e : argAddr verSat 0 = 0x8004 := by decide
    have esp : verSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.Sm4Gcm.streamVerifyScratchContract, Proof.Sm4Gcm.streamVerifyScratchSig,
      Spec.Sm4.Gcm.streamVerifyPost, streamVerifyX86, verifyPre, pubN,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, e, esp] using verSat)

/-- A state satisfying `vg_sm4_gcm_seal`'s precondition (with no nonce,
additional data or data): the context at `0x1000`, the nonce at `0x2000`,
the additional data at `0x2100`, the data at `0x3000`, the tag at `0x5000`
and `work` at `0x4000`. -/
def sealSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20
    else if a = 0x8011 then 0x21 else if a = 0x8019 then 0x30 else if a = 0x8021 then 0x50
    else if a = 0x8025 then 0x40 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 36⟩]

theorem seal_verified : Verified X86.target («seal» vg.callees) (Proof.Sm4Gcm.sealScratchContract X86.abi 1536) :=
  Verified.of_correct seal_correct seal_ct (by
    have a0 : arg sealSat 0 = 0x1000 := by decide
    have a1 : arg sealSat 1 = 0x2000 := by decide
    have a2 : arg sealSat 2 = 0 := by decide
    have a3 : arg sealSat 3 = 0x2100 := by decide
    have a4 : arg sealSat 4 = 0 := by decide
    have a5 : arg sealSat 5 = 0x3000 := by decide
    have a6 : arg sealSat 6 = 0 := by decide
    have a7 : arg sealSat 7 = 0x5000 := by decide
    have a8 : arg sealSat 8 = 0x4000 := by decide
    have e : argAddr sealSat 0 = 0x8004 := by decide
    have esp : sealSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.Sm4Gcm.sealScratchContract, Proof.Sm4Gcm.sealScratchSig,
      Spec.Sm4.Gcm.sealPost, sealX86, sealPre, pubN,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, e, esp] using sealSat)

/-- A state satisfying `vg_sm4_gcm_open`'s precondition: as `sealSat`, with
a received tag of no bytes at `0x5000`. -/
def openSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20
    else if a = 0x8011 then 0x21 else if a = 0x8019 then 0x30 else if a = 0x8021 then 0x50
    else if a = 0x8029 then 0x40 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 40⟩]

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : ([if a = true then 1 else 0] : List Nat) = [if b = true then 1 else 0]) :
    a = b := by
  cases a <;> cases b <;> simp_all

theorem open_pre : ∀ s, (Proof.Sm4Gcm.openScratchContract X86.abi 1536).pre s → openX86.pre s := by
  sig_implies_pre [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
    Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, openX86, openPre, pubN,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

/-- `open`'s public data include its leak, whether it succeeds. -/
theorem open_verified : Verified X86.target («open» vg.callees) (Proof.Sm4Gcm.openScratchContract X86.abi 1536) :=
  Verified.of_correct open_correct open_ct
    { pre := open_pre
      post := by sig_implies_post [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
        Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, openX86, openPre, pubN,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      pub := by
        intro s₁ s₂ h₁ h₂ h
        sig_pub [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
          Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, openX86, openPre, pubN,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
        sig_split h
        sig_reduce [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
          Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, openX86, openPre, pubN,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
        sig_simp [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
          Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, openX86, openPre, pubN,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [Nat.forall_lt_succ_right, Nat.not_lt_zero,
          false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | (apply leak_bool; with_reducible assumption)
      sat := by
        have a0 : arg openSat 0 = 0x1000 := by decide
        have a1 : arg openSat 1 = 0x2000 := by decide
        have a2 : arg openSat 2 = 0 := by decide
        have a3 : arg openSat 3 = 0x2100 := by decide
        have a4 : arg openSat 4 = 0 := by decide
        have a5 : arg openSat 5 = 0x3000 := by decide
        have a6 : arg openSat 6 = 0 := by decide
        have a7 : arg openSat 7 = 0x5000 := by decide
        have a8 : arg openSat 8 = 0 := by decide
        have a9 : arg openSat 9 = 0x4000 := by decide
        have e : argAddr openSat 0 = 0x8004 := by decide
        have esp : openSat.gpr .esp = 0x8000 := rfl
        sig_implies_sat [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
          Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, openX86, openPre, pubN,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
          [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, e, esp] using openSat }

/-- A state satisfying `vg_sm4_gcm_init`'s precondition: the key at
`0x1000`, the context at `0x2000` and `scratch` at `0x4000`. -/
def initSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 12⟩]

theorem init_verified : Verified X86.target init (Proof.Sm4Gcm.initScratchContract X86.abi 1536) :=
  Verified.of_correct init_correct init_ct (by
    have a0 : arg initSat 0 = 0x1000 := by decide
    have a1 : arg initSat 1 = 0x2000 := by decide
    have a2 : arg initSat 2 = 0x4000 := by decide
    have e : argAddr initSat 0 = 0x8004 := by decide
    have esp : initSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.Sm4Gcm.initScratchContract, Proof.Sm4Gcm.initScratchSig, Spec.Sm4.Gcm.initPost, initX86, initPre, pubN,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, e, esp] using initSat)

/-! ## The stack pointer -/

section
variable (vg : GcmImpl)

theorem init_spSafe : init.all (fun i => !X86.isa.writesSp i) = true := by
  simp only [init, keyCall, ctrCall, entry, Code.all, ctr_spSafe, key_spSafe,
    Bool.true_and, Bool.and_true]
  lit_decide

theorem streamEncrypt_spSafe : (streamEncrypt vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, firstFlush, flush, ghCall,
    ghash1, textAbsorb, streamEncrypt, Code.all, GcmImpl.callees, ctr_spSafe, vg.gh.spSafe, Bool.true_and,
    Bool.and_true]
  lit_decide

theorem streamDecrypt_spSafe : (streamDecrypt vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, firstFlush, flush, ghCall,
    ghash1, textAbsorb, streamDecrypt, Code.all, GcmImpl.callees, ctr_spSafe, vg.gh.spSafe, Bool.true_and,
    Bool.and_true]
  lit_decide

theorem streamFinish_spSafe : (streamFinish vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [ctrCall, finTag, flush, ghCall, ghash1, lens, tag, tagOut, streamFinish, Code.all, GcmImpl.callees,
    ctr_spSafe, vg.gh.spSafe, Bool.true_and, Bool.and_true]
  lit_decide

theorem streamVerify_spSafe : (streamVerify vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [ctrCall, finTag, flush, ghCall, ghash1, lens, tag, streamVerify, Code.all, GcmImpl.callees,
    ctr_spSafe, vg.gh.spSafe, Bool.true_and, Bool.and_true]
  lit_decide

theorem seal_spSafe : («seal» vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, flush, ghCall, ghash1, j0,
    j0hash, lens, oneAad, oneCrypt, oneTag, tag, tagOut, «seal», Code.all, GcmImpl.callees, ctr_spSafe,
    vg.gh.spSafe, Bool.true_and, Bool.and_true]
  lit_decide

theorem open_spSafe : («open» vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, flush, ghCall, ghash1, j0,
    j0hash, lens, oneAad, oneCrypt, oneTag, tag, «open», Code.all, GcmImpl.callees, ctr_spSafe, vg.gh.spSafe,
    Bool.true_and, Bool.and_true]
  lit_decide

end

end VG.Proof.Sm4Gcm.X86

end

end


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
