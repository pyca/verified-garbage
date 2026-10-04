import VerifiedGarbage.Proof.AesGcm.Arm.InitCT
import VerifiedGarbage.Proof.AesGcm.Arm.CTStream
import VerifiedGarbage.Proof.AesGcm.Arm.CTCryptFn
import VerifiedGarbage.Proof.AesGcm.Arm.CTOpen
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.AesGcm.Scratch

/-!
# AES-GCM on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, a state satisfying each precondition, and the shared contracts of
`Spec/Gcm/Contract.lean` with the working space as a last argument
(`Proof/AesGcm/Scratch.lean`), with 8 bytes of stack: each call of
`vg_aes_ctr32` or `vg_ghash` pushes two words.
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm

/-- A state with the given registers, the stack pointer at `0x8000`, memory
of zeros (so stack arguments of 0) and the given regions. -/
def mkSat (g : Reg → BitVec 32) (rd wr : List Region) : State where
  gpr := g
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := rd
  wr := wr

/-- A state satisfying `vg_aes_gcm_init`'s precondition. -/
def initSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 16 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 16⟩] [⟨0x2000, 256⟩, ⟨0x3000, 2560⟩]

theorem init_verified : Verified Arm.target init (Proof.AesGcm.initScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => init_wp hs) init_ct (by
    sig_implies [Proof.AesGcm.initScratchContract, Proof.AesGcm.initScratchSig, Spec.Gcm.initPre, Spec.Gcm.initPost, initArm, bel, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [initSat, mkSat] using initSat)

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition (with no nonce). -/
def siSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x8000, 4⟩] [⟨0x3000, 80⟩, ⟨0, 2560⟩]

theorem streamInit_verified :
    Verified Arm.target streamInit (Proof.AesGcm.streamInitScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => streamInit_wp hs) streamInit_ct (by
    sig_implies [Proof.AesGcm.streamInitScratchContract, Proof.AesGcm.streamInitScratchSig, Spec.Gcm.streamInitPost, streamInitArm, bel, arg, args, arg64,
      roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [siSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using siSat)

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition (with no data). -/
def saSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0x8000, 12⟩] [⟨0x3000, 80⟩, ⟨0, 2560⟩]

theorem streamAad_verified :
    Verified Arm.target streamAad (Proof.AesGcm.streamAadScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => streamAad_wp hs) streamAad_ct (by
    sig_implies [Proof.AesGcm.streamAadScratchContract, Proof.AesGcm.streamAadScratchSig, Spec.Gcm.streamAadPost, streamAadArm, bel, arg, args, arg64,
      roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [saSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using saSat)

/-- A state satisfying the precondition of `vg_aes_gcm_stream_encrypt` and `_decrypt` (with no
data, and `scratch` at 0). -/
def scSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 28⟩] [⟨0x3000, 80⟩, ⟨0, 0⟩, ⟨0, 2560⟩]

theorem streamEncrypt_verified :
    Verified Arm.target streamEncrypt (Proof.AesGcm.streamEncryptScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => streamEncrypt_wp hs) streamEncrypt_ct (by
    sig_implies [Proof.AesGcm.streamEncryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Spec.Gcm.streamEncryptPost, Spec.Gcm.streamDecryptPost, streamEncryptArm, streamCryptPre,
      streamCryptPub, bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
      [scSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using scSat)

theorem streamDecrypt_verified :
    Verified Arm.target streamDecrypt (Proof.AesGcm.streamDecryptScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => streamDecrypt_wp hs) streamDecrypt_ct (by
    sig_implies [Proof.AesGcm.streamDecryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Spec.Gcm.streamEncryptPost, Spec.Gcm.streamDecryptPost, streamDecryptArm, streamCryptPre,
      streamCryptPub, bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
      [scSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using scSat)

/-- `mkSat`, with the stack argument 4 (at `0x8010`) `0x4000`. -/
def mkSat4 (g : Reg → BitVec 32) (rd wr : List Region) : State :=
  { mkSat g rd wr with mem := fun a => if a = 0x8011 then 0x40 else 0 }

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition (with `tag` at `0x4000` and `work`
at 0). -/
def fSat : State :=
  mkSat4 (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 24⟩] [⟨0x3000, 80⟩, ⟨0x4000, 16⟩, ⟨0, 2560⟩]

theorem streamFinish_verified :
    Verified Arm.target streamFinish (Proof.AesGcm.streamFinishScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => streamFinish_wp hs) streamFinish_ct (by
    sig_implies [Proof.AesGcm.streamFinishScratchContract, Proof.AesGcm.streamFinishScratchSig,
      Spec.Gcm.streamFinishPre, Spec.Gcm.streamFinishPost, streamFinishArm, streamFinishPreArm, finPub, bel, arg,
      args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [fSat, mkSat4, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using fSat)

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition (with no tag, and `work` at 0). -/
def vSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0x8000, 28⟩] [⟨0x3000, 80⟩, ⟨0, 2560⟩]

/-- The postconditions match; the result is the low word of `r1:r0`. -/
theorem streamVerify_verified :
    Verified Arm.target streamVerify (Proof.AesGcm.streamVerifyScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => streamVerify_wp hs) streamVerify_ct
    { pre := by
        sig_implies_pre [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
          Spec.Gcm.streamVerifyPre, streamVerifyArm, streamVerifyPreArm, finPub, bel, arg, args, arg64, roundsOk,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
          Spec.Gcm.streamVerifyPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [streamVerifyArm, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        intro _ iv a c hs ha hc
        rw [e]
        exact h iv a c hs ha hc
      pub := by
        sig_implies_pub [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
          streamVerifyArm, streamVerifyPreArm, finPub, bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by
        sig_implies_sat [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
          Spec.Gcm.streamVerifyPre, streamVerifyArm, streamVerifyPreArm, finPub, bel, arg, args, arg64, roundsOk,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [vSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using vSat }

/-- A state satisfying `vg_aes_gcm_seal`'s precondition (with no nonce, additional data or
data, `tag` at `0x4000` and `work` at 0). -/
def oSat : State :=
  mkSat4 (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩] [⟨0, 0⟩, ⟨0x4000, 16⟩, ⟨0, 2560⟩]

theorem seal_verified : Verified Arm.target «seal» (Proof.AesGcm.sealScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => seal_wp hs) seal_ct (by
    sig_implies [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre,
      Spec.Gcm.sealPost, sealArm, sealPreArm, onePub, bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [oSat, mkSat4, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using oSat)

/-- A state satisfying `vg_aes_gcm_open`'s precondition (with no nonce, additional data, data
or tag, and `work` at 0). -/
def opSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x8000, 28⟩] [⟨0, 0⟩, ⟨0, 2560⟩]

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The postconditions match on `openResult`; the result is the low word of
`r1:r0`; and `open`'s public data include its leak, whether it succeeds (for
`rounds` of 10, 12 or 14). -/
theorem open_verified : Verified Arm.target «open» (Proof.AesGcm.openScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => open_wp hs) open_ct
    { pre := by
        sig_implies_pre [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre, openArm,
          openPreArm, onePub, bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify,
          Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPost, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [openArm, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        intro _
        rw [e]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openLeak, openArm,
          openPreArm, onePub, bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify,
          Arm.Loc.val, Arm.State.addr] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6⟩ := h
        refine ⟨⟨hsp, h0, h1, h2, h3, fun i hi => ?_⟩, fun hr => leak_bool ?_⟩
        · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact a0
          · exact a1
          · exact a2
          · exact a3
          · exact a4
          · exact a5
          · exact a6
        · have e₁ : ¬((s₁.gpr .r1).toNat = 10 ∨ (s₁.gpr .r1).toNat = 12 ∨ (s₁.gpr .r1).toNat = 14) ↔ False :=
            ⟨fun x => x hr, False.elim⟩
          have e₂ : ¬((s₂.gpr .r1).toNat = 10 ∨ (s₂.gpr .r1).toNat = 12 ∨ (s₂.gpr .r1).toNat = 14) ↔ False :=
            ⟨fun x => x (h1 ▸ hr), False.elim⟩
          simp only [e₁, e₂, ↓reduceIte] at hl
          exact hl
      sat := by
        sig_implies_sat [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre, openArm,
          openPreArm, onePub, bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify,
          Arm.Loc.val, Arm.State.addr]
          [opSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using opSat }

end VG.Proof.AesGcm.Arm
