module

import VerifiedGarbage.Proof.Sm4Gcm.Arm.InitCT
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTStream
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTCryptFn
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTOpen
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.Scratch
public import VerifiedGarbage.Impl.Sm4Gcm.Arm
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Contract
import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamFinish
import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamInit
import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamVerify
import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamAad
import VerifiedGarbage.Proof.Sm4Gcm.Arm.Seal
import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamCrypt

/-!
# SM4-GCM on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, a state satisfying each precondition, and the shared contracts of
`Spec/Sm4/Gcm/Contract.lean` with the working space as a last argument
(`Proof/Sm4Gcm/Scratch.lean`), with 1520 bytes of stack: those of
`vg_sm4_ctr32`'s frame, the most any call uses (`vg_sm4_expand_key` uses
1456, and each call of `vg_ghash` pushes two words).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Impl.Sm4Gcm.Arm

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

/-- A state satisfying `vg_sm4_gcm_init`'s precondition. -/
def initSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 16⟩] [⟨0x2000, 144⟩, ⟨0x3000, 768⟩]

theorem init_verified : Verified Arm.target init (Proof.Sm4Gcm.initScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => init_wp hs) init_ct (by
    sig_implies [Proof.Sm4Gcm.initScratchContract, Proof.Sm4Gcm.initScratchSig, Spec.Sm4.Gcm.initSig,
      Spec.Sm4.Gcm.initPost, initArm, bel, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [initSat, mkSat] using initSat)

/-- A state satisfying `vg_sm4_gcm_stream_init`'s precondition (with no nonce). -/
def siSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 144⟩, ⟨0x2000, 0⟩, ⟨0x8000, 4⟩] [⟨0x3000, 80⟩, ⟨0, 768⟩]

theorem streamInit_verified :
    Verified Arm.target streamInit (Proof.Sm4Gcm.streamInitScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => streamInit_wp hs) streamInit_ct (by
    sig_implies [Proof.Sm4Gcm.streamInitScratchContract, Proof.Sm4Gcm.streamInitScratchSig,
      Spec.Sm4.Gcm.streamInitSig, Spec.Sm4.Gcm.streamInitPost, streamInitArm, bel, arg, args, arg64,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [siSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using siSat)

/-- A state satisfying `vg_sm4_gcm_stream_aad`'s precondition (with no data). -/
def saSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 144⟩, ⟨0, 0⟩, ⟨0x8000, 12⟩] [⟨0x3000, 80⟩, ⟨0, 768⟩]

theorem streamAad_verified :
    Verified Arm.target streamAad (Proof.Sm4Gcm.streamAadScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => streamAad_wp hs) streamAad_ct (by
    sig_implies [Proof.Sm4Gcm.streamAadScratchContract, Proof.Sm4Gcm.streamAadScratchSig,
      Spec.Sm4.Gcm.streamAadSig, Spec.Sm4.Gcm.streamAadPost, streamAadArm, bel, arg, args, arg64,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [saSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using saSat)

/-- A state satisfying the precondition of `vg_sm4_gcm_stream_encrypt` and `_decrypt` (with no
data, and `scratch` at 0). -/
def scSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 144⟩, ⟨0x8000, 20⟩] [⟨0x3000, 80⟩, ⟨0, 0⟩, ⟨0, 768⟩]

theorem streamEncrypt_verified :
    Verified Arm.target streamEncrypt (Proof.Sm4Gcm.streamEncryptScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => streamEncrypt_wp hs) streamEncrypt_ct (by
    sig_implies [Proof.Sm4Gcm.streamEncryptScratchContract, Proof.Sm4Gcm.streamCryptScratchSig,
      Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamEncryptPost, streamEncryptArm, streamCryptPre,
      streamCryptPub, bel, arg, args, arg64, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
      [scSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using scSat)

theorem streamDecrypt_verified :
    Verified Arm.target streamDecrypt (Proof.Sm4Gcm.streamDecryptScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => streamDecrypt_wp hs) streamDecrypt_ct (by
    sig_implies [Proof.Sm4Gcm.streamDecryptScratchContract, Proof.Sm4Gcm.streamCryptScratchSig,
      Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamDecryptPost, streamDecryptArm, streamCryptPre,
      streamCryptPub, bel, arg, args, arg64, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
      [scSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using scSat)

/-- `mkSat`, with the stack argument 2 (at `0x8008`) `0x4000`. -/
def mkSat2 (g : Reg → BitVec 32) (rd wr : List Region) : State :=
  { mkSat g rd wr with mem := fun a => if a = 0x8009 then 0x40 else 0 }

/-- `mkSat`, with the stack argument 3 (at `0x800c`) `0x4000`. -/
def mkSat3 (g : Reg → BitVec 32) (rd wr : List Region) : State :=
  { mkSat g rd wr with mem := fun a => if a = 0x800D then 0x40 else 0 }

/-- A state satisfying `vg_sm4_gcm_stream_finish`'s precondition (with `tag` at `0x4000` and `work`
at 0). -/
def fSat : State :=
  mkSat2 (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 144⟩, ⟨0x8000, 16⟩] [⟨0x3000, 80⟩, ⟨0x4000, 16⟩, ⟨0, 768⟩]

theorem streamFinish_verified :
    Verified Arm.target streamFinish (Proof.Sm4Gcm.streamFinishScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => streamFinish_wp hs) streamFinish_ct (by
    sig_implies [Proof.Sm4Gcm.streamFinishScratchContract, Proof.Sm4Gcm.streamFinishScratchSig,
      Spec.Sm4.Gcm.streamFinishSig, Spec.Sm4.Gcm.streamFinishPost, streamFinishArm, streamFinishPreArm,
      finPub, bel, arg, args, arg64, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [fSat, mkSat2, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using fSat)

/-- A state satisfying `vg_sm4_gcm_stream_verify`'s precondition (with no tag, and `work` at 0). -/
def vSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 144⟩, ⟨0, 0⟩, ⟨0x8000, 20⟩] [⟨0x3000, 80⟩, ⟨0, 768⟩]

/-- The postconditions match; the result is the low word of `r1:r0`. -/
theorem streamVerify_verified :
    Verified Arm.target streamVerify (Proof.Sm4Gcm.streamVerifyScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => streamVerify_wp hs) streamVerify_ct
    { pre := by
        sig_implies_pre [Proof.Sm4Gcm.streamVerifyScratchContract, Proof.Sm4Gcm.streamVerifyScratchSig,
          Spec.Sm4.Gcm.streamVerifySig, streamVerifyArm, streamVerifyPreArm, finPub, bel, arg, args,
          arg64, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.Sm4Gcm.streamVerifyScratchContract, Proof.Sm4Gcm.streamVerifyScratchSig,
          Spec.Sm4.Gcm.streamVerifySig, Spec.Sm4.Gcm.streamVerifyPost, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [streamVerifyArm, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        intro iv a c hs ha hc
        rw [e]
        exact h iv a c hs ha hc
      pub := by
        sig_implies_pub [Proof.Sm4Gcm.streamVerifyScratchContract, Proof.Sm4Gcm.streamVerifyScratchSig,
          Spec.Sm4.Gcm.streamVerifySig, streamVerifyArm, streamVerifyPreArm, finPub, bel, arg, args,
          arg64, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by
        sig_implies_sat [Proof.Sm4Gcm.streamVerifyScratchContract, Proof.Sm4Gcm.streamVerifyScratchSig,
          Spec.Sm4.Gcm.streamVerifySig, streamVerifyArm, streamVerifyPreArm, finPub, bel, arg, args,
          arg64, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [vSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using vSat }

/-- A state satisfying `vg_sm4_gcm_seal`'s precondition (with no nonce, additional data or
data, `tag` at `0x4000` and `work` at 0). -/
def oSat : State :=
  mkSat3 (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0)
    [⟨0x1000, 144⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 20⟩] [⟨0, 0⟩, ⟨0x4000, 16⟩, ⟨0, 768⟩]

theorem seal_verified : Verified Arm.target «seal» (Proof.Sm4Gcm.sealScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => seal_wp hs) seal_ct (by
    sig_implies [Proof.Sm4Gcm.sealScratchContract, Proof.Sm4Gcm.sealScratchSig, Spec.Sm4.Gcm.sealSig,
      Spec.Sm4.Gcm.sealPost, sealArm, sealPreArm, onePub, bel, arg, args, arg64, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [oSat, mkSat3, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using oSat)

/-- A state satisfying `vg_sm4_gcm_open`'s precondition (with no nonce, additional data, data
or tag, and `work` at 0). -/
def opSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0)
    [⟨0x1000, 144⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩] [⟨0, 0⟩, ⟨0, 768⟩]

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The postconditions match on `openResult`; the result is the low word of
`r1:r0`; and `open`'s public data include its leak, whether it succeeds. -/
theorem open_verified : Verified Arm.target «open» (Proof.Sm4Gcm.openScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => open_wp hs) open_ct
    { pre := by
        sig_implies_pre [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
          Spec.Sm4.Gcm.openSig, openArm, openPreArm, onePub, bel, arg, args, arg64, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig, Spec.Sm4.Gcm.openSig,
          Spec.Sm4.Gcm.openPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [openArm, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        rw [e]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig, Spec.Sm4.Gcm.openSig,
          Spec.Sm4.Gcm.openLeak, openArm, openPreArm, onePub, bel, arg, args, arg64, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5⟩ := h
        refine ⟨⟨hsp, h0, h1, h2, h3, fun i hi => ?_⟩, leak_bool hl⟩
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl
        · exact a0
        · exact a1
        · exact a2
        · exact a3
        · exact a4
        · exact a5
      sat := by
        sig_implies_sat [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
          Spec.Sm4.Gcm.openSig, openArm, openPreArm, onePub, bel, arg, args, arg64, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [opSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using opSat }

end VG.Proof.Sm4Gcm.Arm
