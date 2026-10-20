module

public import VerifiedGarbage.Proof.Blowfish.Arm.ModeCore
public import VerifiedGarbage.Proof.Blowfish.FbScratch
public import VerifiedGarbage.Proof.Modes.Arm.SeqCT
public import VerifiedGarbage.Spec.Blowfish.Cfb
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Blowfish.Arm.Run
meta import VerifiedGarbage.Proof.Blowfish.Arm.ModeCore
meta import VerifiedGarbage.Proof.Blowfish.FbScratch
meta import VerifiedGarbage.Proof.Modes.Arm.SeqCT
meta import VerifiedGarbage.Spec.Blowfish.Cfb
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Blowfish.Arm.Run
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe

/-!
# Blowfish-OFB and Blowfish-CFB128 on ARMv7 meet their contracts

The generic OFB and CFB one block at a time over Blowfish's ECB encryption
(`Proof.Modes.Arm.seq_verified` with `ecbSpec true`) meet the contracts
with a scratch buffer of 7 words (`Proof.Blowfish.fbScratchContract`), with the
256 bytes of stack the ECB function uses; the `_framed` theorems keep the
buffer on the stack, zeroed on return: 64 bytes more.
-/

@[expose] public section

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Impl.Blowfish.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

/-- A state satisfying the precondition with the scratch buffer (one block at
`0x5000`), the IV read and written. -/
def fbSat (len : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x4000 | .r2 => 0x5000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 4168⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x4000, 8⟩, ⟨0x5000, len⟩, ⟨0, 56⟩]

/-- A state satisfying the functions' precondition. -/
def fbFrameSat (len : Nat) : State := { fbSat len with rd := [⟨0x1000, 4168⟩], wr := [⟨0x4000, 8⟩, ⟨0x5000, len⟩] }

theorem ofbTaint : SeqTaint (ecbCore true) VG.Impl.Modes.Arm.ofb :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem ofb_implies : (seqArm (ecbCore true) (ecbSpec true) VG.Impl.Modes.Arm.ofb).Implies
    (Proof.Blowfish.fbScratchContract Arm.abi 7 Proof.Blowfish.ofbPost 256) where
  pre s h := seqArm_pre_rw rfl (len := (· * 8)) (fun n => rfl) (by
    sig_pre [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Proof.Blowfish.ofbPost, Spec.Blowfish.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := ofb_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore true) rfl s
    simp only [show (ecbCore true).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, blocksOf_eq, ↓reduceIte] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 8

theorem ofb_verified : Verified Arm.target ofb (Proof.Blowfish.fbScratchContract Arm.abi 7 Proof.Blowfish.ofbPost 256) :=
  seq_verified (ecbSpec true) (ofb_ok _) ofbTaint ofb_implies

theorem ofbFrameSat : ∃ s, (Spec.Blowfish.ofbContract Arm.abi 320).pre s := by
  implies_sat [Spec.Blowfish.ofbContract, Spec.Blowfish.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 8

/-- `ofb`, with its scratch buffer on the stack (zeroed on return). -/
theorem ofb_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 ofb) (Spec.Blowfish.ofbContract Arm.abi 320) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Blowfish.ofbSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.Blowfish.ofbPost Arm.abi.ptrBits) (wa := true) (stack := 256) (m := 0) (bytes := 64)
    ofb_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Blowfish.ofbPost_local _)
    (Proof.Blowfish.ofbPostOut_local _) ofbFrameSat

theorem cfbEncryptTaint : SeqTaint (ecbCore true) cfbEnc :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cfbEncrypt_implies : (seqArm (ecbCore true) (ecbSpec true) cfbEnc).Implies
    (Proof.Blowfish.fbScratchContract Arm.abi 7 Proof.Blowfish.cfbEncPost 256) where
  pre s h := seqArm_pre_rw rfl (len := (· * 8)) (fun n => rfl) (by
    sig_pre [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Proof.Blowfish.cfbEncPost, Spec.Blowfish.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbEnc_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore true) rfl s
    simp only [show (ecbCore true).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, blocksOf_eq, ↓reduceIte] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 8

theorem cfbEncrypt_verified : Verified Arm.target cfbEncrypt (Proof.Blowfish.fbScratchContract Arm.abi 7 Proof.Blowfish.cfbEncPost 256) :=
  seq_verified (ecbSpec true) (cfbEnc_ok _) cfbEncryptTaint cfbEncrypt_implies

theorem cfbEncryptFrameSat : ∃ s, (Spec.Blowfish.cfbEncryptContract Arm.abi 320).pre s := by
  implies_sat [Spec.Blowfish.cfbEncryptContract, Spec.Blowfish.cfbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 8

/-- `cfbEncrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbEncrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cfbEncrypt) (Spec.Blowfish.cfbEncryptContract Arm.abi 320) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.Blowfish.cfbEncPost Arm.abi.ptrBits) (wa := true) (stack := 256) (m := 0) (bytes := 64)
    cfbEncrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Blowfish.cfbEncPost_local _)
    (Proof.Blowfish.cfbEncPostOut_local _) cfbEncryptFrameSat

theorem cfbDecryptTaint : SeqTaint (ecbCore true) cfbDec :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cfbDecrypt_implies : (seqArm (ecbCore true) (ecbSpec true) cfbDec).Implies
    (Proof.Blowfish.fbScratchContract Arm.abi 7 Proof.Blowfish.cfbDecPost 256) where
  pre s h := seqArm_pre_rw rfl (len := (· * 8)) (fun n => rfl) (by
    sig_pre [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Proof.Blowfish.cfbDecPost, Spec.Blowfish.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbDec_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore true) rfl s
    simp only [show (ecbCore true).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, blocksOf_eq, ↓reduceIte] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 8

theorem cfbDecrypt_verified : Verified Arm.target cfbDecrypt (Proof.Blowfish.fbScratchContract Arm.abi 7 Proof.Blowfish.cfbDecPost 256) :=
  seq_verified (ecbSpec true) (cfbDec_ok _) cfbDecryptTaint cfbDecrypt_implies

theorem cfbDecryptFrameSat : ∃ s, (Spec.Blowfish.cfbDecryptContract Arm.abi 320).pre s := by
  implies_sat [Spec.Blowfish.cfbDecryptContract, Spec.Blowfish.cfbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 8

/-- `cfbDecrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cfbDecrypt) (Spec.Blowfish.cfbDecryptContract Arm.abi 320) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.Blowfish.cfbDecPost Arm.abi.ptrBits) (wa := true) (stack := 256) (m := 0) (bytes := 64)
    cfbDecrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Blowfish.cfbDecPost_local _)
    (Proof.Blowfish.cfbDecPostOut_local _) cfbDecryptFrameSat

end VG.Proof.Blowfish.Arm
