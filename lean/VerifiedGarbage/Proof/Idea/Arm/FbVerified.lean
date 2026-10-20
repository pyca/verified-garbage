module

public import VerifiedGarbage.Proof.Idea.Arm.ModeCore
public import VerifiedGarbage.Proof.Idea.FbScratch
public import VerifiedGarbage.Proof.Modes.Arm.SeqCT
public import VerifiedGarbage.Spec.Idea.Cfb
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Idea.Arm.ModeCore
meta import VerifiedGarbage.Proof.Idea.FbScratch
meta import VerifiedGarbage.Proof.Modes.Arm.SeqCT
meta import VerifiedGarbage.Spec.Idea.Cfb
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# IDEA-OFB and IDEA-CFB64 on ARMv7 meet their contracts

The generic OFB and CFB one block at a time over IDEA's ECB function
(`Proof.Modes.Arm.seq_verified` with `ecbSpec`) meet the contracts
with a scratch buffer of 7 words (`Proof.Idea.fbScratchContract`), with the
32 bytes of stack the ECB function uses; the `_framed` theorems keep the
buffer on the stack, zeroed on return: 64 bytes more.
-/

@[expose] public section

namespace VG.Proof.Idea.Arm

open VG VG.Arm VG.Impl.Idea.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

/-- A state satisfying the precondition with the scratch buffer (one block at
`0x3000`), the IV read and written. -/
def fbSat (len : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 104⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, len⟩, ⟨0, 56⟩]

/-- A state satisfying the functions' precondition. -/
def fbFrameSat (len : Nat) : State := { fbSat len with rd := [⟨0x1000, 104⟩], wr := [⟨0x2000, 8⟩, ⟨0x3000, len⟩] }

theorem ofbTaint : SeqTaint (ecbCore) VG.Impl.Modes.Arm.ofb :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem ofb_implies : (seqArm (ecbCore) (ecbSpec) VG.Impl.Modes.Arm.ofb).Implies
    (Proof.Idea.fbScratchContract Arm.abi 7 Proof.Idea.ofbPost 32) where
  pre s h := seqArm_pre_rw rfl (len := (· * 8)) (fun n => rfl) (by
    sig_pre [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Spec.Idea.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Proof.Idea.ofbPost, Spec.Idea.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := ofb_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore) rfl s
    simp only [show (ecbCore).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, State.addr, blocksOf_eq] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Spec.Idea.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Spec.Idea.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 8

theorem ofb_verified : Verified Arm.target ofb (Proof.Idea.fbScratchContract Arm.abi 7 Proof.Idea.ofbPost 32) :=
  seq_verified (ecbSpec) (ofb_ok _) ofbTaint ofb_implies

theorem ofbFrameSat : ∃ s, (Spec.Idea.ofbContract Arm.abi 96).pre s := by
  implies_sat [Spec.Idea.ofbContract, Spec.Idea.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 8

/-- `ofb`, with its scratch buffer on the stack (zeroed on return). -/
theorem ofb_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 ofb) (Spec.Idea.ofbContract Arm.abi 96) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Idea.ofbSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.Idea.ofbPost Arm.abi.ptrBits) (wa := true) (stack := 32) (m := 0) (bytes := 64)
    ofb_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Idea.ofbPost_local _)
    (Proof.Idea.ofbPostOut_local _) ofbFrameSat

theorem cfbEncryptTaint : SeqTaint (ecbCore) cfbEnc :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cfbEncrypt_implies : (seqArm (ecbCore) (ecbSpec) cfbEnc).Implies
    (Proof.Idea.fbScratchContract Arm.abi 7 Proof.Idea.cfbEncPost 32) where
  pre s h := seqArm_pre_rw rfl (len := (· * 8)) (fun n => rfl) (by
    sig_pre [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Spec.Idea.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Proof.Idea.cfbEncPost, Spec.Idea.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbEnc_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore) rfl s
    simp only [show (ecbCore).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, State.addr, blocksOf_eq] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Spec.Idea.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Spec.Idea.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 8

theorem cfbEncrypt_verified : Verified Arm.target cfbEncrypt (Proof.Idea.fbScratchContract Arm.abi 7 Proof.Idea.cfbEncPost 32) :=
  seq_verified (ecbSpec) (cfbEnc_ok _) cfbEncryptTaint cfbEncrypt_implies

theorem cfbEncryptFrameSat : ∃ s, (Spec.Idea.cfbEncryptContract Arm.abi 96).pre s := by
  implies_sat [Spec.Idea.cfbEncryptContract, Spec.Idea.cfbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 8

/-- `cfbEncrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbEncrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cfbEncrypt) (Spec.Idea.cfbEncryptContract Arm.abi 96) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Idea.cfbSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.Idea.cfbEncPost Arm.abi.ptrBits) (wa := true) (stack := 32) (m := 0) (bytes := 64)
    cfbEncrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Idea.cfbEncPost_local _)
    (Proof.Idea.cfbEncPostOut_local _) cfbEncryptFrameSat

theorem cfbDecryptTaint : SeqTaint (ecbCore) cfbDec :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cfbDecrypt_implies : (seqArm (ecbCore) (ecbSpec) cfbDec).Implies
    (Proof.Idea.fbScratchContract Arm.abi 7 Proof.Idea.cfbDecPost 32) where
  pre s h := seqArm_pre_rw rfl (len := (· * 8)) (fun n => rfl) (by
    sig_pre [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Spec.Idea.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Proof.Idea.cfbDecPost, Spec.Idea.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbDec_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore) rfl s
    simp only [show (ecbCore).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, State.addr, blocksOf_eq] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Spec.Idea.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Spec.Idea.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 8

theorem cfbDecrypt_verified : Verified Arm.target cfbDecrypt (Proof.Idea.fbScratchContract Arm.abi 7 Proof.Idea.cfbDecPost 32) :=
  seq_verified (ecbSpec) (cfbDec_ok _) cfbDecryptTaint cfbDecrypt_implies

theorem cfbDecryptFrameSat : ∃ s, (Spec.Idea.cfbDecryptContract Arm.abi 96).pre s := by
  implies_sat [Spec.Idea.cfbDecryptContract, Spec.Idea.cfbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 8

/-- `cfbDecrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cfbDecrypt) (Spec.Idea.cfbDecryptContract Arm.abi 96) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Idea.cfbSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.Idea.cfbDecPost Arm.abi.ptrBits) (wa := true) (stack := 32) (m := 0) (bytes := 64)
    cfbDecrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Idea.cfbDecPost_local _)
    (Proof.Idea.cfbDecPostOut_local _) cfbDecryptFrameSat

end VG.Proof.Idea.Arm
