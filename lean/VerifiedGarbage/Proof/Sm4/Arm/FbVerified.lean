module

public import VerifiedGarbage.Proof.Sm4.Arm.ModeCore
public import VerifiedGarbage.Proof.Sm4.FbScratch
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
public import VerifiedGarbage.Impl.Sm4.Arm.Fb
public import VerifiedGarbage.Proof.Modes.Arm.SeqCT
public import VerifiedGarbage.Spec.Sm4.Cfb
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Sm4.Arm.ModeCore
meta import VerifiedGarbage.Proof.Sm4.FbScratch
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Impl.Sm4.Arm.Fb
meta import VerifiedGarbage.Proof.Modes.Arm.SeqCT
meta import VerifiedGarbage.Spec.Sm4.Cfb
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# SM4-OFB and SM4-CFB128 on ARMv7 meet their contracts

The generic OFB and CFB one block at a time over SM4's ECB encryption
(`Proof.Modes.Arm.seq_verified` with `ecbSpec .encrypt`) meet the contracts
with a scratch buffer of 9 words (`Proof.Sm4.fbScratchContract`), with the
1480 bytes of stack the ECB function uses; the `_framed` theorems keep the
buffer on the stack, zeroed on return: 80 bytes more.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Impl.Sm4.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

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
  rd := [⟨0x1000, 128⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, len⟩, ⟨0, 72⟩]

/-- A state satisfying the functions' precondition. -/
def fbFrameSat (len : Nat) : State := { fbSat len with rd := [⟨0x1000, 128⟩], wr := [⟨0x2000, 16⟩, ⟨0x3000, len⟩] }

theorem ofbTaint : SeqTaint (ecbCore .encrypt) VG.Impl.Modes.Arm.ofb :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem ofb_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) VG.Impl.Modes.Arm.ofb).Implies
    (Proof.Sm4.fbScratchContract Arm.abi 9 Proof.Sm4.ofbPost 1480) where
  pre s h := seqArm_pre_rw rfl (len := (· * 16)) (fun n => rfl) (by
    sig_pre [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Proof.Sm4.ofbPost, Spec.Sm4.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := ofb_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore .encrypt) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 16

theorem ofb_verified : Verified Arm.target ofb (Proof.Sm4.fbScratchContract Arm.abi 9 Proof.Sm4.ofbPost 1480) :=
  seq_verified (ecbSpec .encrypt) (ofb_ok _) ofbTaint ofb_implies

theorem ofbFrameSat : ∃ s, (Spec.Sm4.ofbContract Arm.abi 1560).pre s := by
  implies_sat [Spec.Sm4.ofbContract, Spec.Sm4.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 16

/-- `ofb`, with its scratch buffer on the stack (zeroed on return). -/
theorem ofb_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 ofb) (Spec.Sm4.ofbContract Arm.abi 1560) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Sm4.ofbSig) (nm := "scratch") (e := .u64) (n := 9)
    (post := Proof.Sm4.ofbPost Arm.abi.ptrBits) (wa := true) (stack := 1480) (m := 0) (bytes := 80)
    ofb_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm4.ofbPost_local _)
    (Proof.Sm4.ofbPostOut_local _) ofbFrameSat

theorem cfbEncryptTaint : SeqTaint (ecbCore .encrypt) cfbEnc :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cfbEncrypt_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) cfbEnc).Implies
    (Proof.Sm4.fbScratchContract Arm.abi 9 Proof.Sm4.cfbEncPost 1480) where
  pre s h := seqArm_pre_rw rfl (len := (· * 16)) (fun n => rfl) (by
    sig_pre [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Proof.Sm4.cfbEncPost, Spec.Sm4.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbEnc_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore .encrypt) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 16

theorem cfbEncrypt_verified : Verified Arm.target cfbEncrypt (Proof.Sm4.fbScratchContract Arm.abi 9 Proof.Sm4.cfbEncPost 1480) :=
  seq_verified (ecbSpec .encrypt) (cfbEnc_ok _) cfbEncryptTaint cfbEncrypt_implies

theorem cfbEncryptFrameSat : ∃ s, (Spec.Sm4.cfbEncryptContract Arm.abi 1560).pre s := by
  implies_sat [Spec.Sm4.cfbEncryptContract, Spec.Sm4.cfbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 16

/-- `cfbEncrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbEncrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 cfbEncrypt) (Spec.Sm4.cfbEncryptContract Arm.abi 1560) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Sm4.cfbSig) (nm := "scratch") (e := .u64) (n := 9)
    (post := Proof.Sm4.cfbEncPost Arm.abi.ptrBits) (wa := true) (stack := 1480) (m := 0) (bytes := 80)
    cfbEncrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm4.cfbEncPost_local _)
    (Proof.Sm4.cfbEncPostOut_local _) cfbEncryptFrameSat

theorem cfbDecryptTaint : SeqTaint (ecbCore .encrypt) cfbDec :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cfbDecrypt_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) cfbDec).Implies
    (Proof.Sm4.fbScratchContract Arm.abi 9 Proof.Sm4.cfbDecPost 1480) where
  pre s h := seqArm_pre_rw rfl (len := (· * 16)) (fun n => rfl) (by
    sig_pre [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Proof.Sm4.cfbDecPost, Spec.Sm4.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbDec_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore .encrypt) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 16

theorem cfbDecrypt_verified : Verified Arm.target cfbDecrypt (Proof.Sm4.fbScratchContract Arm.abi 9 Proof.Sm4.cfbDecPost 1480) :=
  seq_verified (ecbSpec .encrypt) (cfbDec_ok _) cfbDecryptTaint cfbDecrypt_implies

theorem cfbDecryptFrameSat : ∃ s, (Spec.Sm4.cfbDecryptContract Arm.abi 1560).pre s := by
  implies_sat [Spec.Sm4.cfbDecryptContract, Spec.Sm4.cfbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 16

/-- `cfbDecrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 cfbDecrypt) (Spec.Sm4.cfbDecryptContract Arm.abi 1560) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Sm4.cfbSig) (nm := "scratch") (e := .u64) (n := 9)
    (post := Proof.Sm4.cfbDecPost Arm.abi.ptrBits) (wa := true) (stack := 1480) (m := 0) (bytes := 80)
    cfbDecrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm4.cfbDecPost_local _)
    (Proof.Sm4.cfbDecPostOut_local _) cfbDecryptFrameSat

end VG.Proof.Sm4.Arm
