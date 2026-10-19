module

public import VerifiedGarbage.Proof.TripleDes.Arm.ModeCore
meta import VerifiedGarbage.Proof.TripleDes.Arm.ModeCore
public import VerifiedGarbage.Proof.TripleDes.FbScratch
meta import VerifiedGarbage.Proof.TripleDes.FbScratch
import VerifiedGarbage.Proof.Modes.Arm.Cfb8
meta import VerifiedGarbage.Proof.Modes.Arm.Cfb8
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
public import VerifiedGarbage.Impl.TripleDes.Arm.Fb
meta import VerifiedGarbage.Impl.TripleDes.Arm.Fb
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Proof.Modes.Arm.SeqCT
meta import VerifiedGarbage.Spec.TripleDes.Cfb
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Impl.Aes.Arm.Alloc
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacAes.Arm.Words
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Linear
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Modes.Arm.Counter
import VerifiedGarbage.Proof.Modes.Arm.SeqLoop
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.TripleDes.Arm.Frame
import VerifiedGarbage.Proof.TripleDes.Arm.Key.Verified
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.TripleDes.CbcBlocks
import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Impl.Aes.Arm.Alloc
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.Aes.SboxSpec
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.CmacAes.Arm.Words
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Linear
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Modes.Addr
meta import VerifiedGarbage.Proof.Modes.Arm.Counter
meta import VerifiedGarbage.Proof.Modes.Arm.SeqLoop
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.TripleDes.Arm.Frame
meta import VerifiedGarbage.Proof.TripleDes.Arm.Key.Verified
meta import VerifiedGarbage.Proof.TripleDes.Bytes
meta import VerifiedGarbage.Proof.TripleDes.CbcBlocks
meta import VerifiedGarbage.Spec.Ctr.Contract

/-!
# Triple DES-OFB, -CFB64 and -CFB8 on ARMv7 meet their contracts

The generic OFB, CFB and CFB8 one element at a time over Triple DES's ECB
encryption (`Proof.Modes.Arm.seq_verified` with `ecbSpec .encrypt`) meet the
contracts with a scratch buffer of 7 words (`Proof.TripleDes.fbScratchContract`,
`cfb8ScratchContract`), with the 1024 bytes of stack the ECB function uses;
the `_framed` theorems keep the buffer on the stack, zeroed on return: 64
bytes more.
-/

@[expose] public section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

/-- A state satisfying the precondition with the scratch buffer (one block,
or `len` bytes, at `0x3000`), the IV read and written. -/
def fbSat (len : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 384⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, len⟩, ⟨0, 56⟩]

/-- A state satisfying the functions' precondition. -/
def fbFrameSat (len : Nat) : State := { fbSat len with rd := [⟨0x1000, 384⟩], wr := [⟨0x2000, 8⟩, ⟨0x3000, len⟩] }

theorem ofbTaint : SeqTaint (ecbCore .encrypt) VG.Impl.Modes.Arm.ofb :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem ofb_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) VG.Impl.Modes.Arm.ofb).Implies
    (Proof.TripleDes.fbScratchContract Arm.abi 7 Proof.TripleDes.ofbPost 1024) where
  pre s h := seqArm_pre_rw rfl (len := (· * 8)) (fun n => rfl) (by
    sig_pre [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Proof.TripleDes.ofbPost, Spec.TripleDes.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := ofb_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore .encrypt) rfl s
    simp only [e1, e2, e3] at e
    rw [show (ecbCore .encrypt).bs = 8 from rfl] at e
    simp only [ecbSpec, dirCipher, State.addr, blocksOf_eq] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 8

theorem ofb_verified : Verified Arm.target ofb (Proof.TripleDes.fbScratchContract Arm.abi 7 Proof.TripleDes.ofbPost 1024) :=
  seq_verified (ecbSpec .encrypt) (ofb_ok _) ofbTaint ofb_implies

theorem ofbFrameSat : ∃ s, (Spec.TripleDes.ofbContract Arm.abi 1088).pre s := by
  implies_sat [Spec.TripleDes.ofbContract, Spec.TripleDes.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 8

/-- `ofb`, with its scratch buffer on the stack (zeroed on return). -/
theorem ofb_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 ofb) (Spec.TripleDes.ofbContract Arm.abi 1088) :=
  Arm.Verified.stackScratchWiped (sig := Spec.TripleDes.ofbSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.TripleDes.ofbPost Arm.abi.ptrBits) (wa := true) (stack := 1024) (m := 0) (bytes := 64)
    ofb_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.TripleDes.ofbPost_local _)
    (Proof.TripleDes.ofbPostOut_local _) ofbFrameSat

theorem cfbEncryptTaint : SeqTaint (ecbCore .encrypt) cfbEnc :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cfbEncrypt_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) cfbEnc).Implies
    (Proof.TripleDes.fbScratchContract Arm.abi 7 Proof.TripleDes.cfbEncPost 1024) where
  pre s h := seqArm_pre_rw rfl (len := (· * 8)) (fun n => rfl) (by
    sig_pre [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Proof.TripleDes.cfbEncPost, Spec.TripleDes.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbEnc_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore .encrypt) rfl s
    simp only [e1, e2, e3] at e
    rw [show (ecbCore .encrypt).bs = 8 from rfl] at e
    simp only [ecbSpec, dirCipher, State.addr, blocksOf_eq] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 8

theorem cfbEncrypt_verified : Verified Arm.target cfbEncrypt (Proof.TripleDes.fbScratchContract Arm.abi 7 Proof.TripleDes.cfbEncPost 1024) :=
  seq_verified (ecbSpec .encrypt) (cfbEnc_ok _) cfbEncryptTaint cfbEncrypt_implies

theorem cfbEncryptFrameSat : ∃ s, (Spec.TripleDes.cfbEncryptContract Arm.abi 1088).pre s := by
  implies_sat [Spec.TripleDes.cfbEncryptContract, Spec.TripleDes.cfbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 8

/-- `cfbEncrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbEncrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cfbEncrypt) (Spec.TripleDes.cfbEncryptContract Arm.abi 1088) :=
  Arm.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.TripleDes.cfbEncPost Arm.abi.ptrBits) (wa := true) (stack := 1024) (m := 0) (bytes := 64)
    cfbEncrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.TripleDes.cfbEncPost_local _)
    (Proof.TripleDes.cfbEncPostOut_local _) cfbEncryptFrameSat

theorem cfbDecryptTaint : SeqTaint (ecbCore .encrypt) cfbDec :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cfbDecrypt_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) cfbDec).Implies
    (Proof.TripleDes.fbScratchContract Arm.abi 7 Proof.TripleDes.cfbDecPost 1024) where
  pre s h := seqArm_pre_rw rfl (len := (· * 8)) (fun n => rfl) (by
    sig_pre [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Proof.TripleDes.cfbDecPost, Spec.TripleDes.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbDec_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore .encrypt) rfl s
    simp only [e1, e2, e3] at e
    rw [show (ecbCore .encrypt).bs = 8 from rfl] at e
    simp only [ecbSpec, dirCipher, State.addr, blocksOf_eq] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 8

theorem cfbDecrypt_verified : Verified Arm.target cfbDecrypt (Proof.TripleDes.fbScratchContract Arm.abi 7 Proof.TripleDes.cfbDecPost 1024) :=
  seq_verified (ecbSpec .encrypt) (cfbDec_ok _) cfbDecryptTaint cfbDecrypt_implies

theorem cfbDecryptFrameSat : ∃ s, (Spec.TripleDes.cfbDecryptContract Arm.abi 1088).pre s := by
  implies_sat [Spec.TripleDes.cfbDecryptContract, Spec.TripleDes.cfbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 8

/-- `cfbDecrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cfbDecrypt) (Spec.TripleDes.cfbDecryptContract Arm.abi 1088) :=
  Arm.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.TripleDes.cfbDecPost Arm.abi.ptrBits) (wa := true) (stack := 1024) (m := 0) (bytes := 64)
    cfbDecrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.TripleDes.cfbDecPost_local _)
    (Proof.TripleDes.cfbDecPostOut_local _) cfbDecryptFrameSat

theorem cfb8EncryptTaint : SeqTaint (ecbCore .encrypt) cfb8Enc :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cfb8Encrypt_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) cfb8Enc).Implies
    (Proof.TripleDes.cfb8ScratchContract Arm.abi 7 Proof.TripleDes.cfb8EncPost 1024) where
  pre s h := seqArm_pre_rw rfl (M := cfb8Enc) (len := id) (fun n => show n = n * 1 from (Nat.mul_one n).symm) (by
    sig_pre [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Proof.TripleDes.cfb8EncPost, Spec.TripleDes.cfb8Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfb8Enc_post (by decide) h
    simp only [ecbSpec, dirCipher, State.addr] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 1

theorem cfb8Encrypt_verified : Verified Arm.target cfb8Encrypt (Proof.TripleDes.cfb8ScratchContract Arm.abi 7 Proof.TripleDes.cfb8EncPost 1024) :=
  seq_verified (ecbSpec .encrypt) (cfb8Enc_ok _ (by decide)) cfb8EncryptTaint cfb8Encrypt_implies

theorem cfb8EncryptFrameSat : ∃ s, (Spec.TripleDes.cfb8EncryptContract Arm.abi 1088).pre s := by
  implies_sat [Spec.TripleDes.cfb8EncryptContract, Spec.TripleDes.cfb8Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 1

/-- `cfb8Encrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfb8Encrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cfb8Encrypt) (Spec.TripleDes.cfb8EncryptContract Arm.abi 1088) :=
  Arm.Verified.stackScratchWiped (sig := Spec.TripleDes.cfb8Sig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.TripleDes.cfb8EncPost Arm.abi.ptrBits) (wa := true) (stack := 1024) (m := 0) (bytes := 64)
    cfb8Encrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.TripleDes.cfb8EncPost_local _)
    (Proof.TripleDes.cfb8EncPostOut_local _) cfb8EncryptFrameSat

theorem cfb8DecryptTaint : SeqTaint (ecbCore .encrypt) cfb8Dec :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cfb8Decrypt_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) cfb8Dec).Implies
    (Proof.TripleDes.cfb8ScratchContract Arm.abi 7 Proof.TripleDes.cfb8DecPost 1024) where
  pre s h := seqArm_pre_rw rfl (M := cfb8Dec) (len := id) (fun n => show n = n * 1 from (Nat.mul_one n).symm) (by
    sig_pre [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Proof.TripleDes.cfb8DecPost, Spec.TripleDes.cfb8Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfb8Dec_post (by decide) h
    simp only [ecbSpec, dirCipher, State.addr] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 1

theorem cfb8Decrypt_verified : Verified Arm.target cfb8Decrypt (Proof.TripleDes.cfb8ScratchContract Arm.abi 7 Proof.TripleDes.cfb8DecPost 1024) :=
  seq_verified (ecbSpec .encrypt) (cfb8Dec_ok _ (by decide)) cfb8DecryptTaint cfb8Decrypt_implies

theorem cfb8DecryptFrameSat : ∃ s, (Spec.TripleDes.cfb8DecryptContract Arm.abi 1088).pre s := by
  implies_sat [Spec.TripleDes.cfb8DecryptContract, Spec.TripleDes.cfb8Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 1

/-- `cfb8Decrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfb8Decrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cfb8Decrypt) (Spec.TripleDes.cfb8DecryptContract Arm.abi 1088) :=
  Arm.Verified.stackScratchWiped (sig := Spec.TripleDes.cfb8Sig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.TripleDes.cfb8DecPost Arm.abi.ptrBits) (wa := true) (stack := 1024) (m := 0) (bytes := 64)
    cfb8Decrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.TripleDes.cfb8DecPost_local _)
    (Proof.TripleDes.cfb8DecPostOut_local _) cfb8DecryptFrameSat

end VG.Proof.TripleDes.Arm
