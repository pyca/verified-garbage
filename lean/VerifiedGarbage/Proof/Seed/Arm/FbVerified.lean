module

public import VerifiedGarbage.Proof.Seed.Arm.ModeCore
meta import VerifiedGarbage.Proof.Seed.Arm.ModeCore
public import VerifiedGarbage.Proof.Seed.FbScratch
public import VerifiedGarbage.Proof.Modes.Arm.SeqCT
public import VerifiedGarbage.Spec.Seed.Cfb
meta import VerifiedGarbage.Proof.Seed.FbScratch
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Impl.Aes.Arm.Alloc
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacAes.Arm.Words
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Modes.Arm.Counter
import VerifiedGarbage.Proof.Modes.Arm.SeqLoop
import VerifiedGarbage.Proof.Seed.Arm.Crypt8
import VerifiedGarbage.Proof.Seed.Arm.Verified
import VerifiedGarbage.Proof.Seed.G16
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Impl.Aes.Arm.Alloc
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.CmacAes.Arm.Words
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Modes.Addr
meta import VerifiedGarbage.Proof.Modes.Arm.Counter
meta import VerifiedGarbage.Proof.Modes.Arm.SeqLoop
meta import VerifiedGarbage.Proof.Seed.Arm.Crypt8
meta import VerifiedGarbage.Proof.Seed.Arm.Verified
meta import VerifiedGarbage.Proof.Seed.G16
meta import VerifiedGarbage.Proof.Seed.Memory
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Spec.Seed.Cfb

/-!
# SEED-OFB and SEED-CFB128 on ARMv7 meet their contracts

The generic OFB and CFB one block at a time over SEED's ECB encryption
(`Proof.Modes.Arm.seq_verified` with `ecbSpec .encrypt`) meet the contracts
with a scratch buffer of 9 words (`Proof.Seed.fbScratchContract`), with the
752 bytes of stack the ECB function uses; the `_framed` theorems keep the
buffer on the stack, zeroed on return: 80 bytes more.
-/

@[expose] public section

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Impl.Seed.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

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
  ⟨⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩⟩

theorem ofb_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) VG.Impl.Modes.Arm.ofb).Implies
    (Proof.Seed.fbScratchContract Arm.abi 9 Proof.Seed.ofbPost 752) where
  pre s h := seqArm_pre_rw rfl (len := (· * 16)) (fun n => rfl) (by
    sig_pre [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Proof.Seed.ofbPost, Spec.Seed.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := ofb_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore .encrypt) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 16

theorem ofb_verified : Verified Arm.target ofb (Proof.Seed.fbScratchContract Arm.abi 9 Proof.Seed.ofbPost 752) :=
  seq_verified (ecbSpec .encrypt) (ofb_ok _) ofbTaint ofb_implies

theorem ofbFrameSat : ∃ s, (Spec.Seed.ofbContract Arm.abi 832).pre s := by
  implies_sat [Spec.Seed.ofbContract, Spec.Seed.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 16

/-- `ofb`, with its scratch buffer on the stack (zeroed on return). -/
theorem ofb_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 ofb) (Spec.Seed.ofbContract Arm.abi 832) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Seed.ofbSig) (nm := "scratch") (e := .u64) (n := 9)
    (post := Proof.Seed.ofbPost Arm.abi.ptrBits) (wa := true) (stack := 752) (m := 0) (bytes := 80)
    ofb_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Seed.ofbPost_local _)
    (Proof.Seed.ofbPostOut_local _) ofbFrameSat

theorem cfbEncryptTaint : SeqTaint (ecbCore .encrypt) cfbEnc :=
  ⟨⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩⟩

theorem cfbEncrypt_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) cfbEnc).Implies
    (Proof.Seed.fbScratchContract Arm.abi 9 Proof.Seed.cfbEncPost 752) where
  pre s h := seqArm_pre_rw rfl (len := (· * 16)) (fun n => rfl) (by
    sig_pre [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Proof.Seed.cfbEncPost, Spec.Seed.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbEnc_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore .encrypt) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 16

theorem cfbEncrypt_verified : Verified Arm.target cfbEncrypt (Proof.Seed.fbScratchContract Arm.abi 9 Proof.Seed.cfbEncPost 752) :=
  seq_verified (ecbSpec .encrypt) (cfbEnc_ok _) cfbEncryptTaint cfbEncrypt_implies

theorem cfbEncryptFrameSat : ∃ s, (Spec.Seed.cfbEncryptContract Arm.abi 832).pre s := by
  implies_sat [Spec.Seed.cfbEncryptContract, Spec.Seed.cfbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 16

/-- `cfbEncrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbEncrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 cfbEncrypt) (Spec.Seed.cfbEncryptContract Arm.abi 832) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Seed.cfbSig) (nm := "scratch") (e := .u64) (n := 9)
    (post := Proof.Seed.cfbEncPost Arm.abi.ptrBits) (wa := true) (stack := 752) (m := 0) (bytes := 80)
    cfbEncrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Seed.cfbEncPost_local _)
    (Proof.Seed.cfbEncPostOut_local _) cfbEncryptFrameSat

theorem cfbDecryptTaint : SeqTaint (ecbCore .encrypt) cfbDec :=
  ⟨⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩⟩

theorem cfbDecrypt_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) cfbDec).Implies
    (Proof.Seed.fbScratchContract Arm.abi 9 Proof.Seed.cfbDecPost 752) where
  pre s h := seqArm_pre_rw rfl (len := (· * 16)) (fun n => rfl) (by
    sig_pre [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Proof.Seed.cfbDecPost, Spec.Seed.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbDec_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore .encrypt) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 16

theorem cfbDecrypt_verified : Verified Arm.target cfbDecrypt (Proof.Seed.fbScratchContract Arm.abi 9 Proof.Seed.cfbDecPost 752) :=
  seq_verified (ecbSpec .encrypt) (cfbDec_ok _) cfbDecryptTaint cfbDecrypt_implies

theorem cfbDecryptFrameSat : ∃ s, (Spec.Seed.cfbDecryptContract Arm.abi 832).pre s := by
  implies_sat [Spec.Seed.cfbDecryptContract, Spec.Seed.cfbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 16

/-- `cfbDecrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 cfbDecrypt) (Spec.Seed.cfbDecryptContract Arm.abi 832) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Seed.cfbSig) (nm := "scratch") (e := .u64) (n := 9)
    (post := Proof.Seed.cfbDecPost Arm.abi.ptrBits) (wa := true) (stack := 752) (m := 0) (bytes := 80)
    cfbDecrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Seed.cfbDecPost_local _)
    (Proof.Seed.cfbDecPostOut_local _) cfbDecryptFrameSat

end VG.Proof.Seed.Arm
