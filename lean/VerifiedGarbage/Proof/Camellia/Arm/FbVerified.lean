module

public import VerifiedGarbage.Proof.Camellia.Arm.ModeCore
meta import VerifiedGarbage.Proof.Camellia.Arm.ModeCore
public import VerifiedGarbage.Proof.Camellia.FbScratch
meta import VerifiedGarbage.Proof.Camellia.FbScratch
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
public import VerifiedGarbage.Impl.Camellia.Arm.Fb
public import VerifiedGarbage.Proof.Modes.Arm.SeqCT
meta import VerifiedGarbage.Impl.Camellia.Arm.Fb
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Impl.Aes.Arm.Alloc
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.Camellia.Arm.Copy
import VerifiedGarbage.Proof.Camellia.Arm.Crypt8
import VerifiedGarbage.Proof.Camellia.Arm.Fl
import VerifiedGarbage.Proof.Camellia.Arm.Verified
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
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Impl.Aes.Arm.Alloc
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.Aes.SboxSpec
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.Camellia.Arm.Copy
meta import VerifiedGarbage.Proof.Camellia.Arm.Crypt8
meta import VerifiedGarbage.Proof.Camellia.Arm.Fl
meta import VerifiedGarbage.Proof.Camellia.Arm.Verified
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
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Spec.Ctr.Contract

/-!
# Camellia-OFB and Camellia-CFB128 on ARMv7 meet their contracts

The generic OFB and CFB one block at a time over Camellia's ECB encryption
(`Proof.Modes.Arm.seq_verified` with `ecbSpec .encrypt`, a core taking the
number of rounds) meet the contracts with a scratch buffer of 9 words
(`Proof.Camellia.ofbScratchContract`, …), with the 2816 bytes of stack the
ECB function uses; the `_framed` theorems keep the buffer on the stack,
zeroed on return: 88 bytes more.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Impl.Camellia.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

/-- A state satisfying the precondition with the scratch buffer (no blocks):
the schedule at `0x1000`, 18 rounds, the IV at `0x2000`, the data at
`0x3000`, and `n = 0` and the scratch buffer's address `0` (the stack
arguments, in memory that is zero). -/
def fbSat (len : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 18 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 272⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, len⟩, ⟨0, 72⟩]

/-- A state satisfying the functions' precondition (no blocks). -/
def fbFrameSat (len : Nat) : State :=
  { fbSat len with rd := [⟨0x1000, 272⟩, ⟨0x8000, 4⟩], wr := [⟨0x2000, 16⟩, ⟨0x3000, len⟩] }

theorem ofbTaint : SeqTaint (ecbCore .encrypt) VG.Impl.Modes.Arm.ofb :=
  ⟨⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩⟩

theorem ofb_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) VG.Impl.Modes.Arm.ofb).Implies
    (Proof.Camellia.ofbScratchContract Arm.abi 9 2816) where
  pre s h := seqArm_pre_rwR rfl (len := (· * 16)) (fun n => rfl) (by
    sig_pre [Proof.Camellia.ofbScratchContract, Proof.Camellia.ofbScratchSig, Spec.Camellia.ofbSig, Spec.Camellia.ofbPre, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Camellia.ofbScratchContract, Proof.Camellia.ofbScratchSig, Spec.Camellia.ofbPost, Spec.Camellia.ofbSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    intro hR
    have e := ofb_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore .encrypt) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, rsel_eq hR, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Camellia.ofbScratchContract, Proof.Camellia.ofbScratchSig, Spec.Camellia.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    exact seqArm_pubR h
  sat := by
    sig_implies_sat [Proof.Camellia.ofbScratchContract, Proof.Camellia.ofbScratchSig, Spec.Camellia.ofbSig, Spec.Camellia.ofbPre, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 0

theorem ofb_verified : Verified Arm.target ofb (Proof.Camellia.ofbScratchContract Arm.abi 9 2816) :=
  seq_verified (ecbSpec .encrypt) (ofb_ok _) ofbTaint ofb_implies

theorem ofbFrameSat : ∃ s, (Spec.Camellia.ofbContract Arm.abi 2904).pre s := by
  implies_sat [Spec.Camellia.ofbContract, Spec.Camellia.ofbSig, Spec.Camellia.ofbPre, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat, stackArg, stackArgAddr, Mem.readW,
    Mem.read] using fbFrameSat 0

/-- `ofb`, with its scratch buffer on the stack (zeroed on return). -/
theorem ofb_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 ofb)
      (Spec.Camellia.ofbContract Arm.abi 2904) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Camellia.ofbSig) (nm := "scratch") (e := .u64) (n := 9)
    (pre := Spec.Camellia.ofbPre Arm.abi.ptrBits) (post := Spec.Camellia.ofbPost Arm.abi.ptrBits)
    (wa := true) (stack := 2816) (m := 1) (bytes := 88)
    ofb_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (Proof.Camellia.ofbPre_local _) (Proof.Camellia.ofbPost_local _) (Proof.Camellia.ofbPostOut_local _) ofbFrameSat

theorem cfbEncryptTaint : SeqTaint (ecbCore .encrypt) cfbEnc :=
  ⟨⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩⟩

theorem cfbEncrypt_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) cfbEnc).Implies
    (Proof.Camellia.cfbEncScratchContract Arm.abi 9 2816) where
  pre s h := seqArm_pre_rwR rfl (len := (· * 16)) (fun n => rfl) (by
    sig_pre [Proof.Camellia.cfbEncScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Camellia.cfbEncScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbEncryptPost, Spec.Camellia.cfbSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    intro hR
    have e := cfbEnc_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore .encrypt) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, rsel_eq hR, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Camellia.cfbEncScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    exact seqArm_pubR h
  sat := by
    sig_implies_sat [Proof.Camellia.cfbEncScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 0

theorem cfbEncrypt_verified : Verified Arm.target cfbEncrypt (Proof.Camellia.cfbEncScratchContract Arm.abi 9 2816) :=
  seq_verified (ecbSpec .encrypt) (cfbEnc_ok _) cfbEncryptTaint cfbEncrypt_implies

theorem cfbEncryptFrameSat : ∃ s, (Spec.Camellia.cfbEncryptContract Arm.abi 2904).pre s := by
  implies_sat [Spec.Camellia.cfbEncryptContract, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat, stackArg, stackArgAddr, Mem.readW,
    Mem.read] using fbFrameSat 0

/-- `cfbEncrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbEncrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 cfbEncrypt)
      (Spec.Camellia.cfbEncryptContract Arm.abi 2904) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Camellia.cfbSig) (nm := "scratch") (e := .u64) (n := 9)
    (pre := Spec.Camellia.cfbPre Arm.abi.ptrBits) (post := Spec.Camellia.cfbEncryptPost Arm.abi.ptrBits)
    (wa := true) (stack := 2816) (m := 1) (bytes := 88)
    cfbEncrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (Proof.Camellia.cfbPre_local _) (Proof.Camellia.cfbEncryptPost_local _) (Proof.Camellia.cfbEncryptPostOut_local _) cfbEncryptFrameSat

theorem cfbDecryptTaint : SeqTaint (ecbCore .encrypt) cfbDec :=
  ⟨⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩⟩

theorem cfbDecrypt_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) cfbDec).Implies
    (Proof.Camellia.cfbDecScratchContract Arm.abi 9 2816) where
  pre s h := seqArm_pre_rwR rfl (len := (· * 16)) (fun n => rfl) (by
    sig_pre [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbDecryptPost, Spec.Camellia.cfbSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    intro hR
    have e := cfbDec_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore .encrypt) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, rsel_eq hR, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    exact seqArm_pubR h
  sat := by
    sig_implies_sat [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 0

theorem cfbDecrypt_verified : Verified Arm.target cfbDecrypt (Proof.Camellia.cfbDecScratchContract Arm.abi 9 2816) :=
  seq_verified (ecbSpec .encrypt) (cfbDec_ok _) cfbDecryptTaint cfbDecrypt_implies

theorem cfbDecryptFrameSat : ∃ s, (Spec.Camellia.cfbDecryptContract Arm.abi 2904).pre s := by
  implies_sat [Spec.Camellia.cfbDecryptContract, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat, stackArg, stackArgAddr, Mem.readW,
    Mem.read] using fbFrameSat 0

/-- `cfbDecrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 cfbDecrypt)
      (Spec.Camellia.cfbDecryptContract Arm.abi 2904) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Camellia.cfbSig) (nm := "scratch") (e := .u64) (n := 9)
    (pre := Spec.Camellia.cfbPre Arm.abi.ptrBits) (post := Spec.Camellia.cfbDecryptPost Arm.abi.ptrBits)
    (wa := true) (stack := 2816) (m := 1) (bytes := 88)
    cfbDecrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (Proof.Camellia.cfbPre_local _) (Proof.Camellia.cfbDecryptPost_local _) (Proof.Camellia.cfbDecryptPostOut_local _) cfbDecryptFrameSat

end VG.Proof.Camellia.Arm
