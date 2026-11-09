module

public import VerifiedGarbage.Proof.Camellia.Arm.FbVerified
public import VerifiedGarbage.Proof.Modes.Arm.SeqFinalCT
public import VerifiedGarbage.Proof.Camellia.CfbFinalScratch
public import VerifiedGarbage.Impl.Camellia.Arm.FbFinal
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Camellia.Arm.FbVerified
meta import VerifiedGarbage.Proof.Modes.Arm.SeqFinalCT
meta import VerifiedGarbage.Proof.Camellia.CfbFinalScratch
meta import VerifiedGarbage.Impl.Camellia.Arm.FbFinal
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-!
# Camellia-CFB128 and Camellia-OFB of a message's last piece on ARMv7 meet their contracts

The generic CFB and OFB over a message's last piece (`Proof.Modes.Arm.seqFinal_verified`)
over Camellia's ECB encryption (`ecbSpec .encrypt`, a core taking the number
of rounds) meet the contracts on the subkeys at the schedule
(`Proof.Camellia.cfbEncFinalScratchContract`, …) with a scratch buffer of 9
words, as the whole-block functions do (`FbVerified.lean`), with the
specification's results (`Proof.Modes.Arm.cfbEncFinal_post`, …,
`Proof.Modes.Arm.ofbFinal_post`); the
`_framed` theorems keep the buffer on the stack, zeroed on return: 88 bytes
more, and give the specification's contracts (`cfbEncryptFinal_of_sk`, …).
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Impl.Camellia.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

theorem cfbEncryptFinalTaint : FinalTaint (ecbCore .encrypt) cfbEnc :=
  ⟨cfbEncryptTaint.pro, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, cfbEncryptTaint.epi⟩

theorem cfbEncryptFinal_implies : (seqFinalArm (ecbCore .encrypt) (ecbSpec .encrypt) cfbEnc).Implies
    (Proof.Camellia.cfbEncFinalScratchContract Arm.abi 9 2816) where
  pre s h := seqArm_pre_rwR (M := byteMode) rfl (len := fun n => n) (fun n => (Nat.mul_one n).symm) (by
    sig_pre [Proof.Camellia.cfbEncFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Camellia.cfbEncFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.cfbFinalSig, Proof.Camellia.cfbEncryptFinalPostSk, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    intro hR
    have e := cfbEncFinal_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore .encrypt) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, rsel_eq hR, State.addr] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Camellia.cfbEncFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.cfbFinalSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pubR (M := byteMode) h
  sat := by
    sig_implies_sat [Proof.Camellia.cfbEncFinalScratchContract, Sig.scratchContract, Sig.withScratch,
      Curry.withScratch, Curry.app, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using fbSat 0

theorem cfbEncryptFinal_verified : Verified Arm.target cfbEncryptFinal
    (Proof.Camellia.cfbEncFinalScratchContract Arm.abi 9 2816) :=
  seqFinal_verified (ecbSpec .encrypt) (cfbEnc_finalOk _ (by decide) (by decide) (by decide)) cfbEncryptFinalTaint
    cfbEncryptFinal_implies

theorem cfbEncryptFinalFrameSat : ∃ s, (Proof.Camellia.cfbEncryptFinalContractSk Arm.abi 2904).pre s := by
  implies_sat [Proof.Camellia.cfbEncryptFinalContractSk, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat, stackArg,
    stackArgAddr, Mem.readW, Mem.read] using fbFrameSat 0

/-- `cfbEncryptFinal`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbEncryptFinal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 cfbEncryptFinal)
      (Spec.Camellia.cfbEncryptFinalContract Arm.abi 2904) :=
  Proof.Camellia.cfbEncryptFinal_of_sk <|
  Arm.Verified.stackScratchWiped (sig := Spec.Camellia.cfbFinalSig) (nm := "scratch") (e := .u64) (n := 9)
    (pre := Spec.Camellia.cfbFinalPre Arm.abi.ptrBits) (post := Proof.Camellia.cfbEncryptFinalPostSk Arm.abi.ptrBits)
    (wa := true) (stack := 2816) (m := 1) (bytes := 88)
    cfbEncryptFinal_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (Proof.Camellia.cfbFinalPre_local _) (Proof.Camellia.cfbEncryptFinalPost_local _)
    (Proof.Camellia.cfbEncryptFinalPostOut_local _) cfbEncryptFinalFrameSat

theorem cfbDecryptFinalTaint : FinalTaint (ecbCore .encrypt) cfbDecF :=
  ⟨cfbDecryptTaint.pro, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, cfbDecryptTaint.epi⟩

theorem cfbDecryptFinal_implies : (seqFinalArm (ecbCore .encrypt) (ecbSpec .encrypt) cfbDecF).Implies
    (Proof.Camellia.cfbDecFinalScratchContract Arm.abi 9 2816) where
  pre s h := seqArm_pre_rwR (M := byteMode) rfl (len := fun n => n) (fun n => (Nat.mul_one n).symm) (by
    sig_pre [Proof.Camellia.cfbDecFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Camellia.cfbDecFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.cfbFinalSig, Proof.Camellia.cfbDecryptFinalPostSk, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    intro hR
    have e := cfbDecFinal_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore .encrypt) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, rsel_eq hR, State.addr] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Camellia.cfbDecFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.cfbFinalSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pubR (M := byteMode) h
  sat := by
    sig_implies_sat [Proof.Camellia.cfbDecFinalScratchContract, Sig.scratchContract, Sig.withScratch,
      Curry.withScratch, Curry.app, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using fbSat 0

theorem cfbDecryptFinal_verified : Verified Arm.target cfbDecryptFinal
    (Proof.Camellia.cfbDecFinalScratchContract Arm.abi 9 2816) :=
  seqFinal_verified (ecbSpec .encrypt) (cfbDecF_finalOk _ (by decide) (by decide) (by decide)) cfbDecryptFinalTaint
    cfbDecryptFinal_implies

theorem cfbDecryptFinalFrameSat : ∃ s, (Proof.Camellia.cfbDecryptFinalContractSk Arm.abi 2904).pre s := by
  implies_sat [Proof.Camellia.cfbDecryptFinalContractSk, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat, stackArg,
    stackArgAddr, Mem.readW, Mem.read] using fbFrameSat 0

/-- `cfbDecryptFinal`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbDecryptFinal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 cfbDecryptFinal)
      (Spec.Camellia.cfbDecryptFinalContract Arm.abi 2904) :=
  Proof.Camellia.cfbDecryptFinal_of_sk <|
  Arm.Verified.stackScratchWiped (sig := Spec.Camellia.cfbFinalSig) (nm := "scratch") (e := .u64) (n := 9)
    (pre := Spec.Camellia.cfbFinalPre Arm.abi.ptrBits) (post := Proof.Camellia.cfbDecryptFinalPostSk Arm.abi.ptrBits)
    (wa := true) (stack := 2816) (m := 1) (bytes := 88)
    cfbDecryptFinal_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (Proof.Camellia.cfbFinalPre_local _) (Proof.Camellia.cfbDecryptFinalPost_local _)
    (Proof.Camellia.cfbDecryptFinalPostOut_local _) cfbDecryptFinalFrameSat

/-! ## OFB of a message's last piece -/

theorem ofbFinalTaint : FinalTaint (ecbCore .encrypt) VG.Impl.Modes.Arm.ofb :=
  ⟨ofbTaint.pro, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ofbTaint.epi⟩

theorem ofbFinal_implies : (seqFinalArm (ecbCore .encrypt) (ecbSpec .encrypt) VG.Impl.Modes.Arm.ofb).Implies
    (Proof.Camellia.ofbFinalScratchContract Arm.abi 9 2816) where
  pre s h := seqArm_pre_rwR (M := byteMode) rfl (len := fun n => n) (fun n => (Nat.mul_one n).symm) (by
    sig_pre [Proof.Camellia.ofbFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.ofbFinalSig, Spec.Camellia.ofbFinalPre, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Camellia.ofbFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.ofbFinalSig, Proof.Camellia.ofbFinalPostSk, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    intro hR
    have e := ofbFinal_post h fun b => by
      show _ = 16
      simp [ecbSpec, dirCipher, Spec.Camellia.cipher]
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore .encrypt) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, rsel_eq hR, State.addr] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Camellia.ofbFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.ofbFinalSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pubR (M := byteMode) h
  sat := by
    sig_implies_sat [Proof.Camellia.ofbFinalScratchContract, Sig.scratchContract, Sig.withScratch,
      Curry.withScratch, Curry.app, Spec.Camellia.ofbFinalSig, Spec.Camellia.ofbFinalPre, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using fbSat 0

theorem ofbFinal_verified : Verified Arm.target ofbFinal
    (Proof.Camellia.ofbFinalScratchContract Arm.abi 9 2816) :=
  seqFinal_verified (ecbSpec .encrypt) (ofb_finalOk _ (by decide) (by decide) (by decide)) ofbFinalTaint
    ofbFinal_implies

theorem ofbFinalFrameSat : ∃ s, (Proof.Camellia.ofbFinalContractSk Arm.abi 2904).pre s := by
  implies_sat [Proof.Camellia.ofbFinalContractSk, Spec.Camellia.ofbFinalSig, Spec.Camellia.ofbFinalPre,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat, stackArg,
    stackArgAddr, Mem.readW, Mem.read] using fbFrameSat 0

/-- `ofbFinal`, with its scratch buffer on the stack (zeroed on return). -/
theorem ofbFinal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 ofbFinal)
      (Spec.Camellia.ofbFinalContract Arm.abi 2904) :=
  Proof.Camellia.ofbFinal_of_sk <|
  Arm.Verified.stackScratchWiped (sig := Spec.Camellia.ofbFinalSig) (nm := "scratch") (e := .u64) (n := 9)
    (pre := Spec.Camellia.ofbFinalPre Arm.abi.ptrBits) (post := Proof.Camellia.ofbFinalPostSk Arm.abi.ptrBits)
    (wa := true) (stack := 2816) (m := 1) (bytes := 88)
    ofbFinal_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (Proof.Camellia.ofbFinalPre_local _) (Proof.Camellia.ofbFinalPost_local _)
    (Proof.Camellia.ofbFinalPostOut_local _) ofbFinalFrameSat

end VG.Proof.Camellia.Arm
