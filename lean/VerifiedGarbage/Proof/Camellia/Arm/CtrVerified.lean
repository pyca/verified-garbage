module

public import VerifiedGarbage.Proof.Camellia.Arm.ModeCore
public import VerifiedGarbage.Proof.Camellia.CtrScratch
import VerifiedGarbage.Proof.Modes.Arm.Ctr
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
public import VerifiedGarbage.Impl.Camellia.Arm.Ctr
public import VerifiedGarbage.Proof.Modes.Arm.SeqCT

import VerifiedGarbage.Proof.Camellia.Arm.FbVerified
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Camellia.Arm.ModeCore
meta import VerifiedGarbage.Proof.Camellia.CtrScratch
meta import VerifiedGarbage.Proof.Modes.Arm.Ctr
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Impl.Camellia.Arm.Ctr
meta import VerifiedGarbage.Proof.Modes.Arm.SeqCT
meta import VerifiedGarbage.Proof.Camellia.Arm.FbVerified
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Impl.Camellia.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

theorem ctrTaint : SeqTaint (ecbCore .encrypt) VG.Impl.Modes.Arm.ctr :=
  ⟨⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩⟩

theorem ctr_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) VG.Impl.Modes.Arm.ctr).Implies
    (Proof.Camellia.ctrScratchContract Arm.abi 9 2816) where
  pre s h := seqArm_pre_rwR rfl (len := (· * 16)) (fun n => rfl) (by
    sig_pre [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig, Spec.Camellia.ctrPre, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrPost, Spec.Camellia.ctrSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    intro hR
    have e := ctr_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore .encrypt) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, rsel_eq hR, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    exact seqArm_pubR h
  sat := by
    sig_implies_sat [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig, Spec.Camellia.ctrPre, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 0

theorem ctr_verified : Verified Arm.target ctr (Proof.Camellia.ctrScratchContract Arm.abi 9 2816) :=
  seq_verified (ecbSpec .encrypt) (ctr_ok _ rfl) ctrTaint ctr_implies

theorem ctrFrameSat : ∃ s, (Spec.Camellia.ctrContract Arm.abi 2904).pre s := by
  implies_sat [Spec.Camellia.ctrContract, Spec.Camellia.ctrSig, Spec.Camellia.ctrPre, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat, stackArg, stackArgAddr, Mem.readW,
    Mem.read] using fbFrameSat 0

/-- `ctr`, with its scratch buffer on the stack (zeroed on return). -/
theorem ctr_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 ctr)
      (Spec.Camellia.ctrContract Arm.abi 2904) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Camellia.ctrSig) (nm := "scratch") (e := .u64) (n := 9)
    (pre := Spec.Camellia.ctrPre Arm.abi.ptrBits) (post := Spec.Camellia.ctrPost Arm.abi.ptrBits)
    (wa := true) (stack := 2816) (m := 1) (bytes := 88)
    ctr_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (Proof.Camellia.ctrPre_local _) (Proof.Camellia.ctrPost_local _) (Proof.Camellia.ctrPostOut_local _) ctrFrameSat

end VG.Proof.Camellia.Arm
