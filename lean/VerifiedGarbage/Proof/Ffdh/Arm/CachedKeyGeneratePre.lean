module

public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateFn
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Spec.Ffdh.Contract

/-! The cached signature extends the established attempt's read-only arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

def cachedPlainState (s : State) : State :=
  s.withRegions [⟨State.addr (stackArg s 0),(stackArg s 1).toNat⟩,
    ⟨State.addr (stackArg s 3),(stackArg s 4).toNat⟩,⟨stackArgAddr s 0,28⟩] s.wr

theorem cachedKeyGenerate_plain_pre (s : State)
    (pre : (Spec.Ffdh.cachedGenerateKeyContract abi 176).pre s) :
    (Spec.Ffdh.generateKeyContract abi 176).pre (cachedPlainState s) := by
  sig_pre [Spec.Ffdh.cachedGenerateKeyContract, Spec.Ffdh.cachedGenerateKeySig,
    Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit,argFit,_rd,wr,xY,xDom,xRand,xS,_xCtx,xArgs,yDom,yRand,yS,_yCtx,yArgs,
    domS,randS,_sCtx,sArgs,stackX,stackY,stackDom,stackRand,stackS,_stackCtx,stackArgs,
    xFit,yFit,domFit,randFit,sFit,_ctxFit,bounds,domainLen,xLen,yLen,rLen,space,_valid,_canonical⟩ := pre
  have inner : (⟨stackArgAddr s 0,28⟩ : Region).Sub ⟨stackArgAddr s 0,36⟩ := by
    simpa only [VG.Proof.Mont.off,BitVec.add_zero] using Offset.sub_base (stackArgAddr s 0) (by decide : 0+28≤36)
  sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs,
    reduceClassify, Loc.val, State.addr]
  exact ⟨stackFit,by omega,rfl,wr,xY,xDom,xRand,xS,
    xArgs.sub_right inner,yDom,yRand,yS,yArgs.sub_right inner,domS,randS,sArgs.sub_right inner,
    stackX,stackY,stackDom,stackRand,stackS,stackArgs.sub_right inner,
    xFit,yFit,domFit,randFit,sFit,bounds,domainLen,xLen,yLen,rLen,space⟩

end VG.Proof.Ffdh.Arm
