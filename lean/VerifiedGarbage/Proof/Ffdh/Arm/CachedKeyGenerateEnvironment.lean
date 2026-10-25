module

public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! The canonical immutable context survives the cached attempt's entry frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm VG.Proof.Mont

theorem cachedKeyGenerate_environment (s : State)
    (pre : (Spec.Ffdh.cachedGenerateKeyContract abi 176).pre s) {p : Inputs}
    (base : stackArg s 5=p.base) (privateValue : s.gpr .r0=p.privateValue)
    (publicValue : s.gpr .r2=p.publicValue) (domain : stackArg s 0=p.domain)
    (count : (stackArg s 2).toNat=p.k) (capacity : (stackArg s 6).toNat=p.len)
    (cache : stackArg s 7=p.cachedContext) (cacheWords : (stackArg s 8).toNat=p.cachedWords)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat=p.dom) :
    CachedGenerationContext p (entered s) ∧ Spec.Ffdh.domainValid p.k p.dom=true := by
  sig_pre [Spec.Ffdh.cachedGenerateKeyContract,Spec.Ffdh.cachedGenerateKeySig,Spec.Ffdh.generateKeySig,
    abi,argRegs,reduceClassify,Loc.val,State.addr] at pre
  obtain ⟨stackFit,argFit,rd,wr,_xY,_xDom,_xRand,xS,xCtx,_xArgs,_yDom,_yRand,yS,yCtx,_yArgs,
    _domS,_randS,sCtx,_sArgs,_stackX,_stackY,_stackDom,_stackRand,stackS,stackCtx,_stackArgs,
    _xFit,_yFit,_domFit,_randFit,_sFit,ctxFit,_bounds,_domainLen,xLen,yLen,_rLen,_space,valid,canonical⟩ := pre
  have frame := entered_frame s (by omega_arith)
  have size : p.cachedContext.toNat+8*p.cachedWords ≤ 2^32 := by rw [←cache,←cacheWords]; omega_arith
  have stackSep : (cachedRegion p).Disjoint (belowA s.sp 176) := by
    unfold cachedRegion
    rw [belowA,addr_sub' stackFit]
    simpa only [←cache,←cacheWords,State.addr,Nat.mul_comm 8] using stackCtx.symm
  have savedSub : (⟨State.addr (pcPushed s).sp,56⟩ : Region).Sub (belowA s.sp 176) :=
    fun a h => belowA_sub (by decide) stackFit a (saved_sub_reserved s (by omega_arith) a h)
  have words : Spec.Rsa.wordsAt (entered s).mem (State.addr p.cachedContext) p.cachedWords =
      Spec.Rsa.wordsAt s.mem (State.addr p.cachedContext) p.cachedWords := by
    unfold Spec.Rsa.wordsAt
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    apply frame.readW (r:=cachedRegion p) _ ?_ (by decide)
    · simp only [cachedRegion,Region.Contains,Offset.add_sub_cancel_left,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega_arith : 8*i<2^64)]
      omega_arith
    · intro r hr
      have eq := List.mem_singleton.mp hr
      subst r
      exact stackSep.sub_right savedSub
  have validP : Spec.Ffdh.domainValid p.k p.dom=true := by
    change Spec.Ffdh.domainValid (stackArg s 2).toNat
      (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)=true at valid
    rw [count,domain,domainBytes] at valid
    exact valid
  refine ⟨⟨?_,validP,size,?_,?_⟩,validP⟩
  · unfold Spec.Ffdh.generationContextAt
    rw [words]
    change Spec.Ffdh.generationContextAt s.mem (State.addr (stackArg s 7))
      (stackArg s 8).toNat (stackArg s 2).toNat
      (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat) at canonical
    simpa only [Spec.Ffdh.generationContextAt,cache,cacheWords,count,domain,domainBytes] using canonical
  · apply entered_read
    refine ⟨⟨State.addr p.cachedContext,8*p.cachedWords⟩,List.mem_append_left _ ?_,Region.contains_self _ _⟩
    rw [rd]
    simp only [cache,cacheWords,State.addr,Nat.mul_comm 8,List.mem_cons]
    simp
  · intro r hr
    simp only [keyCallWrites,keyWrites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with (rfl|rfl|rfl|rfl)|rfl
    · simpa only [cachedRegion,←cache,←cacheWords,←base,←capacity,Nat.mul_comm 8,State.addr] using sCtx.symm
    · exact stackSep.sub_right (fun a h => belowA_sub (by decide) stackFit a (locals_sub_reserved s (by omega_arith) a h))
    · simpa only [cachedRegion,←cache,←cacheWords,←privateValue,←count,←xLen,Nat.mul_comm 8,State.addr] using xCtx.symm
    · simpa only [cachedRegion,←cache,←cacheWords,←publicValue,←count,←yLen,Nat.mul_comm 8,State.addr] using yCtx.symm
    · rw [entered_sp]
      exact stackSep.sub_right (belowA_inner (a:=48) (k:=128) (by decide) stackFit)

end VG.Proof.Ffdh.Arm
