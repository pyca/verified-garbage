module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInput
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsBytes
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract

/-! The reviewed precomputation signature supplies native buffers and frames. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm VG.Proof.Mont

theorem combPrecompute_input (s : State)
    (pre : (Spec.Ffdh.generationPrecomputeContract (abi.withConsts VG.Impl.Ffdh.Arm.VettedGroups.tableConsts) 176).pre s)
    {p : Inputs}
    (base : stackArg s 1 = p.base) (output : s.gpr .r0 = p.output)
    (domain : s.gpr .r2 = p.domain) (count : (stackArg s 0).toNat = p.k)
    (capacity : (stackArg s 2).toNat = p.len)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r3).toNat = p.dom)
    (privateAlias : p.privateValue = p.output) (publicAlias : p.publicValue = p.output)
    (entropyAlias : p.entropy = p.output)
    (environment : VettedGroups.environment.holds p (entered s)) :
    CombPrecomputeFnInput p s := by
  obtain ⟨pre,hc⟩ := pre_consts.mp pre
  sig_pre [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  simp only [show ∀ (K : List (String × List (BitVec 64))) (s : State) (i : Nat), stackArg (stripConsts K s) i = stackArg s i by intros; rfl] at pre
  simp only [show ∀ (K : List (String × List (BitVec 64))) (s : State) (i : Nat), stackArgAddr (stripConsts K s) i = stackArgAddr s i by intros; rfl] at pre
  obtain ⟨stackFit,argFit,rd,wr,outDom,outWs,outArgs,domWs,wsArgs,
    stackOut,stackDom,stackWs,stackArgs,outFit,domFit,wsFit,_,_,ctxLen,_,valid⟩ := pre
  have rdFull : s.rd = [⟨BitVec.setWidth 64 (s.gpr .r2),(s.gpr .r3).toNat⟩,⟨stackArgAddr s 0,12⟩] ++ constRegs VG.Impl.Ffdh.Arm.VettedGroups.tableConsts s := by
    have drop : s.rd.drop (s.rd.length - 1) = constRegs VG.Impl.Ffdh.Arm.VettedGroups.tableConsts s := hc.1
    rw [←List.take_append_drop (s.rd.length - 1) s.rd,drop]
    exact congrArg (· ++ constRegs VG.Impl.Ffdh.Arm.VettedGroups.tableConsts s) rd
  clear rd
  have rd := rdFull
  have domLen : (s.gpr .r3).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  rw [count] at ctxLen valid
  simp only [output,ctxLen,domain,domLen,base,capacity,Nat.mul_comm p.len 8] at rd wr outDom outWs outArgs domWs wsArgs stackOut stackDom stackWs outFit domFit wsFit
  rw [domain] at valid
  change Spec.Ffdh.domainValid p.k (Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r3).toNat) = true at valid
  rw [domainBytes] at valid
  have bytes : Spec.Ffdh.generationPrecomputedWords p.k * 8 = CombBuilder.bytes p := by simp [CombBuilder.bytes,Nat.mul_comm]
  rw [bytes] at wr outDom outWs outArgs stackOut outFit
  have reserved : (⟨State.addr s.sp - BitVec.ofNat 64 176,176⟩ : Region) = belowA s.sp 176 := by
    rw [belowA,addr_sub' stackFit]
  simp only [State.addr] at reserved
  rw [reserved] at stackOut stackDom stackWs stackArgs
  have inner : (belowA s.sp 128).Sub (belowA s.sp 176) := belowA_sub (by decide) stackFit
  have fit128 : 128 ≤ s.sp.toNat := by omega
  have ws : Workspace s p.base (8*p.len) := ⟨wsFit,by rw [wr]; simp [State.addr]⟩
  have domRead : InRegions (s.rd ++ s.wr) (State.addr p.domain) p.dom.length :=
    ⟨_,List.mem_append_left _ (by rw [rd]; simp [State.addr]),Region.contains_self _ _⟩
  have domOctets : Octets p.base p.domain p.len p.dom s :=
    ⟨domFit,domRead,domWs,by rw [←domLen]; exact domainBytes⟩
  have args : ArgumentMemory p [] (entered s) :=
    ⟨entered_workspace ws,entered_locals s fit128 (stackWs.sub_left inner),
      entered_octets domOctets fit128 (stackDom.sub_left inner),
      stackDom.symm.sub_right (fun a h => inner a (locals_sub_reserved s fit128 a h)),by simp⟩
  have outSize : p.k ≤ CombBuilder.bytes p := by
    have small := p.width.2.2.2.1
    change p.k ≤ 8 * p.w at small
    simp only [CombBuilder.bytes,Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,Spec.Rsa.precomputedWords,Spec.Rsa.FixedBaseComb.entries]
    change p.k ≤ 8 * (3 + (2*p.w + 32*p.w))
    omega
  have outSub : (⟨State.addr p.output,p.k⟩ : Region).Sub ⟨State.addr p.output,CombBuilder.bytes p⟩ := by
    simpa only [off,BitVec.add_zero] using
      (Offset.sub_base (State.addr p.output) (d := 0) (n := p.k) (k := CombBuilder.bytes p) (by omega))
  have callSep : (⟨State.addr p.output,CombBuilder.bytes p⟩ : Region).Disjoint (belowA (entered s).sp 48) := by
    rw [entered_sp]
    exact stackOut.symm.sub_right (belowA_inner (a := 48) (k := 128) (by decide) stackFit)
  have calls : KeyCallMemory p (entered s) := KeyCallMemory.of_outer stackFit (entered_sp s) stackWs stackDom.symm
    (by rw [privateAlias]; exact (stackOut.symm.sub_left outSub))
    (by rw [publicAlias]; exact (stackOut.symm.sub_left outSub))
    (by rw [entropyAlias]; exact (stackOut.symm.sub_left outSub))
    (by rw [privateAlias]; omega)
  have incoming (i : Nat) (hi : i < 3) : IncomingWord (stackArg s i) (128+4*i) (entered s) := by
    have start : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
    have addr : stackArgAddr s i = off (State.addr s.sp) (4*i) := addr_add (by omega)
    have sub : (⟨stackArgAddr s i,4⟩ : Region).Sub ⟨stackArgAddr s 0,12⟩ := by
      rw [start,addr]; exact Offset.sub_base _ (by omega)
    refine enteredIncoming s fit128 (by omega) ?_ (stackArgs.sub_left inner |>.sub_right sub) rfl
    refine ⟨⟨stackArgAddr s 0,12⟩,List.mem_append_left _ (by rw [rd]; simp),?_⟩
    rw [start,addr]; exact Offset.contains_base _ (by omega) (by omega)
  refine ⟨stackFit,args,?_,?_,output,domain,?_,calls,?_,outWs.symm,outDom.symm,?_,callSep,valid,environment,?_⟩
  · have h := incoming 0 (by decide)
    have eq : stackArg s 0 = BitVec.ofNat 32 p.k := by rw [←count,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    simpa only [Nat.mul_zero,Nat.add_zero,eq] using h
  · simpa only [Nat.mul_one,base] using incoming 1 (by decide)
  · rw [←domLen,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · refine ⟨outFit,?_⟩
    exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by rw [wr]; simp [State.addr])),Region.contains_self _ _⟩
  · exact stackOut.sub_left (fun a h => inner a (locals_sub_reserved s fit128 a h))
  · intro r hr
    simp only [combPrecomputeWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact stackWs.sub_left (fun a h => inner a (saved_sub_reserved s fit128 a h))
    · exact stackOut.sub_left (fun a h => inner a (saved_sub_reserved s fit128 a h))
    · exact saved_separate_locals s fit128
    · have shifted : (pcPushed s).sp = (entered s).sp + BitVec.ofNat 32 72 := (BitVec.sub_add_cancel _ _).symm
      have fit : (entered s).sp.toNat + 72 < 2^32 := by rw [entered_nat s fit128]; have := s.sp.isLt; omega
      rw [shifted,VG.Arm.addr_add fit,belowA,addr_sub' calls.stack.fit]
      exact (Offset.disjoint_below_above _ (m:=48) (a:=72) (l:=56) (by decide)).symm


end VG.Proof.Ffdh.Arm
