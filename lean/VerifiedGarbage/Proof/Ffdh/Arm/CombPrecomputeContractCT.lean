module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCTState
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedBoundInstance
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeFnCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeData
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeEnvironment
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsEnvironment
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputePre

/-! The cached-context writer depends only on public domain bytes and addresses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts tableSym tableWords)

theorem combPrecompute_contract_ct (backend : MontBackend)
    (mainTiming : ∀ {p : Inputs} {sp : BitVec 32}, Spec.Ffdh.domainValid p.k p.dom=true →
      RelCT isa (fun s t=>CombBuilder.EnterInput p sp s ∧ CombBuilder.EnterInput p sp t ∧
        VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
        (VG.Impl.Ffdh.Arm.CombPrecompute.main
          (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VettedBound.code) (fun _ _=>True)) :
    ConstantTime isa (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts) 176).pre
      (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts) 176).pub
      (VG.Impl.Ffdh.Arm.CombPrecompute.code
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VettedBound.code) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p,base,output,domain,count,capacity,domainBytes,_words,privateAlias,publicAlias,entropyAlias,inputS⟩ :=
    combPrecompute_data s hs
  have symbol := VettedGroups.consts_singleton_symEq (name:=tableSym) (words:=tableWords) (pub_consts.mp hp).2
  have hp := (pub_consts.mp hp).1
  sig_pub [Spec.Ffdh.generationPrecomputeContract,Spec.Ffdh.generationPrecomputeSig,
    abi,argRegs,reduceClassify,Loc.val,State.addr] at hp
  obtain ⟨sp,bytes,p0,_p1,p2,p3,p4,p5,p6⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map,Function.comp_def,BitVec.ofNat_toNat,BitVec.setWidth_eq,List.map_id'] at byteEq
  rw [←p2,←p3] at byteEq
  have environmentT := combPrecompute_environment t ht (p5.symm.trans base) (p0.symm.trans output)
    (by rw [←p6]; exact capacity) (by rw [←p4]; exact count) privateAlias publicAlias
  have inputT := combPrecompute_input t ht (p:=p) (p5.symm.trans base) (p0.symm.trans output)
    (p2.symm.trans domain) (by rw [←p4]; exact count) (by rw [←p6]; exact capacity)
    ?_ privateAlias publicAlias entropyAlias environmentT
  · exact (combPrecomputeFn_ct backend (mainTiming inputS.valid) s t tr1 tr2 u v ⟨inputS,inputT,symbol,sp⟩ e1 e2).1
  · rw [←p3,←domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r2)) (s.gpr .r3).toNat=p.dom
    rw [←byteEq,domain]
    exact domainBytes

end VG.Proof.Ffdh.Arm
