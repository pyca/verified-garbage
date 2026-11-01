module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.Fn
public import VerifiedGarbage.Spec.Gcm.OutOfPlace
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.Verified
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Gather.Verified
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval

-- separate module: the gather caller reserves the split-seal call's deeper frame.
/-! # The split gather caller's stack and buffer layout -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.GatherSplit
open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE.Gather
open VG.Proof.ChaCha20Poly1305.PPC64LE.Gather (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)


def contract : Contract isa := Spec.Gcm.sealGatherContract PPC64LE.abi 2960

structure Layout (s : State) : Prop where
  base : Gather.Lay s
  stack : ∀ r∈[cR s,nR s,aR s,dsR s]++lsR s++[dR s,tgR s,argR s], (below s.sp 2960).Disjoint r
  space : 2960≤s.sp.toNat


theorem layout_pre {s : State} (h : contract.pre s) : Layout s := by
  sig_pre [contract,Spec.Gcm.sealGatherContract,Spec.Gcm.sealGatherSig,Spec.Gcm.sealGatherPre,PPC64LE.abi,
    PPC64LE.argRegs,Gather.stackArgs_three,List.append_eq] at h
  simp only [List.map_append,List.filter_append,List.filter_map,List.map_map,List.filterMap_append,
    List.filterMap_map,List.map_cons,List.map_nil,List.filter_cons,List.filter_nil,Function.comp_def,
    Bool.not_false,Bool.false_eq_true,ite_true,ite_false,filter_true',filter_false',filterMap_some',
    filterMap_none',List.map_id',Sig.conj_cons,Sig.conj_append,Sig.conj_map,Bool.cond_false,Bool.cond_true,
    List.filterMap_cons,List.filterMap_nil,List.append_nil,List.nil_append,Sig.conj,Bool.true_or,
    List.cons_append,Sig.pairFacts] at h
  rw [pairFacts_ro _ (by simp)] at h
  obtain ⟨w₁,w₂,rd,wr,⟨cd,ct,nd,nt,ad,at_,dt,dds,⟨dl,da⟩,tds,⟨tl,ta⟩,-⟩,
    bc,bn,ba,bd,bt,⟨bds,bl,barg⟩,oc,on,oa,od,ot,⟨ods,ol⟩,hR,hg⟩ := h
  have hb : Region.Sub (stkR s) (below s.sp 2960) := below_sub (by decide) (by decide)
  have hp : gatherPre s :=
    ⟨by rw [rd]; simp,wr,cd,ct,nd,nt,ad,at_,dds.symm,tds.symm,
      fun r hr => ⟨(dl r hr).symm,(tl r hr).symm⟩,dt,da,ta,
      bc.sub_left hb,bn.sub_left hb,ba.sub_left hb,bds.sub_left hb,
      fun r hr => (bl r hr).sub_left hb,barg.sub_left hb,bd.sub_left hb,bt.sub_left hb,
      oc,on,oa,ods,ol,od,ot,by omega,by omega,hR,hg⟩
  refine ⟨Gather.lay hp,?_,w₁⟩
  intro r hr
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl) | hr) | (rfl | rfl | rfl)
  exacts [bc,bn,ba,bds,bl r hr,bd,bt,barg]

end VG.Proof.AesGcm.PPC64LE.GatherSplit
