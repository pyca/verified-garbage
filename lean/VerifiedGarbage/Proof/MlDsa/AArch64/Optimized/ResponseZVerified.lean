import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZContract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa

theorem addNorm_contract_ct : ConstantTime isa addNormK.pre addNormK.pub
    VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm := by
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply addNorm_ct s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hp.2.2 ?_,by simp⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact hp.1
  · exact hp.2.1

def addNormSat : State where
  gpr r := if r=.x0 then 4096 else if r=.x1 then 8192 else if r=.x2 then 1 else 0
  sp := 65536
  mem _ := 0
  rd := [⟨8192,1024⟩]
  wr := [⟨4096,1024⟩]

theorem addNorm_verified : Verified target VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm
    (addNormContract abi) := by
  refine Verified.of_correct addNorm_correct addNorm_contract_ct ?_
  refine { pre := ?_,post := ?_,pub := ?_,sat := ?_ }
  · intro s h
    sig_pre [addNormContract,addNormSig,abi,argRegs] at h
    sig_split h
    exact ⟨by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,h⟩
  · sig_implies_post [addNormContract,addNormSig,addNormK,abi,argRegs]
  · sig_implies_pub [addNormContract,addNormSig,addNormK,abi,argRegs]
  · refine ⟨addNormSat,?_⟩
    sig_pre [addNormContract,addNormSig,abi,argRegs]
    sig_and_intros
    all_goals first
      | rfl
      | exact fun i _ => by rw [VG.Proof.MlDsa.AArch64.Pack.coeffAt_zero]; decide
      | exact Region.disjoint_of_sep (by decide)
      | decide

end VG.Proof.MlDsa.AArch64.Optimized.Response
