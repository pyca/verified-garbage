import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowContract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Arith

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

def subLowNormSat : State where
  gpr r := match r with
    | .x0 => 4096 | .x1 => 8192 | .x2 => 12288 | .x3 => 95232 | .x4 => 1 | _ => 0
  sp := 65536
  mem _ := 0
  rd := [⟨8192,1024⟩]
  wr := [⟨4096,1024⟩,⟨12288,1024⟩]

theorem subLowNorm_verified : Verified target VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm
    (subLowNormContract abi) := by
  refine Verified.of_correct subLowNorm_correct subLowNorm_contract_ct ?_
  refine { pre := ?_,post := ?_,pub := ?_,sat := ?_ }
  · intro s h
    sig_pre [subLowNormContract,subLowNormSig,abi,argRegs] at h
    sig_split h
    refine ⟨by assumption,by assumption,by assumption,?_,?_,by assumption,by assumption,?_,by assumption,h⟩
    · exact Region.Disjoint.symm (by assumption)
    · with_reducible assumption
    · exact isG_of_mem (by assumption)
  · sig_implies_post [subLowNormContract,subLowNormSig,subLowNormK,arg32,abi,argRegs]
  · sig_implies_pub [subLowNormContract,subLowNormSig,subLowNormK,abi,argRegs]
  · refine ⟨subLowNormSat,?_⟩
    sig_pre [subLowNormContract,subLowNormSig,abi,argRegs]
    sig_and_intros
    all_goals first
      | rfl
      | exact fun i _ => by rw [VG.Proof.MlDsa.AArch64.Pack.coeffAt_zero]; decide
      | exact Region.disjoint_of_sep (by decide)
      | decide

end VG.Proof.MlDsa.AArch64.Optimized.Response
