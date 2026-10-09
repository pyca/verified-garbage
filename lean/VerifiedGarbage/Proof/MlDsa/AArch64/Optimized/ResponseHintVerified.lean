import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintCorrect
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Arith

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

def hintNormSat : State where
  gpr r := match r with
    | .x0 => 4096 | .x1 => 8192 | .x2 => 12288 | .x3 => 95232 | _ => 0
  sp := 65536
  mem _ := 0
  rd := [⟨8192,1024⟩,⟨12288,1024⟩]
  wr := [⟨4096,1024⟩]

theorem responseDecomposed_zero (p h : Addr) : ResponseDecomposed (fun _ => 0) p h 95232 := by
  intro i hi
  simp only [responseHintBase,VG.Proof.MlDsa.AArch64.Pack.coeffAt_zero]
  decide

theorem hintNorm_verified : Verified target Impl.MlDsa.AArch64.Optimized.Response.hintNorm
    (hintNormContract abi) := by
  refine Verified.of_correct hintNorm_correct hintNorm_contract_ct ?_
  refine { pre := ?_,post := ?_,pub := ?_,sat := ?_ }
  · intro s h
    sig_pre [hintNormContract,hintNormSig,abi,argRegs] at h
    sig_split h
    refine ⟨by assumption,by assumption,?_,?_,?_,by assumption,h⟩
    · with_reducible assumption
    · with_reducible assumption
    · exact isG_of_mem (by assumption)
  · sig_implies_post [hintNormContract,hintNormSig,hintNormK,arg32,abi,argRegs]
  · sig_implies_pub [hintNormContract,hintNormSig,hintNormK,abi,argRegs]
  · refine ⟨hintNormSat,?_⟩
    sig_pre [hintNormContract,hintNormSig,abi,argRegs]
    sig_and_intros
    all_goals first
      | rfl
      | exact responseDecomposed_zero _ _
      | exact fun i _ => by rw [VG.Proof.MlDsa.AArch64.Pack.coeffAt_zero]; decide
      | exact Region.disjoint_of_sep (by decide)
      | decide

end VG.Proof.MlDsa.AArch64.Optimized.Response
