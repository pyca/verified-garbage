import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourContract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Verified

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa

theorem sampler_pre (η : Nat) : ∀s,(rejBoundedFourContract abi η).pre s → (samplerK η).pre s := by
  intro s h
  sig_pre [rejBoundedFourContract,rejBoundedFourSig,abi,argRegs] at h
  sig_split h
  exact ⟨h,by assumption,by assumption,by assumption,by assumption,by assumption⟩

def samplerSat : State where
 gpr r := if r=.x0 then 4096 else if r=.x1 then 8192 else if r=.x2 then 16384 else 0
 sp := 65536
 mem _ := 0
 rd := [⟨4096,264⟩]
 wr := [⟨8192,4096⟩,⟨16384,8192⟩]

theorem sampler_verified (sha3 : Bool) {η : Nat} (hη : η=2∨η=4) :
    Verified target (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η)
      (rejBoundedFourContract abi η) := by
  refine Verified.of_correct (sampler_correct sha3 η) (sampler_ct sha3 η)
    { pre := sampler_pre η,post := ?_,pub := ?_,sat := ?_ }
  · sig_implies_post [rejBoundedFourContract,rejBoundedFourSig,samplerK,
      samplerOut,samplerSeed,ResidentRej.aP,ResidentRej.seedP,abi,argRegs]
  · intro s t _ _ h
    sig_pub [rejBoundedFourContract,rejBoundedFourSig,abi,argRegs] at h
    obtain ⟨hsp,hl,h0,h1,h2⟩:=h
    exact ⟨⟨h2,h1,hsp⟩,h0,hl⟩
  · refine ⟨samplerSat,?_⟩
    sig_pre [rejBoundedFourContract,rejBoundedFourSig,abi,argRegs]
    sig_and_intros
    all_goals first | exact hη | rfl | exact Region.disjoint_of_sep (by decide) | decide

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
