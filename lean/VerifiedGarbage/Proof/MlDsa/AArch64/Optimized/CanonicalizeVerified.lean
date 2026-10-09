import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeContract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith (polyRegion)

theorem canonicalize_contract_ct : ConstantTime isa canonicalizeK.pre canonicalizeK.pub
    VG.Impl.MlDsa.AArch64.Optimized.Response.canonicalize := by
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply canonicalize_ct s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hp.2 ?_,by simp⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact hp.1

def canonicalizeSat : State where
  gpr _ := 0x1000
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := [⟨0x1000,1024⟩]

theorem canonicalize_verified : Verified target VG.Impl.MlDsa.AArch64.Optimized.Response.canonicalize
    (canonicalizeContract abi) := by
  refine Verified.of_correct canonicalize_correct canonicalize_contract_ct ?_
  refine { pre := ?_,post := ?_,pub := ?_,sat := ?_ }
  · intro s h
    sig_pre [canonicalizeContract,canonicalizeSig,abi,argRegs] at h
    sig_split h
    change s.wr=[polyRegion (s.gpr .x0)] ∧ CenteredReduced s.mem (s.gpr .x0)
    exact ⟨by assumption,h⟩
  · sig_implies_post [canonicalizeContract,canonicalizeSig,canonicalizeK,abi,argRegs]
  · sig_implies_pub [canonicalizeContract,canonicalizeSig,canonicalizeK,abi,argRegs]
  · refine ⟨canonicalizeSat,?_⟩
    sig_pre [canonicalizeContract,canonicalizeSig,abi,argRegs]
    sig_and_intros
    all_goals first
      | rfl
      | exact fun i _ => by rw [VG.Proof.MlDsa.AArch64.Pack.coeffAt_zero]; decide
      | decide

end VG.Proof.MlDsa.AArch64.Optimized.Response
