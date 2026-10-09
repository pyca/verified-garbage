import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotSat

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.DotInverse
open VG.Impl.MlDsa.AArch64.Optimized.Inverse (inverseConsts)

/-- The selected fused dot/inverse kernels have canonical output and positive-lazy inputs. -/
theorem dot_verified {count : Nat} (hc : count=4 ∨ count=5 ∨ count=7) :
    Verified target (staticCode count) (dotInverseContract count (abi.withConsts inverseConsts)) := by
  refine Verified.of_correct (dot_correct (by omega) (by omega)) (dot_ct hc)
    { pre := fun _ h => dot_pre h, post := ?_, pub := ?_, sat := ⟨dotSat count,dot_sat count (by omega)⟩ }
  · intro s t _ h
    sig_post [dotInverseContract,dotInverseSig,abi,argRegs,Abi.withConsts,inverseConsts_eq]
    exact h
  · intro s t _ _ h
    exact dot_pub h

theorem dot4_verified : Verified target (staticCode 4)
    (dotInverseContract 4 (abi.withConsts inverseConsts)) := dot_verified (Or.inl rfl)

theorem dot5_verified : Verified target (staticCode 5)
    (dotInverseContract 5 (abi.withConsts inverseConsts)) := dot_verified (Or.inr (Or.inl rfl))

theorem dot7_verified : Verified target (staticCode 7)
    (dotInverseContract 7 (abi.withConsts inverseConsts)) := dot_verified (Or.inr (Or.inr rfl))

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
