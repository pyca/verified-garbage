import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedInitialization
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDecodeTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

/-- The secret-vector transforms and mask-seed hash keep the original
initialization trace policy, adding only public static-table addresses. -/
theorem positiveInitialization_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {E : State → State → Prop} :
    RelCT isa (RootRS p S E (fun σ s => IM p S σ s ∧ StaticRoots S s))
      (positiveDecodeWith keccak.callee P p) (RootRS p S E (PositiveIK p S)) := by
  unfold positiveDecodeWith
  refine RelCT.seq (R := RootRS p S E (PositiveID p S · p.ℓ p.k p.k)) ?_ ?_
  · apply RelCT.mono (positiveDecodeSecrets_tr hP (dChk_ok hp))
    · intro x y h
      exact ⟨h.1.mono (fun _ _ h => h) (fun _ _ h =>
        ⟨h.1,h.2,by simp [PosFam],by simp [PosFam],by simp [PosFam]⟩),h.2⟩
    · intro _ _ h; exact h
  · apply liftRootT (fun _ _ h => ⟨h.im.st,h.roots⟩)
      (fun _ _ _ h => positiveSeed_ok hP hp h)
    exact vector_lrel_tr (fun _ _ h => h.1) keccak.mldsaSignDecodeTaint.choose_spec

end VG.Proof.MlDsa.AArch64.Sign
