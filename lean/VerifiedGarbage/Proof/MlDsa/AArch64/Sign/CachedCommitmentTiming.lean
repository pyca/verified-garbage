import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedHashSetupTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedCommitmentCorrect

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- The cached digest call preserves the original strict signing relation while
producing both the current commitment and the next attempt's tail mask. -/
theorem hash_root_tr {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} (hS : S<2^64) {E : State→State→Prop} {t : Nat} :
    RelCT isa (RootRS p S E (PositiveICh p S · t p.k))
      (Impl.MlDsa.AArch64.Sign.Cached.hash p)
      (RootRS p S E fun σ s=>PositiveIC p S σ t s ∧ Mask p σ (t+1) s) := by
  apply liftRootT (fun _ _ h=>⟨h.c.masks.l.st,h.c.masks.l.k.d.roots⟩)
    (fun _ _ _ h=>hash_ok hp hS h)
  exact RelCT.mono (hash_tr hp hS) (fun _ _ h=>h.1) (fun _ _ h=>h)

/-- Cached commitment timing uses only the public attempt index; cached mask and
hash contents remain secret throughout the unchanged signing schedule. -/
theorem commit_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87) {E : State→State→Prop} {t : Nat} :
    RelCT isa (RootRS p S E fun σ s=>PositiveIL p S σ t s ∧ (t=0 ∨ Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Cached.commit P p)
      (RootRS p S E fun σ s=>PositiveIC p S σ t s ∧ Mask p σ (t+1) s) := by
  have hp3 : Ok3 p := by
    rcases hp with h|h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  unfold Impl.MlDsa.AArch64.Sign.Cached.commit
  exact RelCT.seq (masks_tr hP hp) (RelCT.seq (positiveRows_tr hp3)
    (RelCT.seq (positivePackRows_tr hP hp3) (hash_root_tr hp (by have := hP.sl; omega))))

end VG.Proof.MlDsa.AArch64.Sign.Cached
