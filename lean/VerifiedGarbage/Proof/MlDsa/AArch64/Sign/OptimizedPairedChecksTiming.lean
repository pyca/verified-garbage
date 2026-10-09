import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedChecksCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedChecksPrefixTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedHintsTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintEndTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)

theorem positivePairedOnesOk_tr {p : Params} {S : Nat} (hc : ksChk p=true)
    (hS : S<2^64) {t : Nat} {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIH p S · t p.k)) (.block (onesOk p))
      (PairedRS p S E (PositiveKO p S · t)) :=
  liftPairedR (fun _ _ _ h roots=>WP.pairedRoots (positiveOnesOk_ok hc h) roots (Nat.zero_le _) hS)
    (RelCT.mono (positiveOnesOk_tr hc) (fun _ _ h=>h.root) (fun _ _ _=>trivial))

theorem positivePairedKBranch_tr {p : Params} {S : Nat} (hp : Ok3 p) (hc : ksChk p=true)
    (hS : S<2^64) {t : Nat} {E : State → State → Prop}
    (hE : ∀σ τ,E σ τ → (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ*t))).isSome →
      (sampleInBall p.τ maxBounds.ball (CTv p τ (p.ℓ*t))).isSome →
      (PassV p σ (p.ℓ*t) ↔ PassV p τ (p.ℓ*t))) :
    RelCT isa (PairedRS p S E (PositiveKO p S · t))
      (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (kapAdd p)))
      (PairedRS p S E fun σ s=>PositiveEP p S σ t s ∨ PositiveEF p S σ t s) :=
  liftPairedR (fun _ _ _ h roots=>WP.pairedRoots (positiveKBranch_ok hp hc h) roots (Nat.zero_le _) hS)
    (RelCT.mono (positiveKBranch_tr hp hc hE) (fun _ _ h=>h.root) (fun _ _ _=>trivial))

theorem positivePairedChecks_tr {p : Params} {S : Nat} (hp : Ok3 p) (hc : ksChk p=true)
    (h16 : 16≤S) (hS : S<2^64) {t : Nat} {E : State → State → Prop}
    (hE : ∀σ τ,E σ τ → (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ*t))).isSome →
      (sampleInBall p.τ maxBounds.ball (CTv p τ (p.ℓ*t))).isSome →
      (PassV p σ (p.ℓ*t) ↔ PassV p τ (p.ℓ*t))) :
    RelCT isa (PairedRS p S E fun σ s=>PositiveIB p S σ t s ∧ (s.gpr .x0).setWidth 32=1)
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)
      (PairedRS p S E fun σ s=>PositiveEP p S σ t s ∨ PositiveEF p S σ t s) := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks
  exact RelCT.seq (positivePairedChecksPrefix_tr hp hc h16)
    (RelCT.seq (optimizedHint_paired_vector_tr hp)
      (RelCT.seq (positivePairedOnesOk_tr hc hS) (positivePairedKBranch_tr hp hc hS hE)))

end VG.Proof.MlDsa.AArch64.Sign
