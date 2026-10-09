import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksEnd
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopEnd
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseLCT

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)

theorem positiveChecksInit_tr {p : Params} {S : Nat} (hp : Ok3 p) (hc : ksChk p=true)
    {t : Nat} {E : State → State → Prop} :
    RelCT isa (RootRS p S E (PositiveChallenge p S · t)) (.block kInit)
      (RootRS p S E (PositiveIZ p S · t 0)) :=
  liftRootT (fun _ _ h=>⟨h.c.masks.l.st,h.c.masks.l.k.d.roots⟩)
    (fun _ _ _ h=>positiveChecksInit_ok hp hc h)
    (lrel_tr (fun _ _ h=>h.1) (by taint_decide))

theorem positiveKBranch_tr {p : Params} {S : Nat} (hp : Ok3 p) (hc : ksChk p=true)
    {t : Nat} {E : State → State → Prop}
    (hE : ∀σ τ,E σ τ → (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ*t))).isSome →
      (sampleInBall p.τ maxBounds.ball (CTv p τ (p.ℓ*t))).isSome →
      (PassV p σ (p.ℓ*t) ↔ PassV p τ (p.ℓ*t))) :
    RelCT isa (RootRS p S E (PositiveKO p S · t))
      (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (kapAdd p)))
      (RootRS p S E fun σ s=>PositiveEP p S σ t s ∨ PositiveEF p S σ t s) := by
  refine liftRootR (fun _ _ _ h=>positiveKBranch_ok hp hc h) ?_
  unfold ifOkElse
  refine RelCT.ite ?_ ?_ ?_
  · intro x y h
    obtain ⟨σ,τ,_,_,_,he,hx,hy⟩ := h.1
    have hv : x.gpr .x24=y.gpr .x24 := by
      rw [hx.x24,hy.x24]
      exact bit_congr (hE σ τ he hx.b.sampled hy.b.sampled)
    change some ((x.gpr .x24).setWidth 32 != 0) = some ((y.gpr .x24).setWidth 32 != 0)
    rw [hv]
  · exact lrel_tr (fun _ _ h=>h.1.1.lrel (fun _ _ h=>h.b.l.st)) (by taint_decide)
  · exact lrel_tr (fun _ _ h=>h.1.1.lrel (fun _ _ h=>h.b.l.st)) (kapAdd_taint p)

theorem positiveBallFailure_tr {p : Params} {S : Nat} (hp : Ok3 p) (hc : lChk p=true)
    {t : Nat} {E : State → State → Prop} :
    RelCT isa (RootRS p S E fun σ s=>PositiveIB p S σ t s ∧ (s.gpr .x0).setWidth 32=0)
      (.block (([.movz .x .x24 0 0] : List Instr)++setQ (sc oCNT) 1))
      (RootRS p S E (PositiveEB p S · t)) :=
  liftRootT (fun _ _ h=>⟨h.1.c.masks.l.st,h.1.c.masks.l.k.d.roots⟩)
    (fun _ _ _ h=>positiveBallFailure_ok hp hc h.1 h.2)
    (lrel_tr (fun _ _ h=>h.1) (by taint_decide))

end VG.Proof.MlDsa.AArch64.Sign
