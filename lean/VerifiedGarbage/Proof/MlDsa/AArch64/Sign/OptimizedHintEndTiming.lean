import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintEnd
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseKCT

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem positiveOnesOk_tr {p : Params} {S : Nat} (hc : ksChk p=true)
    {t : Nat} {E : State → State → Prop} :
    RelCT isa (RootRS p S E (PositiveIH p S · t p.k)) (.block (onesOk p))
      (RootRS p S E (PositiveKO p S · t)) :=
  liftRootT (fun _ _ h=>⟨h.1.b.l.st,h.1.b.l.k.d.roots⟩)
    (fun _ _ _ h=>positiveOnesOk_ok hc h)
    (lrel_tr (fun _ _ h=>h.1) (onesOk_taint p))

end VG.Proof.MlDsa.AArch64.Sign
