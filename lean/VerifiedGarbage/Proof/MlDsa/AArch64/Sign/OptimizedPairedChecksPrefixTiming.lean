import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedChecksPrefix

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (callAt)
open VG.Proof.MlDsa.AArch64.Optimized

theorem positivePairedChallenge_tr {p : Params} {S : Nat} (hp : Ok3 p) (h16 : 16≤S)
    {t : Nat} {E : State → State → Prop} :
    RelCT isa (PairedRS p S E fun σ s=>PositiveIB p S σ t s ∧ (s.gpr .x0).setWidth 32=1)
      (callAt "vg_mldsa_ntt_positive" Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt (positiveNttArgs cP))
      (PairedRS p S E (PositiveChallenge p S · t)) :=
  liftPairedR (fun _ _ _ h roots=>positivePairedChallenge_ok hp h16 roots h.1 h.2)
    (RelCT.mono (positiveChallenge_tr hp) (fun _ _ h=>h.root) (fun _ _ _=>trivial))

theorem positivePairedChecksInit_tr {p : Params} {S : Nat} (hp : Ok3 p) (hc : ksChk p=true)
    {t : Nat} {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveChallenge p S · t)) (.block kInit)
      (PairedRS p S E (PositiveIZ p S · t 0)) :=
  liftPairedR (fun _ _ _ h roots=>positivePairedChecksInit_ok hp hc roots h)
    (RelCT.mono (positiveChecksInit_tr hp hc) (fun _ _ h=>h.root) (fun _ _ _=>trivial))

theorem positivePairedChecksPrefix_tr {p : Params} {S : Nat} (hp : Ok3 p) (hc : ksChk p=true)
    (h16 : 16≤S) {t : Nat} {E : State → State → Prop} :
    RelCT isa (PairedRS p S E fun σ s=>PositiveIB p S σ t s ∧ (s.gpr .x0).setWidth 32=1)
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecksPrefix p)
      (PairedRS p S E (PositiveIH p S · t 0)) := by
  refine RelCT.seq (RelCT.seq (positivePairedChallenge_tr hp h16)
    (RelCT.seq (positivePairedChecksInit_tr hp hc) (optimizedZ_paired_vector_tr hp))) ?_
  exact RelCT.mono (optimizedR0_paired_vector_tr hp)
    (fun _ _ h=>h.mono (fun _ _ hz=>positiveIR_of_IZ hz))
    (fun _ _ h=>h.mono (fun _ _ hr=>positiveIH_of_IR hr))

end VG.Proof.MlDsa.AArch64.Sign
