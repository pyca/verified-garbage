import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksPrefix
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedR0Timing

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (callAt)
open VG.Proof.MlDsa.AArch64.Optimized

theorem positiveChallenge_tr {p : Params} {S : Nat} (hp : Ok3 p)
    {t : Nat} {E : State → State → Prop} :
    RelCT isa (RootRS p S E fun σ s=>PositiveIB p S σ t s ∧ (s.gpr .x0).setWidth 32=1)
      (callAt "vg_mldsa_ntt_positive" Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt
        (positiveNttArgs cP)) (RootRS p S E (PositiveChallenge p S · t)) := by
  refine liftRootR (fun _ _ _ h=>positiveChallenge_ok hp h.1 h.2) ?_
  have hc := positiveChallengeChk_ok hp
  simp only [positiveChallengeChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hr,hw⟩,_⟩,_⟩ := hc
  apply positiveNttAt_tr (S := S) (ptr_ok (by decide))
  intro x y h
  obtain ⟨σ,τ,_,_,pub,_,hx,hy⟩ := h.1
  have L := lrel_of pub hx.1.c.masks.l.st hy.1.c.masks.l.st
  have ready (σ s : State) (hs : PositiveIB p S σ t s) (h1 : (s.gpr .x0).setWidth 32=1) :
      NttCallReady cP s := by
    have ls := hs.c.masks.l.st.lay
    have roots := hs.c.masks.l.k.d.roots
    exact ⟨ls.nwp hr,roots.nttTableAt (ls.inW hw),(hs.ok h1).1.1,
      Covers.cons roots.forward.readable (ls.cR hr),ls.cW hw⟩
  exact ⟨ready σ x hx.1 hx.2,ready τ y hy.1 hy.2,L.pa (by decide),L.sp,h.2.1⟩

theorem positiveChecksPrefix_tr {p : Params} {S : Nat} (hp : Ok3 p) (hc : ksChk p=true)
    {t : Nat} {E : State → State → Prop} :
    RelCT isa (RootRS p S E fun σ s=>PositiveIB p S σ t s ∧ (s.gpr .x0).setWidth 32=1)
      (Impl.MlDsa.AArch64.Sign.Optimized.checksPrefix p)
      (RootRS p S E (PositiveIH p S · t 0)) := by
  refine RelCT.seq (RelCT.seq (positiveChallenge_tr hp)
    (RelCT.seq (positiveChecksInit_tr hp hc) (optimizedZ_vector_tr hp))) ?_
  exact RelCT.mono (optimizedR0_vector_tr hp)
    (fun _ _ h=>h.mono (fun _ _ hz=>positiveIR_of_IZ hz))
    (fun _ _ h=>h.mono (fun _ _ hr=>positiveIH_of_IR hr))

end VG.Proof.MlDsa.AArch64.Sign
