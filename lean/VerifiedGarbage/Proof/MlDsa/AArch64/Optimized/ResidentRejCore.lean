import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdaptive
import VerifiedGarbage.Proof.Framework.RelCTAssoc

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

/-- Full selected four-stream front end, parameterized only by its final cleanup and ABI return. -/
theorem four_of_finish {σ : State} {Q : State → Prop} (hp : Pre 4 σ)
    (hfinish : ∀s,Done 4 σ s → WP isa
      (.seq Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.tailZeros
        (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
          Impl.MlDsa.AArch64.Sample.Rej4.epi))) s Q) :
    WP isa Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.code σ Q := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.code
  apply WP.seq
  refine WP.mono (startFour_ok hp) fun a ⟨ha,hpairs,hcounts⟩ => ?_
  apply WP.seq
  refine WP.mono (squeezeSetupZero_env ha) fun b ⟨hb,hm,h22,h23,hbuf⟩ => ?_
  apply WP.assoc
  apply WP.seq
  refine WP.mono (firstFour_ok hp hb (by simpa only [hm] using hpairs)
    (by simpa only [hm] using hcounts) h22 h23 hbuf) fun c hc => ?_
  apply WP.assoc
  apply WP.seq
  refine WP.mono (parseFiveFour_ok hp hc) fun d hd => ?_
  apply WP.seq
  refine WP.mono (flagsSemantic_ok hp hd) fun e ⟨he,hf⟩ => ?_
  apply WP.seq
  exact WP.mono (adaptiveFour_ok hp he hf) hfinish

/-- The two-stream front end has its own seed/output footprint and otherwise the same exact algorithm. -/
theorem two_of_finish {σ : State} {Q : State → Prop} (hp : Pre 2 σ)
    (hfinish : ∀s,Done 2 σ s → WP isa
      (.seq Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.tailZeros
        (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
          Impl.MlDsa.AArch64.Sample.Rej4.epi))) s Q) :
    WP isa Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code σ Q := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code
  apply WP.seq
  refine WP.mono (startTwo_ok hp) fun a ⟨ha,hpairs,hcounts⟩ => ?_
  apply WP.seq
  refine WP.mono (squeezeSetupZero_env ha) fun b ⟨hb,hm,h22,_,hbuf⟩ => ?_
  apply WP.seq
  refine WP.mono (firstTwo_ok hp hb (by simpa only [hm] using hpairs)
    (by simpa only [hm] using hcounts) h22 (fun k hk => hbuf k (by omega))) fun c hc => ?_
  apply WP.assoc
  apply WP.seq
  refine WP.mono (parseFiveTwo_ok hp hc) fun d hd => ?_
  apply WP.seq
  refine WP.mono (flagsSemantic_ok hp hd) fun e ⟨he,hf⟩ => ?_
  apply WP.seq
  exact WP.mono (adaptiveTwo_ok hp he hf) hfinish

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
