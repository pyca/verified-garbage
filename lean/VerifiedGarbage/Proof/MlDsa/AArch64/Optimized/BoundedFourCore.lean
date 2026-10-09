import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourFinish

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample

def sampledRows (σ : State) (η : Nat) (i : Nat) : List Zq :=
 rbFold η (rbFold η [] (chunkBytes (samplerA σ i)))
  (chunkBytes (Resident.permuted (samplerA σ i) 2))

theorem wp_seq_assoc {a b c : Prog isa} {s : State} {Q : State→Prop} :
    WP isa (.seq a (.seq b c)) s Q↔WP isa (.seq (.seq a b) c) s Q := by
  simp only [WP.seq_iff (M := isa)]

theorem sampler_machine_ok (sha3 : Bool) {η : Nat} (hη : η=2∨η=4) {σ : State}
    (hp : SamplerPre σ) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η) σ
      (fun t=>Result σ t (sampledRows σ η)) := by
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler
  change WP isa (.seq (.block samplerSetup) _) σ _
  refine WP.seq (WP.mono (samplerSetup_ok hp) fun a ha=>?_)
  rw [wp_seq_assoc]
  refine WP.seq (WP.mono (sampleRound_ok sha3 hη hp ha.running (by decide : 0≤272)) fun b hb=>?_)
  refine WP.seq (WP.mono (flagsStage_ok hp hb) fun c ⟨hc,hflag⟩=>?_)
  change WP isa (.seq (secondBatch sha3 η) _) c _
  refine WP.seq (WP.mono (secondBatch_ok sha3 hη hp hc hflag) fun d ⟨A,hd,hdf⟩=>?_)
  change WP isa (.seq maskFour _) d _
  refine WP.seq (WP.mono (maskStage_ok hp hd hdf) fun e he=>?_)
  exact finish_ok hp he

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
