import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSeed

/-! ## From `BoundedFourCore.lean` -/

section

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

end

/-! ## From `BoundedFourShake.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlDsa.Sample

theorem permuted_add (A : Spec.Sha3.State) (i j : Nat) :
    Resident.permuted (Resident.permuted A i) j=Resident.permuted A (i+j) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Resident.permuted,ih]; rfl

theorem chunks_squeeze (A : Spec.Sha3.State) :
    chunkBytes A++chunkBytes (Resident.permuted A 2)=
      Spec.Sha3.squeezeBlocks 136 (Spec.Sha3.keccakF A) 4 := by
  apply List.ext_getElem
  · rw [List.length_append,chunkBytes_length,chunkBytes_length,
      VG.Proof.Sha3.length_squeezeBlocks (by decide)]
  · intro j hj hj'
    have hj544 : j<544:=by simpa only [List.length_append,chunkBytes_length] using hj
    rw [VG.Proof.Sha3.getElem_squeezeBlocks (by decide) (by decide),
      VG.Proof.Sha3.iterF_keccakF,←Resident.permuted_eq_iterF]
    by_cases h : j<272
    · rw [List.getElem_append_left (by simpa only [chunkBytes_length] using h)]
      simpa only [getElem!_pos (chunkBytes A) j (by rw [chunkBytes_length]; exact h)] using chunkBytes_get A h
    · rw [List.getElem_append_right (by simpa only [chunkBytes_length] using (by omega : 272≤j))]
      simp only [chunkBytes_length]
      rw [←getElem!_pos (chunkBytes (Resident.permuted A 2)) (j-272) (by rw [chunkBytes_length]; omega),
        chunkBytes_get _ (by omega),permuted_add]
      have hd : 2+((j-272)/136+1)=j/136+1:=by omega
      have hm : (j-272)%136=j%136:=by omega
      rw [hd,hm]

theorem chunks_H (m : Mem) (p : Addr) :
    chunkBytes (ResidentMask.seedState m p)++
      chunkBytes (Resident.permuted (ResidentMask.seedState m p) 2)=
      Spec.MlDsa.H (Spec.Sha3.bytesAt m p 66) 544 := by
  rw [chunks_squeeze,ResidentMask.seedState_eq]
  change _=Spec.Sha3.squeeze 136
    (VG.Proof.MlKem.padded 136 Spec.Sha3.shakeSuffix (Spec.Sha3.bytesAt m p 66)) 544
  rw [ResidentSeed66.padded_A0 (VG.Proof.Sha3.bytesAt_length _ _ _),Spec.Sha3.squeeze]
  change _=(Spec.Sha3.squeezeBlocks 136
    (Spec.Sha3.keccakF (ResidentSeed66.A0 (Spec.Sha3.bytesAt m p 66))) 4).take 544
  rw [List.take_of_length_le (by rw [VG.Proof.Sha3.length_squeezeBlocks (by decide)])]

theorem sampledRows_H (σ : State) (η i : Nat) :
    sampledRows σ η i=rbFold η []
      (Spec.MlDsa.H (Spec.Sha3.bytesAt σ.mem (samplerSeedAt σ i) 66) 544) := by
  unfold sampledRows samplerA
  rw [←rbFold_append,chunks_H]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
