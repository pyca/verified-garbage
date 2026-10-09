import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskFour
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourAdaptive

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample

def resultWord (L : List Zq) (j : Nat) : BitVec 32 := if L.length=256 then zw (L.getD j 0) else 0#32

structure Sampled (σ s : State) (L : Nat→List Zq) : Prop where
 env : SamplerEnv σ s
 bound : ∀i<4,(L i).length≤256
 words : ∀i<4,∀j<256,coeffAt s.mem (outputAt (samplerOut σ) i) j=resultWord (L i) j
 flag : s.gpr .x27=countFlag L

theorem maskStage_ok {σ s : State} (hp : SamplerPre σ) {A : Nat→Spec.Sha3.State}
    {L : Nat→List Zq} (hs : SamplerRun σ s A L) (hf : s.gpr .x27=countFlag L) :
    WP isa maskFour s (fun t=>Sampled σ t L) := by
  have hout (i j : Nat) (hi : i<4) (hj : j<64) :
      InRegions s.wr (outputAt (samplerOut σ) i+BitVec.ofNat 64 (16*j)) 16 := by
    rw [hs.env.wr,hp.wr]
    refine ⟨samplerOutput σ,by simp,?_⟩
    unfold outputAt
    rw [Offset.add_add]
    exact Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (maskFour_ok hs.env.x19 hs.env.x21
    (fun i hi=>by rw [hs.fields.count i hi,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; omega)
    (fun i hi=>sampler_work_read hp hs.env.wr (by omega))
    (fun i hi j hj=>by obtain ⟨r,hr,hc⟩:=hout i j hi hj; exact ⟨r,List.mem_append_right _ hr,hc⟩)
    (fun i hi j hj=>hout i j hi hj)
    (fun i hi j hj=>(hp.output_work.symm.sub_left
      (Offset.sub_base _ (d := 7904+8*i) (n := 8) (k := 8192) (by omega))).sub_right (outputAt_sub _ hj)))
    fun t ht=>?_
  refine ⟨?_,hs.fields.bound,?_,(ht.keep.get .x27).trans hf⟩
  · exact hs.env.frameStep ht.frame (fun r hr=>by
      rw [List.mem_singleton.mp hr]
      exact ⟨ResidentRej.aR 4 σ,by simp,fun _ h=>h⟩)
      (fun r hr=>by rw [List.mem_singleton.mp hr]; exact
        (hp.output_work.sub_right (Offset.sub_base _ (d := 7968) (n := 144) (k := 8192) (by decide))).symm)
      ht.keep.rd ht.keep.wr ht.keep.sp (fun r hr=>ht.keep.get r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> decide))
  · intro i hi j hj
    rw [ht.words i hi j hj,ite_eq_left hi]
    unfold maskedWord resultWord
    rw [hs.fields.count i hi]
    by_cases hfull : (L i).length=256
    · rw [hfull,ite_eq_left rfl,ite_eq_left rfl]
      exact hs.fields.stored i hi j (by omega)
    · have hn : BitVec.ofNat 64 (256-(L i).length)≠0#64 := by
        intro he
        have hh:=congrArg BitVec.toNat he
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at hh
        change 256-(L i).length=0 at hh
        have:=hs.fields.bound i hi
        omega
      rw [ite_eq_right hn,ite_eq_right hfull]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
