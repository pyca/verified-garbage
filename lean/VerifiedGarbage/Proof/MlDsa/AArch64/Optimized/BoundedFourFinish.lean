import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskFour
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourAdaptive
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEpi

/-! ## From `BoundedFourMasked.lean` -/

section

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

end

/-! ## From `BoundedFourFinish.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64

local instance (L : Nat→List Zq) : Decidable (∀i<4,(L i).length=256) :=
 Nat.decidableBallLT 4 (fun i _=>(L i).length=256)

structure Result (σ t : State) (L : Nat→List Zq) : Prop where
 abi : abiPreserved σ t
 frame : Frame [samplerOutput σ,samplerWorkspace σ] σ.mem t.mem
 rd : t.rd=σ.rd
 wr : t.wr=σ.wr
 words : ∀i<4,∀j<256,coeffAt t.mem (outputAt (samplerOut σ) i) j=resultWord (L i) j
 status : t.gpr .x0=if (∀i<4,(L i).length=256) then 1#64 else 0#64

theorem finish_ok {σ s : State} (hp : SamplerPre σ) {L : Nat→List Zq} (h : Sampled σ s L) :
    WP isa (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
      Impl.MlDsa.AArch64.Sample.Rej4.epi)) s (fun t=>Result σ t L) := by
  refine wp_subImm (by decide) fun a ha ea=>wp_lsr (by decide) fun b hb eb=>?_
  have he : SamplerEnv σ b := h.env.lowStep (rs := [])
    (by rw [hb.mem,ha.mem]; exact Frame.refl _ _) (by simp)
    (hb.rd.trans ha.rd) (hb.wr.trans ha.wr) (hb.sp.trans ha.sp)
    (fun r hr=>by
      have hn : r∉[Reg.x27] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> decide
      rw [hb.get r hn,ha.get r hn])
  have hbound : (countFlag L).toNat<512 := ResidentRej.foldedFlags_bound _ _ (fun i hi=>by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega)
  have eflag : b.gpr .x27=if (∀i<4,(L i).length=256) then 1#64 else 0#64 := by
    rw [eb,ea,h.flag,ResidentRej.smallFlag_status _ hbound]
    by_cases hz : countFlag L=0#64
    · rw [ite_eq_left hz,ite_eq_left ((countFlag_zero h.bound).mp hz)]
    · rw [ite_eq_right hz,ite_eq_right (fun hh=>hz ((countFlag_zero h.bound).mpr hh))]
  refine WP.mono (ResidentRej.epi_with he (fun d n hn=>sampler_work_read hp he.wr hn)) fun t ht=>?_
  exact ⟨ht.1,by rw [ht.2.1]; exact he.frame,ht.2.2.2.1.trans he.rd,
    ht.2.2.2.2.trans he.wr,by simpa only [ht.2.1,hb.mem,ha.mem] using h.words,
    ht.2.2.1.trans eflag⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
