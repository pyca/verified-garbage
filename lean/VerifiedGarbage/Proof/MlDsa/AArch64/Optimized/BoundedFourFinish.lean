import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMasked
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEpi

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
