import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourAdaptiveTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourFinish

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa

theorem maskStage_relCT {σ τ : State} (hp : SamplerPre σ) (hq : SamplerPre τ)
    (hb : SamplerBases σ τ) {L M : Nat→List Zq} :
    RelCT isa (fun s t=>(∃A,SamplerRun σ s A L ∧ s.gpr .x27=countFlag L) ∧
      (∃B,SamplerRun τ t B M ∧ t.gpr .x27=countFlag M)) maskFour
      (fun s t=>Sampled σ s L ∧ Sampled τ t M) := by
  obtain ⟨_,hc⟩:=maskFour_taint
  have ct : RelCT isa (fun s t=>(∃A,SamplerRun σ s A L ∧ s.gpr .x27=countFlag L) ∧
      (∃B,SamplerRun τ t B M ∧ t.gpr .x27=countFlag M)) maskFour (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ h=>by
      obtain ⟨⟨A,ha,haf⟩,⟨B,hb',hbf⟩⟩:=h
      apply VG.Proof.MlKem.AArch64.agree_of
      · rw [ha.env.sp,hb'.env.sp]; exact hb.sp
      · intro r hr
        rcases (show r=Reg.x19∨r=Reg.x21 by simpa using hr) with rfl|rfl
        · rw [ha.env.x19,hb'.env.x19]; exact hb.scratch
        · rw [ha.env.x21,hb'.env.x21]; exact hb.output) hc
  exact (ct.wp (fun _ _ h=>by
    obtain ⟨⟨A,ha,haf⟩,⟨B,hb',hbf⟩⟩:=h
    exact ⟨maskStage_ok hp ha haf,maskStage_ok hq hb' hbf⟩)).mono
    (fun _ _ h=>h) (fun _ _ h=>h.2)

theorem finish_relCT {σ τ : State} (hp : SamplerPre σ) (hq : SamplerPre τ)
    (hb : SamplerBases σ τ) {L M : Nat→List Zq} :
    RelCT isa (fun s t=>Sampled σ s L ∧ Sampled τ t M)
      (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
        Impl.MlDsa.AArch64.Sample.Rej4.epi))
      (fun s t=>Result σ s L ∧ Result τ t M) := by
  obtain ⟨_,hc⟩:=finish_taint
  have ct : RelCT isa (fun s t=>Sampled σ s L ∧ Sampled τ t M)
      (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
        Impl.MlDsa.AArch64.Sample.Rej4.epi)) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ h=>VG.Proof.MlKem.AArch64.agree_of
      (by rw [h.1.env.sp,h.2.env.sp]; exact hb.sp) (fun r hr=>by
        rw [List.mem_singleton.mp hr,h.1.env.x19,h.2.env.x19]; exact hb.scratch)) hc
  exact (ct.wp (fun _ _ h=>⟨finish_ok hp h.1,finish_ok hq h.2⟩)).mono
    (fun _ _ h=>h) (fun _ _ h=>h.2)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
