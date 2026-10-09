import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdaptive

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (F)

/-- A failing adaptive parse retains the complete public XOF buffer used by
legacy tail cleanup; successful early completion needs no sixth block. -/
structure TimingDone (v : Nat) (σ s : State) : Prop where
  done : Done v σ s
  bytes : s.gpr .x27≠0#64 → ∀k<v,∀j<1008,
    s.mem (bufP σ k+BitVec.ofNat 64 j)=F σ k j

theorem adaptiveFour_timingDone {σ s : State} (hp : Pre 4 σ)
    (h : Rows 4 5 σ (fun k => prefixRow σ k 840) s)
    (hf : Flags 4 (fun k => prefixRow σ k 840) s) :
    WP isa (.ite (.zero .x .x27) (.block [])
      (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.squeezeN
        Impl.MlDsa.AArch64.Optimized.ResidentRej.step 840 1)
        (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.batch 0 840 56)
          (.block Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.flags)))) s (TimingDone 4 σ) := by
  by_cases hz : s.gpr .x27=0#64
  · refine WP.ite true (by rw [eval_zero,hz]; rfl) (fun _ => ?_) (by simp)
    exact WP.block_nil ⟨h.early_done hf hz,fun hn => False.elim (hn hz)⟩
  · refine WP.ite false (by
      rw [eval_zero]
      have he : (s.gpr .x27==0)=false := by simp only [beq_eq_false_iff_ne]; exact hz
      rw [he]) (by simp) (fun _ => ?_)
    apply WP.seq
    refine WP.mono (sixthFour_ok hp h) fun a ha => ?_
    apply WP.seq
    refine WP.mono (parseSixthFour_ok hp ha) fun b hb => ?_
    exact WP.mono (flagsSemantic_ok hp hb) fun _ ⟨ht,hft⟩ =>
      ⟨ht.done hft,fun _ k hk j hj => ht.bytes k hk j hj⟩

theorem adaptiveTwo_timingDone {σ s : State} (hp : Pre 2 σ)
    (h : Rows 2 5 σ (fun k => prefixRow σ k 840) s)
    (hf : Flags 2 (fun k => prefixRow σ k 840) s) :
    WP isa (.ite (.zero .x .x27) (.block [])
      (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.squeezeN
        Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.step 840 1)
        (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.batch 0 840 56)
          (.block Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.flags)))) s (TimingDone 2 σ) := by
  by_cases hz : s.gpr .x27=0#64
  · refine WP.ite true (by rw [eval_zero,hz]; rfl) (fun _ => ?_) (by simp)
    exact WP.block_nil ⟨h.early_done hf hz,fun hn => False.elim (hn hz)⟩
  · refine WP.ite false (by
      rw [eval_zero]
      have he : (s.gpr .x27==0)=false := by simp only [beq_eq_false_iff_ne]; exact hz
      rw [he]) (by simp) (fun _ => ?_)
    apply WP.seq
    refine WP.mono (sixthTwo_ok hp h) fun a ha => ?_
    apply WP.seq
    refine WP.mono (parseSixthTwo_ok hp ha) fun b hb => ?_
    exact WP.mono (flagsSemantic_ok hp hb) fun _ ⟨ht,hft⟩ =>
      ⟨ht.done hft,fun _ k hk j hj => ht.bytes k hk j hj⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
