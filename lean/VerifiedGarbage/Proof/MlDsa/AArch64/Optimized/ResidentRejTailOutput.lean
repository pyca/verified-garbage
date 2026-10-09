import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTail
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample (coeffAddr)

theorem zeroTail_frame_ok {v k : Nat} {σ s : State} (hp : Pre v σ) (h : Done v σ s)
    (hk : k<v) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.zeroTail k) s (fun t => Done v σ t ∧ Frame [aR v σ] s.mem t.mem) := by
  have hk4 : k<4 := by have := hp.streams; omega
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.zeroTail
  apply WP.seq
  refine wp_ldrx (a := countP σ k) (by
    unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; omega)
    (by rw [h.env.x19]; rfl) (in_scr_rd hp h.env.wr (by
      unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; omega)) fun a ha ea => wp_nil ?_
  have hd : Done v σ a := h.of_control ha (by decide)
  have hc : (a.gpr .x4).toNat=256-(prefixRow σ k 1008).length := by
    rw [ea]; exact h.counts k hk
  by_cases hz : a.gpr .x4=0#64
  · refine WP.ite true (by rw [eval_zero,hz]; rfl) (fun _ => ?_) (by simp)
    exact WP.block_nil ⟨hd,by rw [ha.mem]; exact Frame.refl _ _⟩
  · refine WP.ite false (by
      rw [eval_zero]
      have he : (a.gpr .x4==0)=false := by simp only [beq_eq_false_iff_ne]; exact hz
      rw [he]) (by simp) (fun _ => ?_)
    apply WP.seq
    have hl : (prefixRow σ k 1008).length<256 := by
      have := h.length k hk
      have hn : (a.gpr .x4).toNat≠0 := by intro e; exact hz (BitVec.eq_of_toNat_eq e)
      omega
    change WP isa (.block (tailCursor k++tailRead k++tailAdjust)) a _
    refine WP.mono (tailSetup_ok hp hd.env hk hl hc) fun b hb => ?_
    have hdb : Done v σ b := hd.of_control hb.1 (by decide)
    obtain ⟨skip,hskip,hptr,hcount,hzero⟩ := hb.2
    by_cases hz' : b.gpr .x4=0#64
    · refine WP.ite true (by rw [eval_zero,hz']; rfl) (fun _ => ?_) (by simp)
      exact WP.block_nil ⟨hdb,by rw [hb.1.mem,ha.mem]; exact Frame.refl _ _⟩
    · refine WP.ite false (by
        rw [eval_zero]
        have he : (b.gpr .x4==0)=false := by simp only [beq_eq_false_iff_ne]; exact hz'
        rw [he]) (by simp) (fun _ => ?_)
      have hn : 0<256-((prefixRow σ k 1008).length+skip) := by
        have hn' : (b.gpr .x4).toNat≠0 := by intro e; exact hz' (BitVec.eq_of_toNat_eq e)
        omega
      refine WP.mono (tailLoop_ok hn (by omega) hptr hcount ?_) fun t ht => ?_
      · intro i hi
        rw [hdb.env.wr]
        refine ⟨aR v σ,by simp [hp.wr],?_⟩
        change (aR v σ).Contains (((aP σ+BitVec.ofNat 64 (1024*k))+
          BitVec.ofNat 64 (4*((prefixRow σ k 1008).length+skip)))+BitVec.ofNat 64 (4*i)) 4
        rw [Offset.add_add,Offset.add_add]
        exact Offset.contains_base (aP σ) (by omega) (by have := hp.streams; omega)
      · refine ⟨hdb.tailKeep hp hk (by omega) (by omega) ht.1 ht.2,?_⟩
        have hf : Frame [aR v σ] b.mem t.mem := ht.2.sub (fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact ⟨aR v σ,by simp,fun x hx => poly_sub hk x (tailRange_sub (by omega) x hx)⟩)
        rw [hb.1.mem,ha.mem] at hf
        exact hf


end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
