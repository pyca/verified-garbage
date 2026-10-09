import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailSetup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample (coeffAddr)

theorem zeroTail_ok {v k : Nat} {σ s : State} (hp : Pre v σ) (h : Done v σ s)
    (hk : k<v) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.zeroTail k) s (Done v σ) := by
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
    exact WP.block_nil hd
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
      exact WP.block_nil hdb
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
      · exact hdb.tailKeep hp hk (by omega) (by omega) ht.1 ht.2


theorem tailRows_ok {v : Nat} {σ s : State} (hp : Pre v σ) (h : Done v σ s)
    (ks : List Nat) (hks : ∀k∈ks,k<v) :
    WP isa (ks.foldr (fun k rest => .seq
      (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.zeroTail k) rest) (.block [])) s (Done v σ) := by
  induction ks generalizing s with
  | nil => exact WP.block_nil h
  | cons k ks ih =>
    apply WP.seq
    exact WP.mono (zeroTail_ok hp h (hks k (by simp))) fun t ht =>
      ih ht (fun j hj => hks j (by simp [hj]))

theorem tailZerosFour_ok {σ s : State} (hp : Pre 4 σ) (h : Done 4 σ s) :
    WP isa Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.tailZeros s (Done 4 σ) := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.tailZeros
  by_cases hz : s.gpr .x27=0#64
  · refine WP.ite true (by rw [eval_zero,hz]; rfl) (fun _ => ?_) (by simp)
    exact WP.block_nil h
  · refine WP.ite false (by
      rw [eval_zero]
      have he : (s.gpr .x27==0)=false := by simp only [beq_eq_false_iff_ne]; exact hz
      rw [he]) (by simp) (fun _ => ?_)
    exact tailRows_ok hp h _ (by simpa only [List.mem_range] using fun k hk => hk)

theorem tailZerosTwo_ok {σ s : State} (hp : Pre 2 σ) (h : Done 2 σ s) :
    WP isa Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.tailZeros s (Done 2 σ) := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.tailZeros
  by_cases hz : s.gpr .x27=0#64
  · refine WP.ite true (by rw [eval_zero,hz]; rfl) (fun _ => ?_) (by simp)
    exact WP.block_nil h
  · refine WP.ite false (by
      rw [eval_zero]
      have he : (s.gpr .x27==0)=false := by simp only [beq_eq_false_iff_ne]; exact hz
      rw [he]) (by simp) (fun _ => ?_)
    exact tailRows_ok hp h _ (by simpa only [List.mem_range] using fun k hk => hk)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
