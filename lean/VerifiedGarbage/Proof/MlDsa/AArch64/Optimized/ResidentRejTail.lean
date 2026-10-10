import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejDone
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailAdjust
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailLoop

/-! ## From `ResidentRejTailFrame.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep Only)
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (coeffAt)

def tailRange (σ : State) (k start : Nat) : Region :=
  ⟨coeffAddr (polyP σ k) start,4*(256-start)⟩

theorem tailRange_sub {σ : State} {k start : Nat} (hs : start≤256) :
    Region.Sub (tailRange σ k start) (polyR (polyP σ k)) :=
  Offset.sub_base (polyP σ k) (by omega)

theorem Done.of_control {v : Nat} {σ s t : State} {rs : List Reg} (h : Done v σ s)
    (ht : Only rs s t) (hregs : ∀r∈[Reg.x19,.x20,.x21,.x30,.x27],r∉rs) : Done v σ t := by
  refine ⟨h.env.lowStep (rs := []) (by rw [ht.mem]; exact Frame.refl _ _) (by simp)
    ht.rd ht.wr ht.sp (fun r hr => ht.get r (hregs r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp))),h.length,?_,?_,?_,?_⟩
  · simpa only [ht.mem] using h.counts
  · simpa only [ht.mem] using h.stored
  · rw [ht.get .x27 (hregs .x27 (by simp))]; exact h.flags.bound
  · rw [ht.get .x27 (hregs .x27 (by simp))]; exact h.flags.zero

theorem Done.tailKeep {v k start : Nat} {σ s t : State} (hp : Pre v σ) (h : Done v σ s)
    (hk : k<v) (hs : start≤256) (hlen : (prefixRow σ k 1008).length≤start)
    (ht : Keep [.x3,.x4] s t) (hf : Frame [tailRange σ k start] s.mem t.mem) : Done v σ t := by
  have hsub := tailRange_sub (σ := σ) (k := k) hs
  have hOut : Region.Sub (tailRange σ k start) (aR v σ) := fun x hx => poly_sub hk x (hsub x hx)
  have hscr : (scrR σ).Disjoint (tailRange σ k start) := hp.a_scr.symm.sub_right hOut
  refine ⟨h.env.frameStep hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨aR v σ,by simp,hOut⟩)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hscr.sub_left (Offset.sub_base (scr σ) (by decide)))
    ht.rd ht.wr ht.sp (fun r hr => ht.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)),h.length,?_,?_,?_,?_⟩
  · intro j hj
    rw [hf.readW (Region.contains_self (countP σ j) 8) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hscr.sub_left (Offset.sub_base (scr σ) (by
        unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; have:=hp.streams; omega))) (by decide)]
    exact h.counts j hj
  · intro j hj i hi
    have hl := h.length j hj
    have hd : (Region.mk (polyP σ j) (4*(prefixRow σ j 1008).length)).Disjoint (tailRange σ k start) := by
      by_cases heq : j=k
      · subst j
        exact (Offset.disjoint_base (polyP σ k) (d := 4*start) (n := 4*(256-start))
          (k := 4*(prefixRow σ k 1008).length) (by omega) (by omega)).symm
      · apply (Offset.disjoint (aP σ) (d := 1024*j) (e := 1024*k) (n := 1024) (k := 1024)
          (by omega) (by have:=hp.streams; omega) (by have:=hp.streams; omega)).sub_right hsub |>.sub_left
        exact Region.sub_prefix (by omega)
    change t.mem.readW (coeffAddr (polyP σ j) i) 32= _
    rw [hf.readW (Offset.contains_base (polyP σ j) (d := 4*i) (n := 4)
      (k := 4*(prefixRow σ j 1008).length) (by omega) (by omega))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)]
    exact h.stored j hj i hi
  · rw [ht.get .x27]; exact h.flags.bound
  · rw [ht.get .x27]; exact h.flags.zero

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejTailSetup.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample (coeffAddr)

theorem tailSetup_ok {v k len : Nat} {σ s : State} (hp : Pre v σ) (he : Env v σ s)
    (hk : k<v) (hl : len<256) (hc : (s.gpr .x4).toNat=256-len) :
    WP isa (.block (tailCursor k++tailRead k++tailAdjust)) s fun t =>
      Only [.x3,.x4,.x6,.x7,.x9] s t ∧
      ∃skip≤1,t.gpr .x3=coeffAddr (polyP σ k) (len+skip) ∧
        (t.gpr .x4).toNat=256-(len+skip) ∧ t.gpr .x9=0 := by
  have hk4 : k<4 := by have := hp.streams; omega
  rw [List.append_assoc,WP.block_append_iff]
  apply WP.mono (tailCursor_ok hk4 (by omega) hc)
  intro a ha
  rw [WP.block_append_iff]
  have hr : InRegions (a.rd++a.wr)
      (a.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) 4 := by
    rw [ha.1.rd,ha.1.wr,ha.1.get .x19,he.x19]
    exact in_scr_rd hp he.wr (by omega)
  apply WP.mono (tailRead_ok hk4 hr)
  intro b hb
  apply WP.mono (tailAdjust_ok hl (p := polyP σ k) (by
    rw [hb.get .x3,ha.2,he.x21]; rfl) (by rw [hb.get .x4,ha.1.get .x4]; exact hc))
  intro t ht
  exact ⟨((ha.1.trans hb).trans ht.1).mono (by decide),ht.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejTail.lean` -/

section

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

end
