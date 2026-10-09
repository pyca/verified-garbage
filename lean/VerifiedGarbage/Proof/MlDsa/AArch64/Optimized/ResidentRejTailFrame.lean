import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejDone

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
