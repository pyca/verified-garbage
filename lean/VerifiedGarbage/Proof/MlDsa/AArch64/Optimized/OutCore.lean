import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Core
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterOutInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveInit

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem outerOutPass_frame {m : Mem} {p src : Addr} {r : Region} {z : Nat → Int} {N : Nat}
    (hc : ∀ u<N, ∀ i : Fin 8, r.Contains
      ((p+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16) :
    Frame [r] m (outerOutPassMem m p src z N) := by
  induction N with
  | zero => exact Frame.refl _ _
  | succ N ih =>
    have hf := ih (fun u hu i => hc u (by omega) i)
    simp only [outerOutPassMem,outerOutMemStep]
    exact writeBank_frame _ _ _ (by simp) (hc N (by omega)) hf

def outGprs : List Reg := .x11::nttGprs

def outMemory (m : Mem) (p src : Addr) (z : Nat → Int) (zi zt : Nat → Nat → Nat → Nat → Int) : Mem :=
  fivePassMem (outerOutPassMem m p src z 8) p zi zt 8

/-- Whole selected in-place machine program. This exact word-level contract is
separate from its field interpretation and permits arbitrary initial lane bits. -/
theorem outBody_words_ok {s : State} {z : Nat → Int} {zi zt : Nat → Nat → Nat → Nat → Int}
    (ho : HoistedTable s.mem (s.gpr .x1) z) (ht : RootTable s.mem (s.gpr .x1) zi zt)
    (htr : expandedRegion (s.gpr .x1) ∈ s.rd++s.wr)
    (hr : outputRegion (s.gpr .x11) ∈ s.rd++s.wr)
    (hw : outputRegion (s.gpr .x0) ∈ s.wr)
    (hsep : (expandedRegion (s.gpr .x1)).Disjoint (outputRegion (s.gpr .x0))) :
    WP isa (.seq (.block fastConsts) (.seq outerOut renFive)) s fun t => Keep outGprs s t ∧ Frame [outputRegion (s.gpr .x0)] s.mem t.mem ∧
      t.mem=outMemory s.mem (s.gpr .x0) (s.gpr .x11) z zi zt := by
  refine WP.seq (WP.mono (fastConsts_ok s) fun s₁ ⟨hq₁,hm₁,hk₁⟩ => ?_)
  have ho₁ : HoistedMem s₁ z := HoistedTable.mem
    (by simpa only [hm₁,hk₁.get .x1] using ho)
    (by simpa only [hk₁.rd,hk₁.wr,hk₁.get .x1] using htr) hq₁
  refine WP.seq (WP.mono (outerOut_ok ho₁ ?_ ?_) fun s₂ ⟨hk₂,hc₂,_,_,hm₂⟩ => ?_)
  · intro u hu i
    exact ⟨_,by simpa only [hk₁.rd,hk₁.wr,hk₁.get .x11] using hr,outer_contains _ hu i⟩
  · intro u hu i
    exact ⟨_,by simpa only [hk₁.wr,hk₁.get .x0] using hw,outer_contains _ hu i⟩
  · have hf₂ : Frame [outputRegion (s.gpr .x0)] s.mem s₂.mem := by
      rw [hm₂,hm₁,hk₁.get .x0,hk₁.get .x11]
      exact outerOutPass_frame (fun u hu i => outer_contains _ hu i)
    have ht₂ : RootTable s₂.mem (s₂.gpr .x1) zi zt := by
      rw [hk₂.get .x1,hk₁.get .x1]
      exact ht.frame hf₂ (by intro r hr; have he := List.mem_singleton.mp hr; subst r; exact hsep)
    refine WP.mono (renFive_ok (r := outputRegion (s.gpr .x0)) ht₂ hc₂.q ?_ ?_ ?_ ?_) fun t ⟨hk₃,hf₃,_,_,hm₃⟩ => ?_
    · simpa only [hk₂.rd,hk₂.wr,hk₂.get .x1,hk₁.rd,hk₁.wr,hk₁.get .x1] using htr
    · simpa only [hk₂.wr,hk₁.wr] using hw
    · simpa only [hk₂.get .x1,hk₁.get .x1] using hsep
    · intro u hu i
      rw [hk₂.get .x0,hk₁.get .x0]
      exact inner_output_contains _ hu i
    · refine ⟨((hk₁.trans hk₂).trans hk₃).mono,hf₂.trans hf₃,?_⟩
      simpa only [outMemory,hm₂,hm₁,hk₂.get .x0,hk₁.get .x0,hk₁.get .x11] using hm₃

theorem outerOutPassMem_self (m : Mem) (p : Addr) (z : Nat → Int) (N : Nat) :
    outerOutPassMem m p p z N=outerPassMem m p z N := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [outerOutPassMem,outerPassMem,outerOutMemStep,outerMemStep,ih]

theorem outMemory_self (m : Mem) (p : Addr) (z : Nat → Int) (zi zt : Nat → Nat → Nat → Nat → Int) :
    outMemory m p p z zi zt=nttMemory m p z zi zt := by
  simp only [outMemory,nttMemory,outerOutPassMem_self]

end VG.Proof.MlDsa.AArch64.Optimized
