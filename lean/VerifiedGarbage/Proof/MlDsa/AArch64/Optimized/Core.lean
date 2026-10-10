import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Pro
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveInit

/-! ## From `Constants.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep wp_vop wp_scalar)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

/-- Retain the measured constant initialization, including its unused legacy
reciprocal vector, while exposing only the modulus needed by this transform. -/
theorem fastConsts_ok (s : State) : WP isa (.block fastConsts) s fun t =>
    (∀ e < 4, vword (t.v .v16) e = 8380417#32) ∧ t.mem=s.mem ∧ Keep [.x9,.x10] s t := by
  unfold fastConsts
  rw [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.consts_ok s) fun s₁ ⟨hc,hm₁,hk₁⟩ => ?_
  refine wp_scalar (by rfl) (VG.Proof.MlDsa.AArch64.Arith.movW_ok .x9 2149582593 s₁)
    fun s₂ ⟨⟨_,hm₂⟩,hk₂⟩ hv₂ => ?_
  refine wp_vop (d := .v20) rfl fun s₃ h₃ => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · intro e he
    rw [h₃.get .v16,hv₂,hc.q,VG.AArch64.vword_ofVWords _ _ _ _ he]
    rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega) with rfl | rfl | rfl | rfl <;> rfl
  · rw [h₃.mem,hm₂,hm₁]
  · exact ((hk₁.trans hk₂).trans h₃.keep).mono

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `Core.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def nttGprs : List Reg := [.x2,.x3,.x4,.x5,.x7,.x8,.x9,.x10]

def nttMemory (m : Mem) (p : Addr) (z : Nat → Int) (zi zt : Nat → Nat → Nat → Nat → Int) : Mem :=
  fivePassMem (outerPassMem m p z 8) p zi zt 8

/-- Whole selected in-place machine program. This exact word-level contract is
separate from its field interpretation and permits arbitrary initial lane bits. -/
theorem renamedNtt_words_ok {s : State} {z : Nat → Int} {zi zt : Nat → Nat → Nat → Nat → Int}
    (ho : HoistedTable s.mem (s.gpr .x1) z) (ht : RootTable s.mem (s.gpr .x1) zi zt)
    (htr : expandedRegion (s.gpr .x1) ∈ s.rd++s.wr)
    (hw : outputRegion (s.gpr .x0) ∈ s.wr)
    (hsep : (expandedRegion (s.gpr .x1)).Disjoint (outputRegion (s.gpr .x0))) :
    WP isa renamedNtt s fun t => Keep nttGprs s t ∧ Frame [outputRegion (s.gpr .x0)] s.mem t.mem ∧
      t.mem=nttMemory s.mem (s.gpr .x0) z zi zt := by
  unfold renamedNtt
  refine WP.seq (WP.mono (fastConsts_ok s) fun s₁ ⟨hq₁,hm₁,hk₁⟩ => ?_)
  have ho₁ : HoistedMem s₁ z := HoistedTable.mem
    (by simpa only [hm₁,hk₁.get .x1] using ho)
    (by simpa only [hk₁.rd,hk₁.wr,hk₁.get .x1] using htr) hq₁
  refine WP.seq (WP.mono (outerRenamed_ok ho₁ ?_ ?_) fun s₂ ⟨hk₂,hc₂,_,hm₂⟩ => ?_)
  · intro u hu i
    exact ⟨_,List.mem_append_right _ (by simpa only [hk₁.wr,hk₁.get .x0] using hw),outer_contains _ hu i⟩
  · intro u hu i
    exact ⟨_,by simpa only [hk₁.wr,hk₁.get .x0] using hw,outer_contains _ hu i⟩
  · have hf₂ : Frame [outputRegion (s.gpr .x0)] s.mem s₂.mem := by
      rw [hm₂,hm₁,hk₁.get .x0]
      exact outerPass_frame (fun u hu i => outer_contains _ hu i)
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
      simpa only [nttMemory,hm₂,hm₁,hk₂.get .x0,hk₁.get .x0] using hm₃

end VG.Proof.MlDsa.AArch64.Optimized

end
