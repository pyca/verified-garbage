import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSamplesFourTiming

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params coeffAt)

theorem vectorTail_taint : ∀j<80,
    (taint.check (Taint.ofRegs [.x28]) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (sc (oP j)) 256))
      (VG.Taint.hintOf taint (Taint.ofRegs [.x28]) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (sc 0) 256)))).isSome=true := by
  decide +kernel

theorem tail_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {a : Ptr}
    (hw : inB wbs a 1024 = true) (hin : inB (rbs ++ wbs) a 1024 = true)
    (hr : (s.gpr .x0).setWidth 32 = 0 ∨ (s.gpr .x0).setWidth 32 = 1) :
    WP isa (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code a 256)) s fun s' => PPostB S s s' [(a, 1024)] ∧
      s'.gpr .x24 = ((s.gpr .x24).setWidth 32 &&& (s.gpr .x0).setWidth 32).setWidth 64 ∧
      ∀ i < 256, coeffAt s'.mem (pa s a) i = if (s.gpr .x0).setWidth 32 = 1 then coeffAt s.mem (pa s a) i else 0 := by
  refine WP.seq (WP.mono (and24_ok s) fun s₁ ⟨o₁, e₁⟩ => ?_)
  have P₁ : PostB S s s₁ [] := postB_of_keep o₁.keep (by decide) (by rw [o₁.mem]; exact Frame.refl _ _)
  have L₁ := L.post P₁
  have x0 : s₁.gpr .x0 = s.gpr .x0 := o₁.get .x0
  rw [← x0] at hr
  refine WP.mono (VG.Proof.MlDsa.AArch64.Optimized.MatrixMask.mask_ok L₁ (N := 16) (by decide) (by decide) hw hin hr) fun s' ⟨P', k', hc⟩ => ⟨?_, by rw [k'.get .x24, e₁], ?_⟩
  · refine PostB.trans P₁ ?_ (fun _ h => absurd h List.not_mem_nil) fun _ h => h
    have e : ([(a, 1024)] : List (Ptr × Nat)).map (toR s₁) = [(a, 1024)].map (toR s) :=
      map_toR_post P₁ (fun w hw => by rw [List.mem_singleton.mp hw]; exact L.ptrBs hin)
    rw [← e]; exact P'
  · intro i hi
    rw [← P₁.pa (L.ptrBs hin), hc i hi, x0, o₁.mem]


variable {p : Params} {S : Nat} (hF : VFacts p)
include hF

theorem ballTail_vpiece : VPiece p S (VB1 p) (VB p) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (cP p) 256)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := hF.scr
  refine ⟨fun σ s hp h => ?_, taintRel [.x28] (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
    (vc_two hF p₁ p₂ pub h₁.1.vz.vc h₂.1.vz.vc).x28) (vectorTail_taint _ (by omega))⟩
  have L := h.1.vz.vc.lay hF hp
  obtain ⟨hv, hred, hout⟩ := h
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  refine WP.mono (tail_ok L (a := cP p) (by vlay) (by vlay) hr01) fun s' ⟨hP', x', hco⟩ => ?_
  have hvz := hv.vz.keep hF hp hP' (by vzchk hF)
  have e' : pa s' (cP p) = pa s (cP p) := sc_pa hP' _
  obtain ⟨q, hq, h1, h0⟩ := hv.ok
  rw [hq] at x'
  refine ⟨hvz, hv.nok, fun e he => L.keepRed hP' (by vlay) (hv.red e he), ?_, q && ((s.gpr .x0).setWidth 32 == 1), ?_, fun hq' => ⟨fun e he => ?_, ?_⟩,
    fun hq' => ?_⟩
  · rw [e']
    by_cases h1 : (s.gpr .x0).setWidth 32 = 1
    · exact (Proof.MlDsa.KeyGen.masked_one h1 hco).2 (hred h1)
    · exact (Proof.MlDsa.KeyGen.masked_zero h1 hco).1
  · rw [x', and_flag _ (Q := (s.gpr .x0).setWidth 32 = 1) (by rcases hr01 with h | h <;> rw [h] <;> decide)]
    exact flag_congr (by simp)
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq'
    obtain ⟨b, hb⟩ := h1 hq'.1 e he
    exact ⟨b, by rw [hb, L.keepPolyAt hP' (by vlay)]⟩
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq'
    rcases hout with ⟨_, b, hb⟩ | ⟨h0', _⟩
    · exact ⟨b, by rw [e', (Proof.MlDsa.KeyGen.masked_one hq'.2 hco).1]; exact hb⟩
    · rw [hq'.2] at h0'; exact absurd h0' (by decide)
  · cases hqq : q
    · exact .inl (h0 hqq)
    · rw [hqq] at hq'
      simp only [Bool.true_and, beq_eq_false_iff_ne, ne_eq] at hq'
      rcases hout with ⟨h1'', _⟩ | ⟨_, hn⟩
      · exact absurd h1'' hq'
      · exact .inr hn


end VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
