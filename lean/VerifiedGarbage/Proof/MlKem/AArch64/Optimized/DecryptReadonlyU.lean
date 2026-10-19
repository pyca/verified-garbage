module

public import VerifiedGarbage.Proof.MlKem.AArch64.DecapsA
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemReadonlyTransform
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecryptU
public import VerifiedGarbage.Impl.MlKem.AArch64.ReadonlyDecrypt
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemVDecode
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemVInv
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemURow
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyLayoutTables
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemNoise
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemTransformFrames

/-! # Ciphertext vector transformation with an explicit memory footprint -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Decaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay}

theorem readonly_u_step_frame {s₀ : State} (hp : Pre P (deL P) s₀) (hc : Calls P) {i : Nat} (hi : i < P.k) {s : State}
    (ht : Optimized.TransformTables s)
    (h : DInv P s₀ i s) : WP isa (Impl.MlKem.AArch64.Optimized.readonlyDeU P i) s (fun t => DInv P s₀ (i + 1) t ∧ Frame [R (kA s₀) (deL P).sc (yOff P i) 1024,R (kA s₀) (deL P).sc NS 1024] s.mem t.mem) := by
  have hw := hp.wf
  have hpo := po_y hw hi
  have hu := du_le hi
  have fu : 32 * P.du * i + 32 * P.du ≤ (deL P).len 1 := by dek
  refine WP.seq (WP.mono_syms (ddL_ok hp hc (k := 1) (o := 32 * P.du * i) (d := P.du) (off := yOff P i) (by decide)
    fu (.inl rfl) hpo (.inl (by dek)) h.kb)
    fun s₁ ⟨kb₁, f₁, p₁, x₁⟩ sy₁ => ?_)
  have e₁ := h.frame kb₁ x₁ f₁ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact dfar hp (by omega) hpo.le (.inr (by simp only [yOff]; omega))
  rw [slice_eq h.kb (b := 1) (by decide) fu] at p₁
  have ht₁ := ht.frame sy₁ (kb₁.rd.trans h.kb.rd.symm) (kb₁.wr.trans h.kb.wr.symm) (kb₁.sp.trans h.kb.sp.symm)
    f₁ (cov_w hp h.kb ⟨hp.scw,hp.scb⟩ (o:=yOff P i) (l:=1024) (hp.fs hpo.le))
  refine WP.mono (readonly_ntt_ok hp hpo kb₁ p₁.1 ht₁) fun s₂ ⟨kb₂, f₂, p₂, x₂⟩ => ?_
  have e₂ := e₁.frame kb₂ x₂ f₂ fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact dfar hp (by omega) hpo.le (.inr (by simp only [yOff]; omega))
    · exact dfar hp (by omega) (by kom) (.inl (by kom))
  rw [p₁.2] at p₂
  refine ⟨⟨e₂.kb,e₂.x24,fun i' hi' => ?_⟩,(f₁.mono (by simp)).trans f₂⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact e₂.u i' hi'
  · refine (congrArg (fun x => PolyIs s₂.mem (sA (deL P) s₀ (yOff P i')) (ntt x)) ?_).mp p₂
    simp only [KPke.dcU, cD, deL, List.getD_cons_zero, List.getD_cons_succ, KemLay.params]


theorem readonly_u_all_frame {s₀ s : State} (hp : Pre P (deL P) s₀) (hc : Calls P)
    (ht : Optimized.TransformTables s) (h : DInv P s₀ 0 s) :
    WPs ((List.range P.k).map (Impl.MlKem.AArch64.Optimized.readonlyDeU P)) s fun t =>
      DInv P s₀ P.k t ∧ Frame (uWrites P s₀) s.mem t.mem ∧ Optimized.TransformTables t := by
  apply WPs.range (I := fun i t => DInv P s₀ i t ∧ Frame (uWrites P s₀) s.mem t.mem ∧ Optimized.TransformTables t)
  · intro i hi t ⟨di,fi,ti⟩
    refine WP.mono_syms (readonly_u_step_frame hp hc hi ti di) fun u ⟨du,fu⟩ us => ?_
    have hw := hp.wf
    have cc := covers_cons (cov_s hp di.kb (po_y hw hi).le) (cov_s hp di.kb (o:=NS) (l:=1024) (by kom))
    exact ⟨du,fi.trans (fu.sub (fun r hh => by
      rcases mem2' hh with rfl | rfl
      · exact ⟨R (kA s₀) (deL P).sc (YH P) (1024*P.k),by simp [uWrites],
          R.sub2 (by simp [yOff]) (by simp only [yOff]; omega)⟩
      · exact ⟨_,by simp [uWrites],fun _ hh => hh⟩)),
      ti.frame us (du.kb.rd.trans di.kb.rd.symm) (du.kb.wr.trans di.kb.wr.symm) (du.kb.sp.trans di.kb.sp.symm) fu cc⟩
  · exact ⟨h,Frame.refl _ _,ht⟩

end VG.Proof.MlKem.AArch64.Decaps
