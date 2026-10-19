module

public import VerifiedGarbage.Proof.MlKem.AArch64.DecapsA
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemVDecode
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemVInv
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemReadonlyTransform
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

theorem u_step_frame {s₀ : State} (hp : Pre P (deL P) s₀) (hc : Calls P) {i : Nat} (hi : i < P.k) {s : State}
    (h : DInv P s₀ i s) : WP isa (P.deU i) s (fun t => DInv P s₀ (i + 1) t ∧ Frame [R (kA s₀) (deL P).sc (yOff P i) 1024,R (kA s₀) (deL P).sc NS 1024] s.mem t.mem) := by
  have hw := hp.wf
  have hpo := po_y hw hi
  have hu := du_le hi
  have fu : 32 * P.du * i + 32 * P.du ≤ (deL P).len 1 := by dek
  refine WP.seq (WP.mono (ddL_ok hp hc (k := 1) (o := 32 * P.du * i) (d := P.du) (off := yOff P i) (by decide)
    fu (.inl rfl) hpo (.inl (by dek)) h.kb)
    fun s₁ ⟨kb₁, f₁, p₁, x₁⟩ => ?_)
  have e₁ := h.frame kb₁ x₁ f₁ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact dfar hp (by omega) hpo.le (.inr (by simp only [yOff]; omega))
  rw [slice_eq h.kb (b := 1) (by decide) fu] at p₁
  refine WP.mono (ntt_ok hp hpo kb₁ p₁.1) fun s₂ ⟨kb₂, f₂, p₂, x₂⟩ => ?_
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


def uWrites (P : KemLay) (s₀ : State) : List Region :=
  [R (kA s₀) (deL P).sc (YH P) (1024*P.k),R (kA s₀) (deL P).sc NS 1024]

theorem u_all_frame {s₀ s : State} (hp : Pre P (deL P) s₀) (hc : Calls P) (h : DInv P s₀ 0 s) :
    WPs ((List.range P.k).map P.deU) s fun t => DInv P s₀ P.k t ∧ Frame (uWrites P s₀) s.mem t.mem := by
  apply WPs.range (I := fun i t => DInv P s₀ i t ∧ Frame (uWrites P s₀) s.mem t.mem)
  · intro i hi t ⟨di,fi⟩
    exact WP.mono (u_step_frame hp hc hi di) fun u ⟨du,fu⟩ => ⟨du,fi.trans (fu.sub (fun r hh => by
      rcases mem2' hh with rfl | rfl
      · exact ⟨R (kA s₀) (deL P).sc (YH P) (1024*P.k),by simp [uWrites],
          R.sub2 (by simp [yOff]) (by simp only [yOff]; omega)⟩
      · exact ⟨_,by simp [uWrites],fun _ hh => hh⟩))⟩
  · exact ⟨h,Frame.refl _ _⟩

end VG.Proof.MlKem.AArch64.Decaps
