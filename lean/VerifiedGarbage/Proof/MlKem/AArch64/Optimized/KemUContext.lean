module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemNoise
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table
public import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc

/-! # Readonly data and retained errors survive ciphertext rows -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Noise (noiseOff)
variable {P : KemLay} {L : Layout}

theorem encW_noise_far {s₀ : State} (hp : Pre P L s₀) (hr : Noise.Room P)
    {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {j : Nat} (hj : j<P.k) :
    ∀r∈encW P L s₀ kC co, (polyRegion (sA L s₀ (noiseOff P j))).Disjoint r := by
  have hw := hp.wf
  have hn := Noise.noise_past_kem hr j
  have fits : noiseOff P j+1024≤L.len L.sc := by rw [hp.scl]; exact Noise.noise_fits hr hj
  intro r hh
  rcases mem5 hh with rfl | rfl | rfl | rfl | rfl
  · exact hp.args.rdisj hp.scb hp.scb fits (hp.fs (by lom)) (.inl rfl) (.inr (.inr (by lom)))
  · exact hp.args.rdisj hp.scb hp.scb fits (hp.fs (by lom)) (.inl rfl) (.inr (.inr (by lom)))
  · exact hp.args.rdisj hp.scb hp.scb fits (hp.fs (by lom)) (.inl rfl) (.inr (.inr (by lom)))
  · exact below_R hp hp.scb fits
  · apply hp.args.rdisj hp.scb (hp.lt A.hkC) fits A.fC (.inr (.inl hp.scw))
    rcases A.sC with hc | hc
    · exact .inl (Ne.symm hc)
    · have bound := hp.scl
      have hcfit := A.fC
      have hct : CB P+P.ctLen≤SV P := by lom
      exact .inr (.inr (by rw [hc]; omega))

theorem Errors.frame_enc {s₀ s t : State} (hp : Pre P L s₀) (hr : Noise.Room P)
    {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {rv : List Byte}
    (h : Errors P L s₀ rv s) (hf : Frame (encW P L s₀ kC co) s.mem t.mem) : Errors P L s₀ rv t := by
  intro j hj
  exact polyIs_frame hf (encW_noise_far hp hr A hj) (h j hj)

theorem gamma_frame {m m' : Mem} {p : Addr} {W : List Region}
    (h : Dot.GammaArtifact m p) (hf : Frame W m m')
    (hd : ∀r∈W, (⟨p,512⟩ : Region).Disjoint r) : Dot.GammaArtifact m' p := by
  intro j hj
  rw [←h j hj]
  exact hf.readW (r := ⟨p,512⟩) (contains_off (by omega) (by decide)) hd (by decide)

end VG.Proof.MlKem.AArch64.Kem
