module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenReady
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Fused key-generation rows retain the precomputed error polynomials -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Noise (noiseOff)
variable {P : KemLay}

def Errors (P : KemLay) (s₀ s : State) : Prop :=
  ∀ j < P.k, PolyIs s.mem (kA s₀ 3+BitVec.ofNat 64 (noiseOff P j)) (KPke.kgE P.params (dB s₀) j)

theorem errors_row {s₀ s t : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {i : Nat} (hi : i < P.k) (he : Errors P s₀ s)
    (hf : Frame (rowWrites P s₀ i) s.mem t.mem) : Errors P s₀ t := by
  have hw := hp.wf
  intro j hj
  have eg := Noise.noise_fits hr hj
  have ep := Noise.noise_past_kg hr j
  apply polyIs_frame hf _ (he j hj)
  intro r hm
  simp only [rowWrites,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact hp.args.rdisj (by decide) (by decide) eg (by kl) (by lom)
  · exact hp.args.rdisj (by decide) (by decide) eg (by kl) (.inl (by decide))
  · exact hp.args.rdisj (by decide) (by decide) eg (by kl) (.inl (by decide))

theorem fused_row_ready {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB : Mem} {v : BitVec 64} {i : Nat} (hi : i < P.k) (h : TL P s₀ mB v i s)
    (he : Errors P s₀ s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hc : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : (polyRegion (s.gpr .x28+BitVec.ofNat 64 (TP P))).Disjoint ⟨s.syms "VG_MLKEM_GAMMA",512⟩) :
    WP isa (Impl.MlKem.AArch64.Optimized.kgRow P i) s fun t =>
      TL P s₀ mB v (i+1) t ∧ Errors P s₀ t ∧ Frame (rowWrites P s₀ i) s.mem t.mem := by
  exact WP.mono (fused_row hp hr hi h (row_ready hp hi h ht hc ha).data (row_sum hi h) (he i hi))
    fun t ⟨h',hf⟩ => ⟨h',errors_row hp hr hi he hf,hf⟩

end VG.Proof.MlKem.AArch64.KeyGen
