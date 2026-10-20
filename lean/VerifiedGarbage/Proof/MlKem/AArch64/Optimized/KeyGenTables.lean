module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenRow
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table

/-! # Readonly gamma data through the fused key-generation rows -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay}

structure RowTable (P : KemLay) (s₀ s : State) : Prop where
  table : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA")
  read : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr)
  apart : ∀ i < P.k, ∀ r ∈ rowWrites P s₀ i, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r

theorem RowTable.frame {s₀ s t : State} {i : Nat} (hi : i < P.k)
    (h : RowTable P s₀ s) (hs : t.syms = s.syms)
    (hk : KB P s₀ s) (hk' : KB P s₀ t)
    (hf : Frame (rowWrites P s₀ i) s.mem t.mem) : RowTable P s₀ t := by
  refine ⟨?_,?_,?_⟩
  · rw [hs]
    intro j hj
    rw [←h.table j hj]
    exact hf.readW (r := ⟨s.syms "VG_MLKEM_GAMMA",512⟩)
      (contains_off (by omega) (by decide)) (h.apart i hi) (by decide)
  · simpa only [hs,hk'.rd,hk'.wr,←hk.rd,←hk.wr] using h.read
  · simpa only [hs] using h.apart

end VG.Proof.MlKem.AArch64.KeyGen
