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

end VG.Proof.MlKem.AArch64.KeyGen
