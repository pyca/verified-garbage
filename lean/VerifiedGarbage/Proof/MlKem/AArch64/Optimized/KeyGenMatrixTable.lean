module
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixFrame

/-! # Preserve the immutable rejection table across key-generation matrix entries -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Spec.MlKem
variable {P : KemLay}

structure MatrixTable (P : KemLay) (s₀ s : State) : Prop where
 artifact : Rej8.TableArtifact s.mem (s.syms "VG_MLKEM_REJ_SHUFFLE")
 readable : Covers [⟨s.syms "VG_MLKEM_REJ_SHUFFLE",4096⟩] (s.rd++s.wr)
 apart : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint ⟨kA s₀ 3,P.scl⟩

end VG.Proof.MlKem.AArch64.KeyGen
