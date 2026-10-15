module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecapsRest
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecryptStart
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrix
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Optimized decapsulation satisfies the original outcome and ABI -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Decaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.Kem
variable {P : KemLay} {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem optimized_correct {s₀ : State} (hp : Pre P (deL P) s₀) (hr : Noise.Room P)
    (hc : Calls P) (tables : Tables s₀)
    (depthA : (Impl.MlKem.AArch64.Optimized.deStart keccak.callee P).aarch64Depth≤1)
    (depthB : (Impl.MlKem.AArch64.Paired.matrix P false).aarch64Depth≤1) :
    WP isa (Impl.MlKem.AArch64.Optimized.decapsWith keccak.callee P) s₀ fun t=>
      abiPreserved s₀ t ∧ (decapsAArch64 P).post s₀ t := by
  have scratch0 : Covers [⟨kA s₀ (deL P).sc,P.scl⟩] s₀.wr := by
    have hh := cov_w₀ hp (b:=(deL P).sc) (o:=0) (l:=P.scl) ⟨hp.scw,hp.scb⟩
      (by rw [hp.scl]; omega)
    simpa only [R,ptr_zero] using hh
  refine WP.seq (WP.mono (WP.tablesDepth (start_ok hp hc tables.transforms tables.gamma tables.gammaRead
    (apart_of_covers tables.gammaApart scratch0)) tables depthA) fun sA ⟨hA,ta⟩=>?_)
  have scratchA : Covers [⟨kA s₀ (deL P).sc,P.scl⟩] sA.wr := by
    have hh := cov_w hp hA.kb (b:=(deL P).sc) (o:=0) (l:=P.scl) ⟨hp.scw,hp.scb⟩
      (by rw [hp.scl]; omega)
    simpa only [R,ptr_zero] using hh
  have mt : MatrixTable P (deL P) s₀ sA :=
    ⟨ta.shuffle,ta.shuffleRead,apart_of_covers ta.shuffleApart scratchA⟩
  refine WP.seq (WP.mono (WP.tablesDepth
    (paired_matrix_ok hp (BInv.zero hA.kb hA.x24 hA.rho) mt) ta depthB)
    fun sB ⟨⟨hB,_⟩,tb⟩=>?_)
  refine WP.mono (fused_c_ok hp hr hc hA tb.transforms hB tb.gamma tb.gammaRead
    (readonly_enc hp hB.kb (encArgs hp.wf) tb.gammaApart tb.gammaStack)
    (readonly_noise hp hr hB.kb tb.gammaApart)) fun t ht=>⟨ht.abi,post_of hB ht⟩

end VG.Proof.MlKem.AArch64.Decaps
