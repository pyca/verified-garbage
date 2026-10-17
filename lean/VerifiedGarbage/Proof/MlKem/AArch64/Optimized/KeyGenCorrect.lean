module

public import VerifiedGarbage.Proof.MlKem.AArch64.KeyGen
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrix
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables

/-! # Optimized key generation satisfies the original outcome and ABI -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64.Optimized
variable {P : KemLay} {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem optimized_correct {s₀ : State} (hp : Pre P s₀) (hr : Noise.Room P) (tables : Tables s₀)
    (depthA : (P.kgAWith keccak.callee).aarch64Depth≤1)
    (depthB : (Impl.MlKem.AArch64.Paired.matrix P true).aarch64Depth≤1) :
    WP isa (Impl.MlKem.AArch64.Optimized.keyGenWith keccak.callee P) s₀ fun t=>
      abiPreserved s₀ t ∧ (keyGenAArch64 P).post s₀ t := by
  refine WP.seq (WP.mono (WP.tablesDepth (a_ok hp) tables depthA) fun sA ⟨hA,ta⟩=>?_)
  have scratchA : Covers [⟨kA s₀ 3,P.scl⟩] sA.wr := by
    simpa only [R,ptr_zero] using (cov_w hp hA.kb (b:=3) (o:=0) (l:=P.scl) (by decide) (by kl))
  have mt : MatrixTable P s₀ sA :=
    ⟨ta.shuffle,ta.shuffleRead,apart_of_covers ta.shuffleApart scratchA⟩
  refine WP.seq (WP.mono (WP.tablesDepth (paired_matrix_ok hp (BInv.zero hA) mt) ta depthB)
    fun sB ⟨⟨hB,_⟩,tb⟩=>?_)
  have hw := hp.wf
  refine WP.mono (rest_ok hp hr tb.transforms hB
    (readonly_rows hp hB.kb tb.gamma tb.gammaRead tb.gammaApart)
    (readonly_noise hp hr hB.kb tb.gammaApart)
    (apart_of_covers tb.gammaApart (cov_w hp hB.kb (b:=2) (o:=0) (l:=384*P.k) (by decide) (by kl))))
    fun t ht=>⟨ht.abi,post_of hB ht⟩

end VG.Proof.MlKem.AArch64.KeyGen
