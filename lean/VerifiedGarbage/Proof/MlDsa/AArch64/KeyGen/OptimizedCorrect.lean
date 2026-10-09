import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Optimized
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedMatrixTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecrets
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedRest

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Spec.MlDsa (Params)
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem prefix_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {cd : Prog isa}
    (C : CalleeOk S cd (Spec.MlDsa.rejNTT2Contract AArch64.abi S))
    {p : Params} (hF : PFacts p) (hm : p.k*p.ℓ%4=0 ∨ p.k*p.ℓ%4=2)
    (hs : (p.ℓ+p.k)%4=0 ∨ (p.ℓ+p.k)%4=3) :
    Piece p S (fun σ s => s=σ) (KSamp p · (p.k*p.ℓ) (p.ℓ+p.k))
      (prefixWith keccak.callee P cd p) :=
  Piece.seq (pro_piece hF) (Piece.seq (seeds_piece hF hP.s16 hP.s64)
    (Piece.seq (matrixWith_piece hP C hF hm) (secrets_piece keccak.callee hF hs S)))

/-- The selected key-generation computation retains the original outcome and
ABI. Immutable tables are the only additional entry resources. -/
theorem codeWith_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {cd : Prog isa}
    (C : CalleeOk S cd (Spec.MlDsa.rejNTT2Contract AArch64.abi S))
    {p : Params} (hF : PFacts p) (hm : p.k*p.ℓ%4=0 ∨ p.k*p.ℓ%4=2)
    (hs : (p.ℓ+p.k)%4=0 ∨ (p.ℓ+p.k)%4=3)
    {s : State} (hp : kgPre p S s) (roots : Sign.StaticRoots S s)
    (hdprefix : 16*(prefixWith keccak.callee P cd p).aarch64Depth≤S)
    (hdpack : ∀j<p.ℓ+p.k,16*(packSecret P p j).aarch64Depth≤S)
    (hdrow : ∀i<p.k,16*(Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i).aarch64Depth≤S) :
    WP isa (codeWith keccak.callee P cd p) s fun t =>
      abiPreserved s t ∧ (Spec.MlDsa.keyGenContract p AArch64.abi S).post s t := by
  unfold codeWith
  apply WP.seq
  refine WP.mono (roots.phase hdprefix hP.s64 ((prefix_piece hP C hF hm hs).ok s s hp rfl))
    fun u ⟨hu,ru⟩ => ?_
  apply WP.seq
  refine WP.mono (rest_ok hP hF hp hu ru hdpack hdrow) fun v hv => ?_
  exact (epi_piece hF).ok s v hp hv

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
