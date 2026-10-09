import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedBody
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedContract

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.KeyGen
variable {keccak : Proof.Sha3.AArch64.Permutation}

theorem verify_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    Piece p S (fun σ s=>s=σ ∧ Sign.StaticRoots S s)
      (fun σ s=>abiPreserved σ s ∧ (verifyContract p abi S).post σ s)
      (Impl.MlDsa.AArch64.Verify.Optimized.verifyWith keccak.callee P p) := by
  unfold Impl.MlDsa.AArch64.Verify.Optimized.verifyWith
  exact (Piece.of_vpiece (OptimizedSamples.rooted_piece (pro_vpiece hF)
    (by change 0≤S;omega) hP.s64)).seq
    ((body_piece hP hF).seq (Piece.of_vpiece (epi_vpiece hF)))

/-- Exact optimized verification under the unchanged public algorithm,
with only the two immutable artifact tables supplied by the ABI. -/
theorem verify_verified {P : Prims} (hP : PrimsOk P 16) {p : Params}
    (hp : p=mlDsa44∨p=mlDsa65∨p=mlDsa87) :
    Verified target (Impl.MlDsa.AArch64.Verify.Optimized.verifyWith keccak.callee P p)
      (verifyContract p (abi.withConsts Sign.signRootConsts) 16) := by
  apply Verified.of_correct (k:=verifyK p 16)
  · intro σ h
    exact (verify_piece hP (vfacts hp)).ok σ σ h.1 ⟨rfl,h.2⟩
  · intro s t ts tt u v hs ht pub es et
    exact ((verify_piece hP (vfacts hp)).tr _ _ _ _ _ _
      ⟨⟨s,t,hs.1,ht.1,pub.1,⟨rfl,hs.2⟩,⟨rfl,ht.2⟩⟩,pub.2⟩ es et).1
  · exact verifyK_implies hp

end VG.Proof.MlDsa.AArch64.Verify.Optimized
