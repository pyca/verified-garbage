import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedRestTiming

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Spec.MlDsa (Params)
variable {keccak : Proof.Sha3.AArch64.Permutation}

theorem codeWith_ct {P : Prims} {S : Nat} (hP : PrimsOk P S) {cd : Prog isa}
    (C : CalleeOk S cd (Spec.MlDsa.rejNTT2Contract AArch64.abi S))
    {p : Params} (hF : PFacts p) (hm : p.k*p.ℓ%4=0∨p.k*p.ℓ%4=2)
    (hs : (p.ℓ+p.k)%4=0∨(p.ℓ+p.k)%4=3)
    (hdprefix : 16*(prefixWith keccak.callee P cd p).aarch64Depth≤S)
    (hdpack : ∀j<p.ℓ+p.k,16*(packSecret P p j).aarch64Depth≤S)
    (hdrow : ∀i<p.k,16*(Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i).aarch64Depth≤S) :
    ConstantTime isa (fun s => kgPre p S s ∧ Sign.StaticRoots S s)
      (fun s t => kgPub p S s t ∧ TableEq s t) (codeWith keccak.callee P cd p) := by
  have ht : RelCT isa (RootPair p S (fun σ s => s=σ))
      (codeWith keccak.callee P cd p) (fun _ _ => True) :=
    RelCT.seq (piece_rooted (prefix_piece hP C hF hm hs) hdprefix hP.s64)
      (RelCT.seq (rest_relCT hP hF hdpack hdrow) (epi_piece hF).tr)
  intro s t tr ur s' t' hs ht' pub es et
  exact (ht _ _ _ _ _ _ ⟨⟨s,t,hs.1,ht'.1,pub.1,⟨rfl,hs.2⟩,⟨rfl,ht'.2⟩⟩,pub.2⟩ es et).1

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
