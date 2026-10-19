module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryPost

/-! Complete native generation satisfies the shared functional contract. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64

theorem generation_correct (H : GenerationHashes) (M : Mont) (K : Kernel)
    (s : State) (pre : (Spec.Dsa.generateParametersContract abi 464).pre s) :
    ∃ trace t, Exec isa (Impl.Dsa.AArch64.Generation.code H.sha1 H.sha256 M.mm K.run) s trace t ∧
      abiPreserved s t ∧ (Spec.Dsa.generateParametersContract abi 464).post s t := by
  obtain ⟨trace, t, he, result, habi, _, _⟩ := entryRun_ok H M K (generationABI_of pre)
  exact ⟨trace, t, he, habi, entry_shared_post result⟩

end VG.Proof.Dsa.AArch64.Generation
