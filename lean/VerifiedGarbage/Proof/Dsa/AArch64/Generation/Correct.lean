module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStage
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hashes
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTest
public import VerifiedGarbage.Spec.Dsa.Generate

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryPost

/-! Complete native generation satisfies the shared functional contract. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64

theorem generation_correct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest)
    (s : State) (pre : (Spec.Dsa.generateParametersContract abi 736).pre s) :
    ∃ trace t, Exec isa (Impl.Dsa.AArch64.Generation.code H.sha1 H.sha256 G.run T.run) s trace t ∧
      abiPreserved s t ∧ (Spec.Dsa.generateParametersContract abi 736).post s t := by
  obtain ⟨trace, t, he, result, habi, _, _⟩ := entryRun_ok H G T (generationABI_of pre)
  exact ⟨trace, t, he, habi, entry_shared_post result⟩

end VG.Proof.Dsa.AArch64.Generation
