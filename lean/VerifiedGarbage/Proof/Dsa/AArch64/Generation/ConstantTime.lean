module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStage
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hashes
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTest
public import VerifiedGarbage.Spec.Dsa.Generate

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryInnerCT
import VerifiedGarbage.Proof.Framework.AArch64.RelCT

/-! Complete generation timing depends only on the contract's public inputs. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.MillerRabin.AArch64 VG.Proof.Bignum.AArch64

theorem generation_ct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) :
    ConstantTime isa (Spec.Dsa.generateParametersContract abi 736).pre
      (Spec.Dsa.generateParametersContract abi 736).pub
      (Impl.Dsa.AArch64.Generation.code H.sha1 H.sha256 G.run T.run) := by
  intro s t xs ys u v hs ht hp es et
  have ha := generationABI_of hs
  have hb := generationABI_of ht
  have agree := generation_public_related hp
  have ct : RelCT isa (fun s t => GenerationABI s ∧ GenerationABI t ∧ GenerationPublicAgree s t)
      (Impl.Dsa.AArch64.Generation.code H.sha1 H.sha256 G.run T.run) (fun _ _ => True) := by
    apply RelCT.alloc
    rintro a b xa xb u v ⟨s, t, ⟨hs, ht, hp⟩, rfl, rfl⟩ ea eb
    exact ⟨entryAllocated_ct H G T hs ht hp ea eb, True.intro⟩
  exact (ct _ _ _ _ _ _ ⟨ha, hb, agree⟩ es et).1

end VG.Proof.Dsa.AArch64.Generation
