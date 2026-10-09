import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskTiming
import VerifiedGarbage.Spec.MlDsa.ResidentMask
import VerifiedGarbage.Proof.Framework.Contract

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64 VG.Spec.MlDsa

def pairK : Contract isa where
  pre := Pre
  post s t :=
    let g := (s.gpr .x1).setWidth 32 |>.toNat
    let d := 1+bitlen (g-1)
    PolyIs t.mem (s.gpr .x2) (toRq (bitUnpack (H (Spec.Sha3.bytesAt s.mem (s.gpr .x0) 66) (32*d)) (g-1) g)) ∧
    PolyIs t.mem (s.gpr .x3) (toRq (bitUnpack (H (Spec.Sha3.bytesAt s.mem (s.gpr .x0+66) 66) (32*d)) (g-1) g))
  pub := publicInputs

theorem pair_correct (core : Resident.Core) (s : State) (hp : pairK.pre s) :
    ∃ trace t, Exec isa (Impl.MlDsa.AArch64.Optimized.ResidentMask.rawWith core.code) s trace t ∧
      abiPreserved s t ∧ pairK.post s t := by
  rcases hp.gamma with hg | hg
  · obtain ⟨tr,t,he,ht⟩ := rawWith_ok core s hp (.inl rfl) hg
    refine ⟨tr,t,he,ht.1,?_⟩
    simpa only [pairK,hg,maskPoly,show (131072#32).toNat=2^17 from rfl,
      show 1+bitlen (2^17-1)=18 from rfl] using And.intro ht.2.2.1 ht.2.2.2.1
  · obtain ⟨tr,t,he,ht⟩ := rawWith_ok core s hp (.inr rfl) hg
    refine ⟨tr,t,he,ht.1,?_⟩
    simpa only [pairK,hg,maskPoly,show (524288#32).toNat=2^19 from rfl,
      show 1+bitlen (2^19-1)=20 from rfl] using And.intro ht.2.2.1 ht.2.2.2.1

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
