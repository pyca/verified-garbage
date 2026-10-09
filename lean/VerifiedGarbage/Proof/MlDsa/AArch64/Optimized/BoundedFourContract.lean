import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSmall
import VerifiedGarbage.Proof.MlKem.AArch64.Common

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa

def samplerK (η : Nat) : Contract isa where
 pre s := (η=2∨η=4) ∧ SamplerPre s
 post s t := (∀i<4,Reduced t.mem (samplerOut s+BitVec.ofNat 64 (1024*i))) ∧
   (∀i<4,BoundedOutput η t.mem (samplerOut s+BitVec.ofNat 64 (1024*i))) ∧
   Outcome (fun b=>(rejBoundedFour η b.rejBounded s.mem (samplerSeed s)).map (List.map toRq))
     ((t.gpr .x0).setWidth 32)
     ((List.range 4).map fun i=>polyAt t.mem (samplerOut s+BitVec.ofNat 64 (1024*i)))
 pub s t := SamplerPublic η s t

theorem sampler_correct (sha3 : Bool) (η : Nat) (s : State) (h : (samplerK η).pre s) :
    ∃tr t,Exec isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η) s tr t ∧
      abiPreserved s t ∧ (samplerK η).post s t := by
  obtain ⟨tr,t,he,ht⟩:=sampler_machine_ok sha3 h.1 h.2
  exact ⟨tr,t,he,ht.abi,(fun i hi=>ht.reduced hi),(fun i hi=>ht.small hi),ht.outcome⟩

theorem sampler_ct (sha3 : Bool) (η : Nat) :
    ConstantTime isa (samplerK η).pre (samplerK η).pub
      (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η) := by
  intro s t tr ur u v hs ht hp es et
  exact (sampler_relCT sha3 hs.1 hs.2 ht.2 hp s t tr ur u v ⟨rfl,rfl⟩ es et).1

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
