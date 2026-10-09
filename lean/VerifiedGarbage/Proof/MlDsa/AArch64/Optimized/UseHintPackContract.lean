import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackProg
import VerifiedGarbage.Proof.MlKem.AArch64.Common

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Arith (polyRegion)
open HighPack (packWidth)

def packK (g : Nat) : Contract isa where
  pre s := s.rd=[polyRegion (s.gpr .x1),polyRegion (s.gpr .x2)] ∧
    s.wr=[⟨s.gpr .x0,32*packWidth g⟩] ∧
    (polyRegion (s.gpr .x1)).Disjoint ⟨s.gpr .x0,32*packWidth g⟩ ∧
    (polyRegion (s.gpr .x2)).Disjoint ⟨s.gpr .x0,32*packWidth g⟩ ∧
    arg32 s .x3=g ∧ Reduced s.mem (s.gpr .x2)
  post s t := Spec.Sha3.bytesAt t.mem (s.gpr .x0) (32*packWidth g)=
    packed g s.mem (s.gpr .x1) (s.gpr .x2)
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧
    s.gpr .x2=t.gpr .x2 ∧ (s.gpr .x3).setWidth 32=(t.gpr .x3).setWidth 32 ∧ s.sp=t.sp

theorem pack_pre {g : Nat} {s : State} (hp : (packK g).pre s) : Pre g s := by
  obtain ⟨rd,wr,hs,ws,hg,hr⟩ := hp
  refine ⟨hg,hr,?_,?_,?_,ws,hs⟩
  · rw [rd];exact ⟨polyRegion (s.gpr .x2),by simp,Region.contains_self _ _⟩
  · rw [rd];exact ⟨polyRegion (s.gpr .x1),by simp,Region.contains_self _ _⟩
  · rw [wr];exact ⟨_,List.mem_singleton_self _,Region.contains_self _ _⟩

/-- Full selected program satisfies the AArch64 calling convention. -/
theorem pack_correct {g : Nat} (hg : IsG g) (s : State) (hp : (packK g).pre s) :
    ∃ tr t, Exec isa Impl.MlDsa.AArch64.Optimized.UseHintPack.prog s tr t ∧
      abiPreserved s t ∧ (packK g).post s t := by
  obtain ⟨tr,t,he,ht⟩ := prog_ok hg (pack_pre hp)
  exact ⟨tr,t,he,VG.Proof.MlKem.AArch64.abi_of rfl (by decide +kernel) he,ht.bytes⟩

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
