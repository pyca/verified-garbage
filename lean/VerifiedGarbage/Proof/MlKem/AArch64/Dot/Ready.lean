module

public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

/-- Caller-level requirements; input polynomials may alias one another. -/
structure Ready (s : State) (p t : Addr) (terms : List (Nat × Nat))
    (F G : (Nat × Nat) → Poly) : Prop where
  count : terms.length ≤ 4
  offF : ∀ fg ∈ terms, fg.1 < 65536
  offG : ∀ fg ∈ terms, fg.2 < 65536
  inputF : ∀ fg ∈ terms, PolyIs s.mem (s.gpr .x28+BitVec.ofNat 64 fg.1) (F fg)
  inputG : ∀ fg ∈ terms, PolyIs s.mem (s.gpr .x28+BitVec.ofNat 64 fg.2) (G fg)
  apartF : ∀ fg ∈ terms, (polyRegion p).Disjoint (polyRegion (s.gpr .x28+BitVec.ofNat 64 fg.1))
  apartG : ∀ fg ∈ terms, (polyRegion p).Disjoint (polyRegion (s.gpr .x28+BitVec.ofNat 64 fg.2))
  readF : ∀ fg ∈ terms, Covers [polyRegion (s.gpr .x28+BitVec.ofNat 64 fg.1)] (s.rd++s.wr)
  readG : ∀ fg ∈ terms, Covers [polyRegion (s.gpr .x28+BitVec.ofNat 64 fg.2)] (s.rd++s.wr)
  write : Covers [polyRegion p] s.wr
  tableApart : (polyRegion p).Disjoint ⟨t,512⟩
  tableRead : Covers [⟨t,512⟩] (s.rd++s.wr)
  table : GammaArtifact s.mem t

theorem Ready.data {s : State} {p t : Addr} {terms : List (Nat × Nat)}
    {F G : (Nat × Nat) → Poly} (h : Ready s p t terms F G) :
    LoopData s p t terms (polyValues F) (polyValues G) gammaValues := by
  refine ⟨h.count,h.offF,h.offG,?_,?_,?_,?_,h.apartF,h.apartG,?_,?_,?_,h.tableApart,?_,?_,?_⟩
  · intro fg hf i hi; exact ((F fg)[i]!).isLt
  · intro fg hf i hi; exact ((G fg)[i]!).isLt
  · intro fg hf i hi; exact polyIs_toNat (h.inputF fg hf) hi
  · intro fg hf i hi; exact polyIs_toNat (h.inputG fg hf) hi
  · intro fg hf j hj
    exact h.readF fg hf _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  · intro fg hf j hj
    exact h.readG fg hf _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  · intro j hj
    exact h.write _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  · intro c hc
    exact h.tableRead _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  · intro c hc; exact h.table.lanes hc
  · intro i hi; exact (gamma i).isLt

end VG.Proof.MlKem.AArch64.Dot
