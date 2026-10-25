module
public import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Loop
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table

import VerifiedGarbage.Proof.MlKem.PolyW

/-! # The fused dot product of 16-bit polynomials in 1024-byte buffers

`ReadyW`: `Dot.Ready` for polynomials stored with 16 bits in the first half of
buffers of 1024 bytes, from which `ReadyW.data` gives `dotW`'s `LoopDataW`. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Dot

structure ReadyW (s : State) (p t : Addr) (terms : List (Nat × Nat))
    (F G : (Nat × Nat) → Poly) : Prop where
  count : terms.length ≤ 4
  offF : ∀ fg ∈ terms, fg.1 < 65536
  offG : ∀ fg ∈ terms, fg.2 < 65536
  inputF : ∀ fg ∈ terms, PolyIsW 16 s.mem (s.gpr .x28+BitVec.ofNat 64 fg.1) (F fg)
  inputG : ∀ fg ∈ terms, PolyIsW 16 s.mem (s.gpr .x28+BitVec.ofNat 64 fg.2) (G fg)
  apartF : ∀ fg ∈ terms, (polyRegion p).Disjoint (polyRegion (s.gpr .x28+BitVec.ofNat 64 fg.1))
  apartG : ∀ fg ∈ terms, (polyRegion p).Disjoint (polyRegion (s.gpr .x28+BitVec.ofNat 64 fg.2))
  readF : ∀ fg ∈ terms, Covers [polyRegion (s.gpr .x28+BitVec.ofNat 64 fg.1)] (s.rd++s.wr)
  readG : ∀ fg ∈ terms, Covers [polyRegion (s.gpr .x28+BitVec.ofNat 64 fg.2)] (s.rd++s.wr)
  write : Covers [polyRegion p] s.wr
  tableApart : (polyRegion p).Disjoint ⟨t,512⟩
  tableRead : Covers [⟨t,512⟩] (s.rd++s.wr)
  table : GammaArtifact s.mem t

theorem half_sub (p : Addr) : Region.Sub ⟨p, 512⟩ (polyRegion p) := Region.sub_prefix (by decide)

theorem ReadyW.data {s : State} {p t : Addr} {terms : List (Nat × Nat)}
    {F G : (Nat × Nat) → Poly} (h : ReadyW s p t terms F G) :
    LoopDataW s .x28 .x28 p t terms (polyValues F) (polyValues G) gammaValues := by
  refine ⟨by decide, by decide, h.count, h.offF, h.offG, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (h.tableApart.sub_left (half_sub p)), ?_, ?_, ?_⟩
  · intro fg _ i _; exact ((F fg)[i]!).isLt
  · intro fg _ i _; exact ((G fg)[i]!).isLt
  · intro fg hf i hi; exact polyIsW_toNat (h.inputF fg hf) hi
  · intro fg hf i hi; exact polyIsW_toNat (h.inputG fg hf) hi
  · intro fg hf; exact ((h.apartF fg hf).sub_left (half_sub p)).sub_right (half_sub _)
  · intro fg hf; exact ((h.apartG fg hf).sub_left (half_sub p)).sub_right (half_sub _)
  · intro fg hf o ho
    exact h.readF fg hf _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  · intro fg hf o ho
    exact h.readG fg hf _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  · intro o ho
    exact h.write _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  · intro c hc
    exact h.tableRead _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  · intro c hc; exact h.table.lanes hc
  · intro i _; exact (gamma i).isLt

end VG.Proof.MlKem.AArch64.DotW
