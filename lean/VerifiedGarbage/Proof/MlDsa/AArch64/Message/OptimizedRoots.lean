module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots StaticTable signRootConsts)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message

/-- Reborrowing for the inner signer retains both tables and narrows only
writable buffers; the immutable addresses remain those of the symbol map. -/
theorem roots_reborrow {s : State} {rd wr : List Region} (h : StaticRoots 16 s)
    (hr : rootRegions s⊆rd) (hw : Covers wr s.wr) :
    StaticRoots 16 (s.callEntry.withRegions rd wr) := by
  have transfer {nm : String} {ws : List (BitVec 64)} (ht : StaticTable 16 nm ws s)
      (hm : (⟨s.syms nm,3904⟩ : Region)∈rd) :
      StaticTable 16 nm ws (s.callEntry.withRegions rd wr) := by
    refine ⟨ht.held,ht.fit,?_,?_,ht.stack,ht.aligned⟩
    · apply Covers.one
      exact ⟨⟨s.syms nm,3904⟩,List.mem_append_left _ hm,Region.contains_self _ _⟩
    · intro r hmem
      exact ht.apart_write (hw r.base r.len ⟨r,hmem,Region.contains_self _ _⟩)
  exact ⟨transfer h.forward (hr (by simp [rootRegions])),
    transfer h.inverse (hr (by simp [rootRegions]))⟩

end VG.Proof.MlDsa.AArch64.Message.Optimized
