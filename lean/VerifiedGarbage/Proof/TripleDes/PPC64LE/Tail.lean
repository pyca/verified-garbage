module

import VerifiedGarbage.Proof.TripleDes.PPC64LE.Store
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Save
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.WordState
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.BlockIO
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bytes
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

structure TailPost (original origin : State) (x : BitVec 64) (s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (origin.gpr .r4) =
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp x)
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ loadKept, s.gpr q = origin.gpr q
  frame : Frame [⟨origin.gpr .r4, 8⟩] origin.mem s.mem

theorem blockTail_ok (original s : State) (x : BitVec 64)
    (hword : WordState x s) (hsaved : Saved original s)
    (hsavedRead : ∀ i < 15, InRegions (s.rd ++ s.wr) (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8)
    (hwrite : InRegions s.wr (s.gpr .r4) 8)
    (hsep : (⟨s.gpr .r4, 8⟩ : Region).Disjoint ⟨s.gpr .r5, 120⟩) :
    WP isa (.block (blockStore ++ blockRestore)) s (TailPost original s x) := by
  obtain ⟨s₁, run₁, mem₁, rd₁, wr₁, regs₁⟩ :=
    blockStore_ok s ((x >>> 32).setWidth 32) (x.setWidth 32) hword.left hword.right hwrite
  have hframe₁ : Frame [⟨s.gpr .r4, 8⟩] s.mem s₁.mem := by
    rw [mem₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have saved₁ : Saved original s₁ := by
    intro i hi
    rw [regs₁ .r5 (by decide)]
    refine (hframe₁.readW (r := ⟨s.gpr .r5 + BitVec.ofNat 64 (8 * i), 8⟩)
      (Region.contains_self _ _) (fun q hq => ?_) (by decide)).trans (hsaved i hi)
    obtain rfl := List.mem_singleton.mp hq
    exact (hsep.sub_right (Offset.sub_base _ (by omega))).symm
  have savedRead₁ : ∀ i < 15, InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [rd₁, wr₁, regs₁ .r5 (by decide)]
    exact hsavedRead
  apply WP.block_append
  apply WP.of_runBlock
  refine ⟨s₁, run₁, ?_⟩
  apply WP.mono (blockRestore_ok original s₁ saved₁ savedRead₁)
  intro s₂ hs₂
  have hregs₂ : ∀ q ∈ loadKept, s₂.gpr q = s.gpr q := by
    intro q hq
    have hn : q ∉ savedRegs := by revert hq; cases q <;> decide
    exact (hs₂.keep.gpr hn).trans (regs₁ q hq)
  refine ⟨?_, hs₂.saved, hs₂.keep.2.1.trans rd₁, hs₂.keep.2.2.trans wr₁, hregs₂, ?_⟩
  · rw [hs₂.mem, mem₁, VG.Proof.TripleDes.halves_append x]
    exact blockAt_writeW s.mem (s.gpr .r4) (Spec.TripleDes.permute Spec.TripleDes.fp x)
  · rw [hs₂.mem]; exact hframe₁

end VG.Proof.TripleDes.PPC64LE
