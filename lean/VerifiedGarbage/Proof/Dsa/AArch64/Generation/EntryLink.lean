module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntrySpill
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ABIContext
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryState
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryInitial
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToDual

/-! Save the incoming link register outside the persistent generation words. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem link_sub (s : State) : Region.Sub (linkRegion s) (below s.sp 464) := by
  intro a ha
  apply Offset.sub_below s.sp (a := 448) (n := 448) (b := 464) (m := 464) (by decide) (by decide)
  exact Offset.sub_base (generationBase s) (d := 296) (n := 152) (k := 448) (by decide) a ha

theorem link_frame (s : State) : Frame [linkRegion s] s.mem (linkState s).mem := by
  have gp := Spill.saveMem_frame (l := Impl.Dsa.AArch64.Generation.abiGprs) (lo := 296) (n := 152)
    (by decide) (by decide) s.mem (generationBase s) s.gpr
  have vp := Spill.saveMem_frame (l := vectorSlots) (lo := 296) (n := 152)
    (by decide) (by decide)
    (Spill.saveMem s.mem (generationBase s) s.gpr Impl.Dsa.AArch64.Generation.abiGprs)
    (generationBase s) (vectorValues s)
  have ff : Frame [linkRegion s] s.mem (savedAbiMem s) := gp.trans vp
  have hc : (linkRegion s).Contains (linkRegion s).base 8 := by
    have hc := Offset.contains_base (off (generationBase s) 296) (d := 0) (n := 8) (k := 152)
      (by decide) (by decide)
    simpa only [linkRegion, off, BitVec.add_zero] using hc
  exact ff.writeW (r := linkRegion s) (by simp) (s.gpr .x30) hc

theorem link_tape {s : State} (h : GenerationABI s) (ptr : Addr) (len : BitVec 64)
    (bound : ptr.toNat + len.toNat ≤ 2 ^ 64)
    (arena : (⟨ptr, len.toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩)
    (stack : (below s.sp 464).Disjoint ⟨ptr, len.toNat⟩)
    (hin : (⟨ptr, len.toNat⟩ : Region) ∈ s.rd) :
    GenerationTapeMemory (tapeOf h ptr len bound arena stack) (linkState s) where
  cover := (allocated_tape h ptr len bound arena stack hin).cover
  bytes := by
    change Spec.Rsa.bytesAt (linkState s).mem ptr (Spec.Rsa.bytesAt s.mem ptr len.toNat).length = _
    rw [bytesAt_length]
    apply VG.Proof.Dsa.Generation.frame_bytesAt (link_frame s)
    · intro r hr
      rcases List.mem_singleton.mp hr with rfl
      exact (stack.sub_left (link_sub s)).symm
    · exact Nat.le_of_lt len.isLt

theorem entryInitial_link {s : State} (h : GenerationABI s) :
    EntryState (contextOf h) (linkState s) := by
  have init := entryInitial h
  refine {
    sp := init.sp
    frame := init.frame
    frameTop := init.frameTop
    scratch := init.scratch.congr rfl
    registers := by
      intro slot hs
      simp only [headerSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    incoming := ?_
    incomingRead := init.incomingRead
    hashScratch := init.hashScratch
    seeds := link_tape h _ _ h.seedsBound h.seedsScratch h.stackSeeds (by rw [h.rd]; simp)
    hs := link_tape h _ _ h.hsBound h.hsScratch h.stackHs (by rw [h.rd]; simp)
    rand := link_tape h _ _ h.randBound h.randScratch h.stackRand (by rw [h.rd]; simp) }
  intro slot hs
  have bound := argumentSlots_bounds hs
  have same := (link_frame s).readW (w := 64)
    (r := ⟨off (generationBase s) slot.1, 8⟩) (Region.contains_self _ _) (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      apply Offset.disjoint
      · right
        simp only [argumentSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl <;> decide
      · exact bound.2
      · decide) (by decide : 64 / 8 < 2 ^ 64)
  exact same.trans (init.incoming slot hs)

end VG.Proof.Dsa.AArch64.Generation
