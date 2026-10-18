module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryInitial
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Framework.Omega

/-! Save the incoming link register outside the persistent generation words. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def linkRegion (s : State) : Region := ⟨off (generationBase s) 296, 8⟩

def linkState (s : State) : State :=
  { allocState 320 s with mem := s.mem.writeW (linkRegion s).base (s.gpr .x30) }

theorem link_sub (s : State) : Region.Sub (linkRegion s) (below s.sp 336) := by
  intro a ha
  apply Offset.sub_below s.sp (a := 320) (n := 320) (b := 336) (m := 336) (by decide) (by decide)
  exact Offset.sub_base (generationBase s) (d := 296) (n := 8) (k := 320) (by decide) a ha

theorem link_frame (s : State) : Frame [linkRegion s] s.mem (linkState s).mem :=
  (Frame.refl _ _).writeW (r := linkRegion s) (by simp) _ (Region.contains_self _ _)

theorem entrySave_ok (s : State) :
    WP isa (.block [.strSp .x30 296]) (allocState 320 s) (fun t => t = linkState s) := by
  have hw : InRegions (allocState 320 s).wr ((allocState 320 s).sp + BitVec.ofNat 64 296) 8 :=
    ⟨⟨generationBase s, 320⟩, List.mem_cons_self .., Offset.contains_base _ (by decide) (by decide)⟩
  brun [exec_storeSp (off := 296) (by decide), hw]
  rfl

theorem link_tape {s : State} (h : GenerationABI s) (ptr : Addr) (len : BitVec 64)
    (bound : ptr.toNat + len.toNat ≤ 2 ^ 64)
    (arena : (⟨ptr, len.toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩)
    (stack : (below s.sp 336).Disjoint ⟨ptr, len.toNat⟩)
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
    registers := init.registers
    incoming := ?_
    incomingRead := init.incomingRead
    hashScratch := init.hashScratch
    seeds := link_tape h _ _ h.seedsBound h.seedsScratch h.stackSeeds (by rw [h.rd]; simp)
    hs := link_tape h _ _ h.hsBound h.hsScratch h.stackHs (by rw [h.rd]; simp)
    rand := link_tape h _ _ h.randBound h.randScratch h.stackRand (by rw [h.rd]; simp) }
  intro slot hs
  have bound := argumentSlots_bounds hs
  have outside := writeW_outside s.mem (generationBase s) (d := 296) (s.gpr .x30) (by decide)
  have same := outside.word (d := slot.1) (Or.inr (by
    simp only [argumentSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> decide)) bound.2
  exact same.trans (init.incoming slot hs)

end VG.Proof.Dsa.AArch64.Generation
