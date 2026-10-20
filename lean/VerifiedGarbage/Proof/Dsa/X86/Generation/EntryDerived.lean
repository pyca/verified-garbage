module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryArguments
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Entry
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs

/-! # Derive persistent workspace addresses without changing incoming arguments -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem storeEntrySlot_ok {base : Addr} {args W : Nat → BitVec 32} {s : State} {slot : Nat}
    (R : EntryArguments base args s) (words : FrameWords s.mem base W) (hs : slot < 37) :
    WP isa (.block [.store (frameSlot slot) .eax]) s fun t =>
      EntryArguments base args t ∧ FrameWords t.mem base (frameUpdate W slot (s.gpr .eax)) ∧
      Frame [⟨base, VG.Impl.Dsa.X86.Generation.frameBytes⟩] s.mem t.mem ∧ Keeps [] s t := by
  refine wp_storeS (R.frame.ea hs) (R.frame.writable hs) fun t st => WP.block_nil ?_
  have O : Frame [⟨base, VG.Impl.Dsa.X86.Generation.frameBytes⟩] s.mem t.mem := by
    rw [st.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains_base _ (by unfold VG.Impl.Dsa.X86.Generation.frameBytes; omega) (by omega))
  exact ⟨R.keep O (st.keeps []) (by decide), by rw [st.mem]; exact words.write hs _, O, st.keeps []⟩

def derivedWords (W : Nat → BitVec 32) (pairs : List (Nat × Nat)) : Nat → BitVec 32 :=
  pairs.foldl (fun words pair => frameUpdate words pair.1 (words 5 + BitVec.ofNat 32 pair.2)) W

theorem entryDerivedList_ok {base : Addr} {args W : Nat → BitVec 32} {s : State} (pairs : List (Nat × Nat))
    (R : EntryArguments base args s) (words : FrameWords s.mem base W)
    (bounds : ∀ pair ∈ pairs, pair.1 < 37) :
    WP isa (.block (pairs.flatMap fun (slot, offset) => bufferPointer .eax offset ++ ([.store (frameSlot slot) .eax] : List Instr))) s
      fun t => EntryArguments base args t ∧ FrameWords t.mem base (derivedWords W pairs) ∧
        Frame [⟨base, VG.Impl.Dsa.X86.Generation.frameBytes⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  induction pairs generalizing s W with
  | nil => exact WP.block_nil ⟨R, words, Frame.refl _ _, Keeps.refl _ _⟩
  | cons pair rest ih =>
    obtain ⟨slot, offset⟩ := pair
    rw [List.flatMap_cons, List.append_assoc]
    refine WP.block_append (WP.mono (bufferPointer_ok R.frame (words 5 (by decide)) .eax offset)
      fun a ⟨ax, mem, Ka⟩ => ?_)
    have Oa : Frame [⟨base, VG.Impl.Dsa.X86.Generation.frameBytes⟩] s.mem a.mem := by rw [mem]; exact Frame.refl _ _
    have Ra := R.keep Oa Ka (by decide)
    have Wa : FrameWords a.mem base W := by rw [mem]; exact words
    refine WP.block_append (WP.mono (storeEntrySlot_ok Ra Wa (bounds (slot, offset) List.mem_cons_self))
      fun b ⟨Rb, Wb, Ob, Kb⟩ => ?_)
    rw [ax] at Wb
    refine WP.mono (ih Rb Wb (fun pair hp => bounds pair (List.mem_cons_of_mem _ hp))) fun t ⟨Rt, Wt, Ot, Kt⟩ => ?_
    exact ⟨Rt, Wt, Oa.trans (Ob.trans Ot), Ka.trans ((Kb.mono (by simp)).trans Kt)⟩

theorem entryDerived_ok {base : Addr} {args W : Nat → BitVec 32} {s : State}
    (R : EntryArguments base args s) (words : FrameWords s.mem base W) :
    WP isa (.block entryDerived) s fun t => EntryArguments base args t ∧
      FrameWords t.mem base (frameUpdate (derivedWords W derivedSlots) 16 0) ∧
      Frame [⟨base, VG.Impl.Dsa.X86.Generation.frameBytes⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold entryDerived
  refine WP.block_append (WP.mono (entryDerivedList_ok derivedSlots R words (by
    intro pair hp; simp only [derivedSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> decide)) fun a ⟨Ra, Wa, Oa, Ka⟩ => ?_)
  refine wp_movS rfl fun b ab _ => ?_
  have Ob : Frame [⟨base, VG.Impl.Dsa.X86.Generation.frameBytes⟩] a.mem b.mem := by rw [ab.mem]; exact Frame.refl _ _
  refine WP.mono (storeEntrySlot_ok (W := derivedWords W derivedSlots) (Ra.keep Ob ab.keeps (by decide)) (by rw [ab.mem]; exact Wa)
    (by decide : 16 < 37)) fun t ⟨Rt, Wt, Ot, Kt⟩ => ?_
  rw [ab.gpr] at Wt
  exact ⟨Rt, Wt, Oa.trans (Ob.trans Ot), Ka.trans (ab.keeps.trans (Kt.mono (by simp)))⟩
end VG.Proof.Dsa.X86.Generation
