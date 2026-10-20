module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.EntryBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Incoming

/-! Retain the appended readonly context pointer and word count in state word four. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

def entryCacheMem (p : KeyPublic sampling) (m : Mem) : Mem :=
  (m.writeW (off (State.addr p.control) 32) p.context).writeW
    (off (State.addr p.control) 36) (BitVec.ofNat 32 p.contextWords)

theorem entryCache_frame (p : KeyPublic sampling) (m : Mem) :
    Frame [⟨State.addr p.control,128⟩] m (entryCacheMem p m) := by
  unfold entryCacheMem
  apply Frame.writeW
  · exact (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide : 32+4≤128) (by decide))
  · exact List.mem_cons_self
  · exact Offset.contains_base _ (by decide : 36+4≤128) (by decide)

theorem entryCache_ok (s : State) {p : KeyPublic sampling} (h : EntryContext p s)
    (cached : sampling.cachedContext=true) :
    WP isa (.block [.ldrSp .r3 60,.str .r3 .r4 32,.ldrSp .r3 64,.str .r3 .r4 36]) s fun t =>
      (EntryContext p t ∧ t.mem=entryCacheMem p s.mem) ∧ Rest [.r3] s t := by
  have a9 := h.incoming 9 (by simp only [entryWords,cached,ite_true]; decide)
  have a10 := h.incoming 10 (by simp only [entryWords,cached,ite_true]; decide)
  have a60 : State.addr (s.sp+BitVec.ofNat 32 60)=off (State.addr s.sp) 60 := addr_add (by have := a9.fits; omega)
  have a64 : State.addr (s.sp+BitVec.ofNat 32 64)=off (State.addr s.sp) 64 := addr_add (by have := a10.fits; omega)
  have d32 : State.addr (p.control+BitVec.ofNat 32 32)=off (State.addr p.control) 32 := addr_add (by have := h.controller.space.nowrap; omega)
  have d36 : State.addr (p.control+BitVec.ofNat 32 36)=off (State.addr p.control) 36 := addr_add (by have := h.controller.space.nowrap; omega)
  have raw : WP isa (.block [.ldrSp .r3 60,.str .r3 .r4 32,.ldrSp .r3 64,.str .r3 .r4 36]) s fun t =>
      t.mem=entryCacheMem p s.mem ∧ Rest [.r3] s t := by
    refine withRest [.r3] ?_ (by
      intro r hr i hi
      simp only [instrs,List.mem_cons,List.not_mem_nil,or_false] at hi
      have ne : r≠.r3 := by simpa only [List.mem_singleton] using hr
      rcases hi with rfl|rfl|rfl|rfl <;> simp [clobbers,dstOf,Ne.symm ne]) rfl
    have kept : s.mem.readW (off (State.addr s.sp) 64) 32 =
        (s.mem.writeW (off (State.addr p.control) 32) p.context).readW (off (State.addr s.sp) 64) 32 := by
      symm
      exact Mem.readW_writeW_sep
        ((h.separate 10 (by rw [entryWords,cached]; decide)).sep
          (Region.contains_self _ _) (Offset.contains_base _ (by decide : 32+4≤128) (by decide))) (by decide)
    unfold entryCacheMem
    ffrun [a60,a64,d32,d36,h.controller.ptr,a9.readable,a9.word,a10.readable,a10.word,
      incomingValue,h.controller.space.write (off:=32) (by decide),
      h.controller.space.write (off:=36) (by decide),←kept]
  refine WP.mono raw ?_
  rintro t ⟨mem,rest⟩
  have frame : Frame [⟨State.addr p.control,128⟩] s.mem t.mem := by rw [mem]; exact entryCache_frame p s.mem
  exact ⟨⟨h.after rest (by simp) frame,mem⟩,rest⟩

end VG.Proof.Ffdh.Arm.KeySearch
