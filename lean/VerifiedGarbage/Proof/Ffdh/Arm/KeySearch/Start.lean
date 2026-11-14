module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Push
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Memory
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Packed
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.PushedArguments
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ConstantMemory
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CachedGeometry
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.EntryBlocks
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Fields
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Incoming
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Block

/-! ### `Ffdh.Arm.KeySearch.InitialWords`, which only this module used -/

section

/-! Exact native halves of the initialized retry counters and domain width. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Spec.Ffdh

theorem KeyInput.initial_words {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    s.mem.readW (off (State.addr p.control) 0) 64 = BitVec.ofNat 64 p.keys ∧
    s.mem.readW (off (State.addr p.control) 8) 64 = BitVec.ofNat 64 p.scalars ∧
    s.mem.readW (off (State.addr p.control) 16) 64 = BitVec.ofNat 64 p.len := by
  have pre := h.1
  cases h.2.1
  refine ⟨?_, ?_, ?_⟩
  · simp only [keyOfState, BitVec.ofNat_toNat, BitVec.setWidth_eq, off, BitVec.add_zero]
  · simp only [keyOfState, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · cases sampling <;>
      sig_pre [GenerationPolicy.searchContract,GenerationPolicy.legacySearchContract,
        cachedKeySearchContract,cachedKeySearchSig,keySearchSig,abi,argRegs,reduceClassify,Loc.val,State.addr] at pre
    all_goals simp only [KeyConstants.stackArg_stripConsts,KeyConstants.stackArgAddr_stripConsts] at pre
    all_goals sig_split pre
    all_goals
      have value : s.mem.readW (BitVec.setWidth 64 (stackArg s 8)+(16 : BitVec 64)) 64 = BitVec.ofNat 64 (stackArg s 3).toNat := by assumption
      simpa only [keyOfState,off,State.addr,BitVec.ofNat_toNat,show (16 : BitVec 64)=16#64 from rfl] using value

theorem KeyInput.pushed_word {p : KeyPublic sampling} {s : State} {j : Nat} (h : KeyInput p s) (bound : j < 3) :
    (searchPushed s).mem.readW (off (State.addr p.control) (8 * j)) 64 =
      s.mem.readW (off (State.addr p.control) (8 * j)) 64 := by
  have fit : stackUse sampling ≤ p.sp.toNat := h.bounds.stackFits
  have rootFit : 24 ≤ s.sp.toNat := by rw [← h.2.1] at fit; change stackUse sampling ≤ s.sp.toNat at fit; have := stackUse_min sampling; omega_using [fit, this]
  have frame : Frame [FrameStack.belowA s.sp 24] s.mem (searchPushed s).mem :=
    FrameStack.pushed_frameA (rs := [.r4, .r9, .r10, .r11, .r12, .lr]) rootFit
  have sep : (rControl p).Disjoint (FrameStack.belowA s.sp 24) := by
    have base : p.sp = s.sp := by rw [← h.2.1]; rfl
    rw [← base]
    exact h.saved_control.symm
  exact frame.readW (r := rControl p) (Offset.contains_base _ (by omega_using [bound]) (by omega_using [bound]))
    (by simpa using sep) (by decide)

theorem KeyInput.pushed_policy {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    lowWord (searchPushed s).mem p.control 0 = BitVec.ofNat 32 p.keys ∧
    lowWord (searchPushed s).mem p.control 1 = BitVec.ofNat 32 p.scalars ∧
    lowWord (searchPushed s).mem p.control 2 = BitVec.ofNat 32 p.len ∧
    (∀ j < 3, (searchPushed s).mem.readW (off (State.addr p.control) (8 * j + 4)) 32 = 0) := by
  have w0 := (h.pushed_word (j := 0) (by decide)).trans h.initial_words.1
  have w1 := (h.pushed_word (j := 1) (by decide)).trans h.initial_words.2.1
  have w2 := (h.pushed_word (j := 2) (by decide)).trans h.initial_words.2.2
  have keys : p.keys < 2 ^ 32 := by have := h.bounds.keys; omega_using [this]
  have scalars : p.scalars < 2 ^ 32 := by have := h.bounds.scalars; omega_using [this]
  have len : p.len < 2 ^ 32 := by have := h.bounds.maxLength; omega_using [this]
  refine ⟨packed_low _ _ _ _ keys w0, packed_low _ _ _ _ scalars w1, packed_low _ _ _ _ len w2, ?_⟩
  intro j hj
  have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega_using [hj]
  rcases casesJ with rfl | rfl | rfl
  · exact packed_high _ _ _ _ keys w0
  · exact packed_high _ _ _ _ scalars w1
  · exact packed_high _ _ _ _ len w2

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! ### `Ffdh.Arm.KeySearch.Entry`, which only this module used -/

section

/-! Exact argument snapshot made before entering the key-search loop. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

def entryValues (p : KeyPublic sampling) : List (Nat × BitVec 32) :=
  [(5, p.xp), (6, p.yp), (15, p.up), (7, p.dp), (8, BitVec.ofNat 32 p.dlen),
    (9, p.rp), (10, BitVec.ofNat 32 p.randLen), (12, p.scratch),
    (13, BitVec.ofNat 32 p.capacity), (11, 0)]

theorem entryValues_bound (p : KeyPublic sampling) : ∀ e ∈ entryValues p, e.1 < 16 := by
  simp only [entryValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem entry_base_ok (s : State) {p : KeyPublic sampling} (h : EntryArguments p s)
    (space : Workspace s p.control 128) (x : s.gpr .r0 = p.xp) (y : s.gpr .r2 = p.yp) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.entry) s fun t =>
      (EntryContext p t ∧ t.mem = writeLow s.mem p.control (entryValues p)) ∧ Rest [.r3, .r4] s t := by
  refine withRest_all [.r3, .r4] ?_ (by rfl) (by rfl)
  change WP isa (.block ([.ldrSp .r4 56, VG.Impl.Ffdh.Arm.KeySearch.stf .r0 5,
    VG.Impl.Ffdh.Arm.KeySearch.stf .r2 6] ++ _)) s _
  rw [WP.block_append_iff]
  refine WP.mono (entryHead_ok s h space x y) ?_
  rintro u ⟨⟨pointer, mem⟩, rest⟩
  have frame : Frame [⟨State.addr p.control, 128⟩] s.mem u.mem := by
    rw [mem]; exact writeLow_frame _ _ _ (by simp)
  have context : EntryContext p u :=
    ⟨h.after rest frame, ⟨space.congr rest.wr, pointer⟩⟩
  refine wp_entryCopy (i := 0) (j := 15) context (by have := entryWords_min sampling; omega_using [this]) (by decide) fun s1 c1 m1 _ => ?_
  refine wp_entryCopy (i := 1) (j := 7) c1 (by have := entryWords_min sampling; omega_using [this]) (by decide) fun s2 c2 m2 _ => ?_
  refine wp_entryCopy (i := 2) (j := 8) c2 (by have := entryWords_min sampling; omega_using [this]) (by decide) fun s3 c3 m3 _ => ?_
  refine wp_entryCopy (i := 4) (j := 9) c3 (by have := entryWords_min sampling; omega_using [this]) (by decide) fun s4 c4 m4 _ => ?_
  refine wp_entryCopy (i := 5) (j := 10) c4 (by have := entryWords_min sampling; omega_using [this]) (by decide) fun s5 c5 m5 _ => ?_
  refine wp_entryCopy (i := 6) (j := 12) c5 (by have := entryWords_min sampling; omega_using [this]) (by decide) fun s6 c6 m6 _ => ?_
  refine wp_entryCopy (i := 7) (j := 13) c6 (by have := entryWords_min sampling; omega_using [this]) (by decide) fun s7 c7 m7 _ => ?_
  refine WP.mono (entryZero_ok s7 c7) ?_
  rintro t ⟨m8, r8⟩
  have frame8 : Frame [⟨State.addr p.control, 128⟩] s7.mem t.mem := by
    rw [m8]
    exact (Frame.refl _ _).writeW (r := ⟨State.addr p.control, 128⟩) (by simp) (0#32)
      (Offset.contains_base _ (by decide : 88 + 4 ≤ 128) (by decide))
  refine ⟨c7.after r8 (by simp) frame8, ?_⟩
  rw [m8, m7, m6, m5, m4, m3, m2, m1, mem]
  rfl

theorem entry_fields (p : KeyPublic sampling) (m : Mem)
    (keys : lowWord m p.control 0 = BitVec.ofNat 32 p.keys)
    (scalars : lowWord m p.control 1 = BitVec.ofNat 32 p.scalars)
    (width : lowWord m p.control 2 = BitVec.ofNat 32 p.len) :
    Slots (writeLow m p.control (entryValues p)) p.control (p.headers 0 p.keys p.scalars) := by
  apply (slots_fields _ _ _ _ _ _).mpr
  intro j hj
  rw [lowWord_writeLow _ _ _ (entryValues_bound p) j (headerIndices_bound hj)]
  simp only [headerIndices, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [entryValues, lowValue, KeyPublic.field, keys, scalars, width]

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! ### `Ffdh.Arm.KeySearch.EntryCache`, which only this module used -/

section

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
  have a60 : State.addr (s.sp+BitVec.ofNat 32 60)=off (State.addr s.sp) 60 := addr_add (by have := a9.fits; omega_using [this])
  have a64 : State.addr (s.sp+BitVec.ofNat 32 64)=off (State.addr s.sp) 64 := addr_add (by have := a10.fits; omega_using [this])
  have d32 : State.addr (p.control+BitVec.ofNat 32 32)=off (State.addr p.control) 32 := addr_add (by have := h.controller.space.nowrap; omega_using [this])
  have d36 : State.addr (p.control+BitVec.ofNat 32 36)=off (State.addr p.control) 36 := addr_add (by have := h.controller.space.nowrap; omega_using [this])
  have raw : WP isa (.block [.ldrSp .r3 60,.str .r3 .r4 32,.ldrSp .r3 64,.str .r3 .r4 36]) s fun t =>
      t.mem=entryCacheMem p s.mem ∧ Rest [.r3] s t := by
    refine withRest_all [.r3] ?_ (by rfl) rfl
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

end

end

/-! The native entry code establishes the complete key-search loop invariant. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeySearch/EntryFor.lean`, which only this module imported.
section

/-! The same entry snapshot optionally retains the two cached-context arguments. -/

section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

def entryMem (p : KeyPublic sampling) (m : Mem) : Mem :=
  if sampling.cachedContext then entryCacheMem p (writeLow m p.control (entryValues p))
  else writeLow m p.control (entryValues p)

theorem entryMem_frame (p : KeyPublic sampling) (m : Mem) :
    Frame [⟨State.addr p.control,128⟩] m (entryMem p m) := by
  unfold entryMem
  split
  · exact (writeLow_frame _ _ _ (entryValues_bound p)).trans (entryCache_frame _ _)
  · exact writeLow_frame _ _ _ (entryValues_bound p)

theorem entry_ok (s : State) {p : KeyPublic sampling} (h : EntryArguments p s)
    (space : Workspace s p.control 128) (x : s.gpr .r0=p.xp) (y : s.gpr .r2=p.yp) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.entryFor sampling.cachedContext)) s fun t =>
      (EntryContext p t ∧ t.mem=entryMem p s.mem) ∧ Rest [.r3,.r4] s t := by
  rw [VG.Impl.Ffdh.Arm.KeySearch.entryFor,WP.block_append_iff]
  refine WP.mono (entry_base_ok s h space x y) ?_
  rintro u ⟨⟨context,mem⟩,rest⟩
  by_cases cached : sampling.cachedContext=true
  · simp only [cached,ite_true]
    refine WP.mono (entryCache_ok u context cached) ?_
    rintro t ⟨⟨ct,memT⟩,restT⟩
    refine ⟨⟨ct,?_⟩,rest.trans (restT.mono (by simp))⟩
    rw [memT,mem,entryMem,ite_eq_left cached]
  · simp only [cached]
    exact WP.block_nil ⟨⟨context,by rw [entryMem,ite_eq_right cached]; exact mem⟩,rest⟩

theorem entryCache_read (p : KeyPublic sampling) (m : Mem) {d : Nat}
    (bound : d+4≤128) (sep : d+4≤32 ∨ 40≤d) :
    (entryCacheMem p m).readW (off (State.addr p.control) d) 32 =
      m.readW (off (State.addr p.control) d) 32 := by
  unfold entryCacheMem
  rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]

theorem entryMem_fields (p : KeyPublic sampling) (m : Mem)
    (keys : lowWord m p.control 0=BitVec.ofNat 32 p.keys)
    (scalars : lowWord m p.control 1=BitVec.ofNat 32 p.scalars)
    (width : lowWord m p.control 2=BitVec.ofNat 32 p.len) :
    Slots (entryMem p m) p.control (p.headers 0 p.keys p.scalars) := by
  have old := entry_fields p m keys scalars width
  unfold entryMem
  split
  · apply (slots_fields _ _ _ _ _ _).mpr
    intro j hj
    change (entryCacheMem p _).readW _ 32 = _
    rw [entryCache_read _ _ (by have := headerIndices_bound hj; omega) (by
      simp only [headerIndices,List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]
    exact (slots_fields _ _ _ _ _ _).mp old j hj
  · exact old

theorem entryMem_high (p : KeyPublic sampling) (m : Mem) {j : Nat} (hj : j<3) :
    (entryMem p m).readW (off (State.addr p.control) (8*j+4)) 32 =
      m.readW (off (State.addr p.control) (8*j+4)) 32 := by
  unfold entryMem
  split
  · rw [entryCache_read _ _ (by omega) (by omega)]
    exact highWord_writeLow _ _ _ (entryValues_bound p) j (by omega)
  · exact highWord_writeLow _ _ _ (entryValues_bound p) j (by omega)

theorem entryMem_cached (p : KeyPublic sampling) (m : Mem) : CachedSlots p (entryMem p m) := by
  intro cached
  rw [entryMem,ite_eq_left cached]
  unfold entryCacheMem
  constructor
  · rw [Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · exact Mem.readW_writeW_self32 _ _ _

end VG.Proof.Ffdh.Arm.KeySearch
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem KeyInput.pushed_read {p : KeyPublic sampling} {s : State} {r : Region}
    (h : KeyInput p s) (read : r ∈ s.rd) :
    Spec.Rsa.bytesAt (searchPushed s).mem r.base r.len = Spec.Rsa.bytesAt s.mem r.base r.len := by
  have rootSp : p.sp = s.sp := by rw [← h.2.1]; rfl
  have fit : stackUse sampling ≤ s.sp.toNat := by rw [← rootSp]; exact h.bounds.stackFits
  have frame : Frame [FrameStack.belowA s.sp 24] s.mem (searchPushed s).mem :=
    FrameStack.pushed_frameA (rs := [.r4, .r9, .r10, .r11, .r12, .lr]) (by change 24 ≤ s.sp.toNat; have := stackUse_min sampling; omega_using [fit, this])
  have sep : r.Disjoint (FrameStack.belowA s.sp 24) := by
    apply Region.Disjoint.symm
    apply (h.stack_separate (List.mem_append_right _ read)).sub_left
    rw [rootSp]
    exact FrameStack.belowA_sub (by cases sampling <;> decide : 24 ≤ (stackUse sampling)) fit
  apply bytesAt_frame frame (by simpa using sep)
  have nowrap := h.layout.nowrap r (by rw [← h.layout.wr, ← h.layout.rd]; exact List.mem_append_right _ read)
  omega_using [nowrap]

theorem start_ok {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.entryFor sampling.cachedContext)) (searchPushed s) fun t =>
      KeyLive p s 0 p.keys p.scalars t := by
  have rootSp : p.sp = s.sp := by rw [← h.2.1]; rfl
  have fit : 24 ≤ s.sp.toNat := by rw [← rootSp]; have := h.bounds.stackFits; have := stackUse_min sampling; omega_arith
  have space : Workspace (searchPushed s) p.control 128 :=
    h.control_space (fun _ hr => List.mem_cons_of_mem _ hr)
  have x : (searchPushed s).gpr .r0 = p.xp := by rw [← h.2.1]; rfl
  have y : (searchPushed s).gpr .r2 = p.yp := by rw [← h.2.1]; rfl
  refine WP.mono_syms (entry_ok (searchPushed s) h.pushed_arguments space x y) ?_
  rintro t ⟨⟨context, mem⟩, rest⟩ syms
  have frame : Frame [rControl p] (searchPushed s).mem t.mem := by
    rw [mem]; exact entryMem_frame _ _
  have saved : Spill.Saved (searchPushed s).mem (State.addr (p.sp - 24#32)) s.gpr savedSlots := by
    rw [rootSp]; exact push_saved s fit
  refine ⟨h, Nat.zero_le _, h.bounds.keys, h.bounds.scalars, rest.rd, ?_, ?_, context.controller.ptr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rest.wr]
    change (⟨State.addr (s.sp - 24#32), 24⟩ :: s.wr) = _
    rw [rootSp]
  · rw [rest.sp]
    change s.sp - 24#32 = p.sp - 24#32
    rw [rootSp]
  · intro r hr
    exact rest.gpr r (by revert r hr; decide)
  · apply saved.frame (lo := 0) (hi := 24) (by decide) frame
    simpa using h.saved_control
  · exact (bytesAt_frame (r := rRandom p) frame (by simpa using h.random_control)
      (by change p.randLen ≤ 2 ^ 64; have := h.bounds.randomFits; omega_using [this])).trans
        (h.pushed_read (r := rRandom p) (by rw [h.read_regions]; simp))
  · have original : Spec.Rsa.bytesAt s.mem (State.addr p.dp) p.dlen = p.dom := by rw [← h.2.1]; rfl
    exact (bytesAt_frame (r := rDomain p) frame (by simpa using h.domain_control)
      (by change p.dlen ≤ 2 ^ 64; have := h.bounds.domainFit; omega_using [this])).trans
        ((h.pushed_read (r := rDomain p) (by rw [h.read_regions]; simp)).trans original)
  · rw [mem]
    exact entryMem_fields p _ h.pushed_policy.1 h.pushed_policy.2.1 h.pushed_policy.2.2.1
  · intro j hj
    rw [mem, entryMem_high _ _ hj]
    exact h.pushed_policy.2.2.2 j hj

  · have ptrS : KeyConstants.tablePtr sampling s = p.tablePtr := by rw [← h.2.1]; rfl
    cases sampling <;> simpa only [KeyConstants.tablePtr, syms, searchPushed, pushed] using ptrS
  · have ptrS : KeyConstants.tablePtr sampling s = p.tablePtr := by rw [← h.2.1]; rfl
    have heldS := KeyConstants.held_of_consts h.2.2
    rw [ptrS] at heldS
    have pushedFrame : Frame [FrameStack.belowA p.sp 24] s.mem (searchPushed s).mem := by
      rw [rootSp]
      exact FrameStack.pushed_frameA (rs := [.r4, .r9, .r10, .r11, .r12, .lr]) fit
    have heldP := KeyConstants.held_after_frame heldS pushedFrame (by
      intro table ht r hr
      have er := List.mem_singleton.mp hr
      subst r
      exact (h.constants_stack table ht).sub_right (FrameStack.belowA_sub (by cases sampling <;> decide : 24 ≤ (stackUse sampling)) h.bounds.stackFits))
    exact KeyConstants.held_after_frame heldP frame (by
      intro table ht r hr
      have er := List.mem_singleton.mp hr
      subst r
      exact h.constants_control table ht)

  · have pushedFrame : Frame [FrameStack.belowA p.sp 24] s.mem (searchPushed s).mem := by
      rw [rootSp]
      exact FrameStack.pushed_frameA (rs := [.r4,.r9,.r10,.r11,.r12,.lr]) fit
    have heldP := h.cached_held.after_frame pushedFrame
      (fun cached => by have := h.context_fit cached; omega_using [this]) (by
        intro cached r hr
        have eq := List.mem_singleton.mp hr
        subst r
        have member : rContext p ∈ s.rd := by rw [h.read_regions]; simp [contextRegions,cached]
        exact (h.stack_separate (List.mem_append_right s.wr member)).symm.sub_right
          (FrameStack.belowA_sub (by have := stackUse_min sampling; omega_using [this]) h.bounds.stackFits))
    exact heldP.after_frame frame (fun cached => by have := h.context_fit cached; omega_using [this]) (by
      intro cached r hr
      have eq := List.mem_singleton.mp hr
      subst r
      exact h.context_control cached)
  · rw [mem]
    exact entryMem_cached p _

end VG.Proof.Ffdh.Arm.KeySearch
