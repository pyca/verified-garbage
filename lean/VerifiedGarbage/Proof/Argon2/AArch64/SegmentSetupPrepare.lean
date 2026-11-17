module

import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Argon2.AArch64.SegmentSetup
public import VerifiedGarbage.Impl.Argon2.AArch64.FillSegment
public import VerifiedGarbage.Impl.Argon2.AArch64.FillBlock
public import VerifiedGarbage.Proof.Argon2.AArch64.DependentWord
public import VerifiedGarbage.Impl.Argon2.AArch64.RandomSource
public import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Proof.Argon2.AArch64.FillKernelStable
public import VerifiedGarbage.Proof.Argon2.AArch64.AddressCacheWord
public import VerifiedGarbage.Proof.Argon2.AArch64.AddressCallsStage
import VerifiedGarbage.Proof.Argon2.AArch64.ClearBlock
public import VerifiedGarbage.Proof.Argon2.AddressInput
public import VerifiedGarbage.Proof.Argon2.AArch64.Initialize
import VerifiedGarbage.Proof.Argon2.AArch64.AddressHeaderWords
import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressSetup
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Impl.Argon2.AArch64.MemoryInit
public import VerifiedGarbage.Proof.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceStart
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Argon2.AArch64.Carry
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Argon2.Dimensions
public import VerifiedGarbage.Proof.Argon2.FillStep
import VerifiedGarbage.Proof.Argon2.AArch64.Instructions
public import VerifiedGarbage.Proof.Argon2.Segment

/-! ### `Argon2.AArch64.SegmentSetupSteps`, which this module and modules that import it used -/

section

/-! ### `Argon2.AArch64.FillSegment`, which only this module used -/

section

/-! ### `Argon2.AArch64.FillSegmentBody`, which only this module used -/

section

/-! ### `Argon2.AArch64.FillBlock`, which only this module used -/

section

/-! ### `Argon2.AArch64.RandomSource`, which only this module used -/

section

/-! ### `Argon2.AArch64.RandomSourcePrepare`, which only this module used -/

section

/-! ### `Argon2.AArch64.AddressCacheSelect`, which only this module used -/

section

/-! ### `Argon2.AArch64.AddressCallsPrepare`, which only this module used -/

section

/-! Merged from `Proof.Argon2.AArch64.AddressHeaderCorrect`. -/

@[expose] public section

section
/-! Merged from `Proof.Argon2.AArch64.AddressHeader`. -/
section
/-! Compose the seven input fields, preserving frame reads across every write. -/

namespace VG.Proof.Argon2.AArch64.AddressHeader

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressHeader

def value (s : State) (i : Nat) : Addr :=
  if i = 1 then s.gpr .x24 else if i = 2 then s.gpr .x22
  else s.mem.readW (off (s.gpr .x19) (frameOffset i)) 64

def headerMem (s : State) (p : Addr) : Nat → Mem
  | 0 => s.mem
  | n + 1 => (headerMem s p n).writeW (off p (8 * n)) (value s n)

theorem offset_bound : ∀ i < 7, frameOffset i + 8 ≤ 272 := by decide +kernel

theorem offset_aligned (i : Nat) : frameOffset i % 8 = 0 := by
  unfold frameOffset
  split <;> [rfl; skip]
  split <;> [rfl; skip]
  split <;> [rfl; skip]
  split <;> rfl

theorem field_ok (s : State) (i : Nat) (hi : i < 7)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) (frameOffset i)) 8)
    (hw : InRegions s.wr (off (s.gpr .x0) (8 * i)) 8) :
    WP isa (.block (field i)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x0) (8 * i)) (value s i) ∧
      CopyKeeps s t ∧ t.sp = s.sp := by
  unfold field value
  by_cases one : i = 1
  · simp only [one, ite_true]
    refine (registerWord_ok s 1 .x24 (by decide) (one ▸ hw)).mono ?_
    rintro t ⟨mem, regs, rd, wr, mx⟩
    exact ⟨mem, ⟨fun r _ _ => congrFun regs r, rd, wr⟩, mx⟩
  · simp only [one, ite_false]
    by_cases two : i = 2
    · simp only [two, ite_true]
      refine (registerWord_ok s 2 .x22 (by decide) (two ▸ hw)).mono ?_
      rintro t ⟨mem, regs, rd, wr, mx⟩
      exact ⟨mem, ⟨fun r _ _ => congrFun regs r, rd, wr⟩, mx⟩
    · simp only [two, ite_false]
      refine (frameWord_ok s i (frameOffset i) (by omega_using [hi]) (offset_aligned i) (offset_bound i hi) hr hw).mono ?_
      rintro t ⟨mem, regs, rd, wr, mx⟩
      exact ⟨mem, ⟨fun r h _ => regs r h, rd, wr⟩, mx⟩

theorem offset_read (s : State) (i : Nat)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8) :
    InRegions (s.rd ++ s.wr) (off (s.gpr .x19) (frameOffset i)) 8 := by
  apply reads
  unfold frameOffset
  split <;> [simp; skip]
  split <;> [simp; skip]
  split <;> [simp; skip]
  split <;> simp

theorem value_kept {s t : State} (keeps : CopyKeeps s t)
    (hf : Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem)
    (sep : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩)
    (i : Nat) (hi : i < 7) : value t i = value s i := by
  unfold value
  rw [keeps.1 .x24 (by decide) (by decide), keeps.1 .x22 (by decide) (by decide), keeps.1 .x19 (by decide) (by decide)]
  have read : t.mem.readW (off (s.gpr .x19) (frameOffset i)) 64 =
      s.mem.readW (off (s.gpr .x19) (frameOffset i)) 64 :=
    hf.readW (r := ⟨s.gpr .x19, 272⟩)
      (Offset.contains_base _ (offset_bound i hi)
        (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) (offset_bound i hi)) (by decide)))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sep) (by decide)
  rw [read]

theorem prefix_ok (n : Nat) (hn : n ≤ 7) (s : State)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8)
    (write : Covers [⟨s.gpr .x0, 1024⟩] s.wr)
    (sep : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩) :
    WP isa (.block (fields n)) s fun t =>
      t.mem = headerMem s (s.gpr .x0) n ∧
      Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.sp = s.sp := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, Frame.refl _ _, CopyKeeps.refl s, rfl⟩
  | succ n ih =>
    simp only [fields, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega_using [hn])).mono ?_
    rintro a ⟨mem, frame, keeps, mx⟩
    have dest : a.gpr .x0 = s.gpr .x0 := keeps.1 .x0 (by decide) (by decide)
    have read : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) (frameOffset n)) 8 := by
      rw [keeps.2.1, keeps.2.2, keeps.1 .x19 (by decide) (by decide)]
      exact offset_read s n reads
    have writable : InRegions a.wr (off (a.gpr .x0) (8 * n)) 8 := by
      rw [dest, keeps.2.2]
      exact write _ _ ⟨⟨s.gpr .x0, 1024⟩, by simp,
        Offset.contains_base _ (d := 8 * n) (n := 8) (k := 1024) (by omega_using [hn]) (by omega_using [hn])⟩
    refine (field_ok a n (by omega_using [hn]) read writable).mono ?_
    rintro t ⟨mem', keeps', mx'⟩
    have value' := value_kept keeps frame sep n (by omega_using [hn])
    refine ⟨?_, ?_, keeps.trans keeps', mx'.trans mx⟩
    · rw [mem', dest, value', mem]
      rfl
    · rw [mem', dest]
      exact frame.writeW (r := ⟨s.gpr .x0, 1024⟩) (by simp) _
        (Offset.contains_base _ (by omega_using [hn]) (by omega_using [hn]))

end VG.Proof.Argon2.AArch64.AddressHeader
end

/-! The prepared input agrees with RFC 9106's seven public address words. -/

namespace VG.Proof.Argon2.AArch64.AddressHeader

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressHeader

def input (s : State) : Block :=
  zeroBlock |>.set 0 (value s 0) |>.set 1 (value s 1) |>.set 2 (value s 2)
    |>.set 3 (value s 3) |>.set 4 (value s 4) |>.set 5 (value s 5) |>.set 6 (value s 6)

theorem headerMem_block (s : State) (p : Addr) (zero : blockAt s.mem p = zeroBlock) :
    blockAt (headerMem s p 7) p = input s := by
  rw [headerMem, blockAt_write_nat _ p 6 (by decide),
    headerMem, blockAt_write_nat _ p 5 (by decide),
    headerMem, blockAt_write_nat _ p 4 (by decide),
    headerMem, blockAt_write_nat _ p 3 (by decide),
    headerMem, blockAt_write_nat _ p 2 (by decide),
    headerMem, blockAt_write_nat _ p 1 (by decide),
    headerMem, blockAt_write_nat _ p 0 (by decide), headerMem, zero]
  rfl

theorem code_ok (s : State)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8)
    (write : Covers [⟨s.gpr .x0, 1024⟩] s.wr)
    (sep : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩)
    (zero : blockAt s.mem (s.gpr .x0) = zeroBlock) :
    WP isa code s fun t => blockAt t.mem (s.gpr .x0) = input s ∧
      Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.sp = s.sp := by
  refine (prefix_ok 7 (by decide) s reads write sep).mono ?_
  rintro t ⟨mem, frame, keeps, mx⟩
  exact ⟨by rw [mem]; exact headerMem_block s _ zero, frame, keeps, mx⟩

structure Words (p : Params) (pass lane slice counter : Nat) (s : State) : Prop where
  passWord : s.mem.readW (off (s.gpr .x19) 0) 64 = BitVec.ofNat 64 pass
  laneWord : s.gpr .x24 = BitVec.ofNat 64 lane
  sliceWord : s.gpr .x22 = BitVec.ofNat 64 slice
  blocksWord : s.mem.readW (off (s.gpr .x19) 240) 64 = BitVec.ofNat 64 p.blocks
  passesWord : s.mem.readW (off (s.gpr .x19) 72) 64 = BitVec.ofNat 64 p.passes
  variantWord : s.mem.readW (off (s.gpr .x19) 112) 64 = BitVec.ofNat 64 p.variant.code
  counterWord : s.mem.readW (off (s.gpr .x19) 8) 64 = BitVec.ofNat 64 counter

theorem input_spec (p : Params) (pass lane slice counter : Nat) (s : State)
    (h : Words p pass lane slice counter s) :
    input s = Proof.Argon2.addressInput p pass lane slice counter := by
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceEqDiff, input, value, frameOffset,
    h.passWord, h.laneWord, h.sliceWord, h.blocksWord,
    h.passesWord, h.variantWord, h.counterWord, Proof.Argon2.addressInput]

end VG.Proof.Argon2.AArch64.AddressHeader
end

/-! Merged from `Proof.Argon2.AArch64.AddressCallsClear`. -/
section
/-! Clear an address-generation block, retaining the allocation invariants. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCalls

structure Cleared (s t : State) (offset : Nat) : Prop where
  block : blockAt t.mem (off (work s) offset) = zeroBlock
  ready : Ready t
  work_eq : work t = work s
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨off (work s) offset, 1024⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem clearAt_ok (s : State) (h : Ready s) (offset : Nat) (bound : offset + 1024 ≤ 8192) :
    WP isa (clearAt offset) s (Cleared s · offset) := by
  unfold clearAt
  refine WP.seq ((pointer_ok s offset (by omega_using [bound]) h.frameRead).mono ?_)
  rintro a ⟨dest, keeps⟩
  have write : Covers [⟨a.gpr .x0, 1024⟩] a.wr := by
    rw [dest, keeps.wr]; exact work_cover s h offset 1024 bound
  refine (ClearBlock.code_ok a write).mono ?_
  rintro t ⟨zero, frame, tk, mx⟩
  have regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r := by
    intro r hr
    have ne : r ≠ .x8 ∧ r ≠ .x9 ∧ r ∉ [Reg.x0, .x12, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (tk.1 r ne.1 ne.2.1).trans (keeps.regs r ne.2.2)
  have rd := tk.2.1.trans keeps.rd
  have wr := tk.2.2.trans keeps.wr
  have hf : Frame [⟨off (work s) offset, 1024⟩] s.mem t.mem := by
    rw [dest, keeps.mem] at frame; exact frame
  have bigger : Frame (stageWrites s offset) s.mem t.mem :=
    hf.mono (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      simp [stageWrites])
  obtain ⟨ready, work'⟩ := ready_of_frame h offset bound regs rd wr (mx.trans keeps.sp) bigger
  rw [dest] at zero
  exact ⟨zero, ready, work', regs, rd, wr, hf, mx.trans keeps.sp⟩

theorem Cleared.full_frame {s t : State} {offset : Nat} (h : Cleared s t offset)
    (bound : offset + 1024 ≤ 8192) : Frame [⟨work s, 8192⟩] s.mem t.mem := by
  apply h.frame.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨work s, 8192⟩, by simp, Offset.sub_base _ bound⟩

theorem frame_word {s t : State} (h : Ready s) (frame : Frame [⟨work s, 8192⟩] s.mem t.mem)
    (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (s.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 :=
  frame.readW (r := ⟨s.gpr .x19, 272⟩) (Offset.contains_base _ bound (by omega_using [bound]))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.frameWork) (by decide)

end VG.Proof.Argon2.AArch64.AddressCalls
end

/-! Prepare the independent-address input and zero block from arbitrary scratch. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCalls

structure Stable (s t : State) : Prop where
  ready : Ready t
  work_eq : work t = work s
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨work s, 8192⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem Stable.trans {s a t : State} (h : Stable s a) (k : Stable a t) : Stable s t := by
  have hf := k.frame
  rw [h.work_eq] at hf
  exact ⟨k.ready, k.work_eq.trans h.work_eq, fun r hr => (k.regs r hr).trans (h.regs r hr),
    k.rd.trans h.rd, k.wr.trans h.wr, h.frame.trans hf, k.sp.trans h.sp⟩

theorem Cleared.stable {s t : State} {offset : Nat} (h : Cleared s t offset)
    (bound : offset + 1024 ≤ 8192) : Stable s t :=
  ⟨h.ready, h.work_eq, h.regs, h.rd, h.wr, h.full_frame bound, h.sp⟩

theorem stable_of_frame {s t : State} (h : Ready s)
    (regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (frame : Frame [⟨work s, 8192⟩] s.mem t.mem) (mx : t.sp = s.sp) : Stable s t := by
  have bp := regs .x19 (by simp [FillCompress.loopRegs])
  have sp := mx
  have work' : work t = work s := by
    unfold work
    rw [bp, frame_word h frame 248 (by decide)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, work', regs, rd, wr, frame, mx⟩
  · rw [rd, wr, bp]; exact h.frameRead
  · rw [work', wr]; exact h.workWrite
  · rw [bp, work']; exact h.frameWork
  · rw [bp, sp]; exact h.frameStack
  · rw [sp, work']; exact h.stackWork

theorem Stable.reads {s t : State} (h : Stable s t)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8) :
    ∀ d ∈ [0, 8, 72, 112, 240], InRegions (t.rd ++ t.wr) (off (t.gpr .x19) d) 8 := by
  rw [h.rd, h.wr, h.regs .x19 (by simp [FillCompress.loopRegs])]
  exact reads

theorem Stable.words {s t : State} {p : Params} {pass lane slice counter : Nat} (ready : Ready s) (h : Stable s t)
    (words : AddressHeader.Words p pass lane slice counter s) :
    AddressHeader.Words p pass lane slice counter t := by
  have bp := h.regs .x19 (by simp [FillCompress.loopRegs])
  have read (d : Nat) (hd : d + 8 ≤ 272) :
      t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
    rw [bp]; exact frame_word ready h.frame d hd
  exact ⟨(read 0 (by decide)).trans words.passWord,
    (h.regs .x24 (by simp [FillCompress.loopRegs])).trans words.laneWord,
    (h.regs .x22 (by simp [FillCompress.loopRegs])).trans words.sliceWord,
    (read 240 (by decide)).trans words.blocksWord,
    (read 72 (by decide)).trans words.passesWord,
    (read 112 (by decide)).trans words.variantWord,
    (read 8 (by decide)).trans words.counterWord⟩

theorem pointer_stable {s a : State} (h : Ready s)
    (k : Divide.Keeps [.x0, .x12, .x15] s a) : Stable s a := by
  apply stable_of_frame h _ k.rd k.wr _ k.sp
  · intro r hr
    apply k.regs
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [k.mem]; exact Frame.refl _ _

theorem Stable.input {s t : State} (ready : Ready s) (h : Stable s t) :
    AddressHeader.input t = AddressHeader.input s := by
  have value (i : Nat) (hi : i < 7) : AddressHeader.value t i = AddressHeader.value s i := by
    unfold AddressHeader.value
    rw [h.regs .x24 (by simp [FillCompress.loopRegs]), h.regs .x22 (by simp [FillCompress.loopRegs]),
      h.regs .x19 (by simp [FillCompress.loopRegs]),
      frame_word ready h.frame (Impl.Argon2.AArch64.AddressHeader.frameOffset i)
        (AddressHeader.offset_bound i hi)]
  unfold AddressHeader.input
  rw [value 0 (by decide), value 1 (by decide), value 2 (by decide), value 3 (by decide),
    value 4 (by decide), value 5 (by decide), value 6 (by decide)]

structure PreparedInput (s t : State) : Prop where
  stable : Stable s t
  zero : blockAt t.mem (off (work s) 7168) = zeroBlock
  input : blockAt t.mem (off (work s) 5120) = AddressHeader.input s

structure Prepared (s t : State) (p : Params) (pass lane slice counter : Nat) : Prop where
  stable : Stable s t
  zero : blockAt t.mem (off (work s) 7168) = zeroBlock
  input : blockAt t.mem (off (work s) 5120) = Proof.Argon2.addressInput p pass lane slice counter

theorem prepare_layout_ok (s : State) (h : Ready s)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8)
    : WP isa prepare s (PreparedInput s) := by
  unfold prepare
  refine WP.seq ((clearAt_ok s h 5120 (by decide)).mono ?_)
  intro a inputClear
  refine WP.seq ((clearAt_ok a inputClear.ready 7168 (by decide)).mono ?_)
  intro b zeroClear
  have stableB := (inputClear.stable (by decide)).trans (zeroClear.stable (by decide))
  have inputZero : blockAt b.mem (off (work s) 5120) = zeroBlock := by
    have kept := FillCompress.block_frame zeroClear.frame (p := off (work s) 5120) (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      rw [inputClear.work_eq]
      exact Offset.disjoint _ (by decide) (by decide) (by decide))
    exact kept.trans inputClear.block
  refine WP.seq ((pointer_ok b 5120 (by decide) zeroClear.ready.frameRead).mono ?_)
  rintro c ⟨dest, keeps⟩
  have stableC := stableB.trans (pointer_stable zeroClear.ready keeps)
  have dest' : c.gpr .x0 = off (work s) 5120 := by rw [dest, stableB.work_eq]
  have write : Covers [⟨c.gpr .x0, 1024⟩] c.wr := by
    rw [dest, keeps.wr]; exact work_cover b zeroClear.ready 5120 1024 (by decide)
  have sep : (⟨c.gpr .x19, 272⟩ : Region).Disjoint ⟨c.gpr .x0, 1024⟩ := by
    rw [dest', stableC.regs .x19 (by simp [FillCompress.loopRegs])]
    exact h.frameWork.sub_right (Offset.sub_base _ (by decide))
  have zero : blockAt c.mem (c.gpr .x0) = zeroBlock := by rw [dest', keeps.mem]; exact inputZero
  refine (AddressHeader.code_ok c (stableC.reads reads) write sep zero).mono ?_
  rintro t ⟨input, frame, tk, mx⟩
  have regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = c.gpr r := by
    intro r hr
    apply tk.1 _ _ (by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have frame' : Frame [⟨work c, 8192⟩] c.mem t.mem := by
    apply frame.sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    refine ⟨⟨work c, 8192⟩, by simp, ?_⟩
    rw [dest', stableC.work_eq]
    exact Offset.sub_base _ (by decide)
  have stableT := stableC.trans (stable_of_frame stableC.ready regs tk.2.1 tk.2.2 frame' mx)
  refine ⟨stableT, ?_, ?_⟩
  · have kept := FillCompress.block_frame frame (p := off (work s) 7168) (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      rw [dest']
      exact Offset.disjoint _ (by decide) (by decide) (by decide))
    rw [kept, keeps.mem, ← inputClear.work_eq]
    exact zeroClear.block
  · rw [dest'] at input
    exact input.trans (stableC.input h)

theorem prepare_ok (p : Params) (pass lane slice counter : Nat) (s : State) (h : Ready s)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8)
    (words : AddressHeader.Words p pass lane slice counter s) :
    WP isa prepare s (Prepared s · p pass lane slice counter) :=
  (prepare_layout_ok s h reads).mono (fun _ k =>
    ⟨k.stable, k.zero, k.input.trans (AddressHeader.input_spec p pass lane slice counter s words)⟩)

end VG.Proof.Argon2.AArch64.AddressCalls

end

end

/-! ### `Argon2.AArch64.AddressCalls`, which only this module used -/

section

/-! Both compression calls produce exactly the reviewed independent-address block. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCalls

def writes (s : State) : List Region := [⟨work s, 8192⟩, below s.sp 8]

structure Generated (s t : State) (p : Params) (pass lane slice counter : Nat) : Prop where
  block : blockAt t.mem (off (work s) 6144) = addressBlock p pass lane slice counter
  ready : Ready t
  work : work t = work s
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (writes s) s.mem t.mem

theorem stage_frame_full {s t : State} {out : Nat} (bound : out + 1024 ≤ 8192)
    (hf : Frame (stageWrites s out) s.mem t.mem) : Frame (writes s) s.mem t.mem := by
  apply hf.sub
  intro r hr
  simp only [stageWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨work s, 8192⟩, by simp [writes], Offset.sub_base _ bound⟩
  · exact ⟨⟨work s, 8192⟩, by simp [writes], Region.sub_prefix (by decide)⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩

theorem zero_preserved {s t : State} (h : Ready s)
    (hf : Frame (stageWrites s 4096) s.mem t.mem) :
    blockAt t.mem (off (work s) 7168) = blockAt s.mem (off (work s) 7168) := by
  apply FillCompress.block_frame hf
  intro r hr
  simp only [stageWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ (by decide) (by decide) (by decide)
  · exact Offset.disjoint_base _ (by decide) (by decide)
  · exact (h.stackWork.sub_right (Offset.sub_base _ (by decide))).symm

theorem calls_ok (p : Params) (pass lane slice counter : Nat) (s : State) (h : Ready s)
    (zero : blockAt s.mem (off (work s) 7168) = zeroBlock)
    (input : blockAt s.mem (off (work s) 5120) = Proof.Argon2.addressInput p pass lane slice counter) :
    WP isa calls s (Generated s · p pass lane slice counter) := by
  unfold calls
  refine WP.seq ((stage_ok s h 7168 5120 4096 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).mono ?_)
  intro a first
  refine (stage_ok a first.ready 7168 4096 6144 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).mono ?_
  intro t second
  refine ⟨?_, second.ready, second.work.trans first.work,
    fun r hr => (second.regs r hr).trans (first.regs r hr),
    second.rd.trans first.rd, second.wr.trans first.wr, second.sp.trans first.sp, ?_⟩
  · have result := second.result
    rw [first.work, zero_preserved h first.frame, zero, first.result, zero, input] at result
    rw [Proof.Argon2.addressBlock_eq]
    exact result
  · have next := stage_frame_full (by decide) second.frame
    simp only [writes, first.work, first.sp] at next
    exact (stage_frame_full (by decide) first.frame).trans next

end VG.Proof.Argon2.AArch64.AddressCalls

end

end


/-! Merged from `Proof.Argon2.AArch64.AddressGeneration`. -/

@[expose] public section

section
/-! Complete independent-address generation against the reviewed algorithm. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCalls

theorem calls_sp_ok (p : Params) (pass lane slice counter : Nat) (s : State) (h : Ready s)
    (zero : blockAt s.mem (off (work s) 7168) = zeroBlock)
    (input : blockAt s.mem (off (work s) 5120) = Proof.Argon2.addressInput p pass lane slice counter) :
    WP isa calls s fun t => Generated s t p pass lane slice counter ∧ t.sp = s.sp :=
  (calls_ok p pass lane slice counter s h zero input).mono (fun _ h => ⟨h, h.sp⟩)

theorem code_ok (p : Params) (pass lane slice counter : Nat) (s : State) (h : Ready s)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8)
    (words : AddressHeader.Words p pass lane slice counter s) :
    WP isa code s fun t => Generated s t p pass lane slice counter ∧ t.sp = s.sp := by
  unfold code
  refine WP.seq ((prepare_ok p pass lane slice counter s h reads words).mono ?_)
  intro a prepared
  have zero : blockAt a.mem (off (work a) 7168) = zeroBlock := by
    rw [prepared.stable.work_eq]; exact prepared.zero
  have input : blockAt a.mem (off (work a) 5120) = Proof.Argon2.addressInput p pass lane slice counter := by
    rw [prepared.stable.work_eq]; exact prepared.input
  refine (calls_sp_ok p pass lane slice counter a prepared.stable.ready zero input).mono ?_
  rintro t ⟨generated, mx⟩
  have frame := generated.frame
  rw [writes, prepared.stable.work_eq, prepared.stable.sp] at frame
  have firstFrame : Frame (writes s) s.mem a.mem :=
    prepared.stable.frame.mono (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      simp [writes])
  refine ⟨⟨?_, generated.ready, generated.work.trans prepared.stable.work_eq,
    fun r hr => (generated.regs r hr).trans (prepared.stable.regs r hr),
    generated.rd.trans prepared.stable.rd, generated.wr.trans prepared.stable.wr, generated.sp.trans prepared.stable.sp,
    firstFrame.trans frame⟩, mx.trans prepared.stable.sp⟩
  have block := generated.block
  rw [prepared.stable.work_eq] at block
  exact block

end VG.Proof.Argon2.AArch64.AddressCalls
end

/-! Merged from `Proof.Argon2.AArch64.AddressCacheSave`. -/
section
/-! Save the public cache counter without disturbing scratch or header fields. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCache

theorem save_ok (s : State) (hw : InRegions s.wr (off (s.gpr .x19) 8) 8) :
    WP isa (.block save) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x19) 8) (s.gpr .x8) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [off] at hw
  apply WP.of_runBlock
  simp only [save, VG.Impl.Argon2.AArch64.Instructions.store,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    show 8 % 8 = 0 ∧ 8 < 4096 * 8 from by decide, hw, and_self,
    ite_true, State.store, State.read, BitVec.setWidth_eq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial⟩

structure Saved (s t : State) : Prop where
  mem : t.mem = s.mem.writeW (off (s.gpr .x19) 8) (s.gpr .x8)
  regs : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  ready : AddressCalls.Ready t
  work_eq : AddressCalls.work t = AddressCalls.work s
  frame : Frame [⟨off (s.gpr .x19) 8, 8⟩] s.mem t.mem

theorem save_ready (s : State) (h : AddressCalls.Ready s)
    (hw : InRegions s.wr (off (s.gpr .x19) 8) 8) : WP isa (.block save) s (Saved s) := by
  refine (save_ok s hw).mono ?_
  rintro t ⟨mem, regs, rd, wr, mx⟩
  have work' : AddressCalls.work t = AddressCalls.work s := by
    unfold AddressCalls.work
    rw [regs, mem, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
  have ready : AddressCalls.Ready t := by
    constructor
    · rw [rd, wr, regs]; exact h.frameRead
    · rw [work', wr]; exact h.workWrite
    · rw [regs, work']; exact h.frameWork
    · rw [regs, mx]; exact h.frameStack
    · rw [mx, work']; exact h.stackWork
  refine ⟨mem, regs, rd, wr, mx, ready, work', ?_⟩
  rw [mem]
  exact (Frame.refl _ _).writeW (r := ⟨off (s.gpr .x19) 8, 8⟩) (by simp) _
    (Region.contains_self _ _)

theorem Saved.read {s t : State} (h : Saved s t) (d : Nat)
    (hd : d + 8 ≤ 8 ∨ 16 ≤ d) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [h.regs, h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ hd (by omega_using [bound]) (by decide)) (by decide)

theorem Saved.words {s t : State} {p : Params} {pass lane slice old counter : Nat}
    (h : Saved s t) (words : AddressHeader.Words p pass lane slice old s)
    (value : s.gpr .x8 = BitVec.ofNat 64 counter) :
    AddressHeader.Words p pass lane slice counter t := by
  refine ⟨(h.read 0 (by decide) (by decide)).trans words.passWord,
    ?_, ?_, (h.read 240 (by decide) (by decide)).trans words.blocksWord,
    (h.read 72 (by decide) (by decide)).trans words.passesWord,
    (h.read 112 (by decide) (by decide)).trans words.variantWord, ?_⟩
  · rw [h.regs]; exact words.laneWord
  · rw [h.regs]; exact words.sliceWord
  · rw [h.regs, h.mem, Mem.readW_writeW_self64, value]

end VG.Proof.Argon2.AArch64.AddressCache
end

/-! Regenerate only when the public one-based block counter changes. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCache

def wanted (s : State) : Nat := (s.gpr .x23).toNat / 128 + 1

def writes (s : State) : List Region :=
  [⟨AddressCalls.work s, 8192⟩, below s.sp 8, ⟨off (s.gpr .x19) 8, 8⟩]

structure Ready (p : Params) (pass lane slice old : Nat) (s : State) : Prop where
  layout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  write : InRegions s.wr (off (s.gpr .x19) 8) 8
  words : AddressHeader.Words p pass lane slice old s
  cached : counter (s.gpr .x23) = s.mem.readW (off (s.gpr .x19) 8) 64 →
    blockAt s.mem (off (AddressCalls.work s) 6144) = addressBlock p pass lane slice (wanted s)

structure Selected (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  block : blockAt t.mem (off (AddressCalls.work s) 6144) = addressBlock p pass lane slice (wanted s)
  layout : AddressCalls.Ready t
  work_eq : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s) s.mem t.mem
  sp : t.sp = s.sp
  counterWord : t.mem.readW (off (t.gpr .x19) 8) 64 = counter (s.gpr .x23)

theorem check_stable {s a : State} (h : AddressCalls.Ready s) (k : Divide.Keeps [.x8, .x13, .x14, .x15] s a) :
    AddressCalls.Stable s a := by
  apply AddressCalls.stable_of_frame h _ k.rd k.wr _ k.sp
  · intro r hr
    apply k.regs
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [k.mem]; exact Frame.refl _ _

theorem selected_ok (p : Params) (pass lane slice old : Nat) (s : State)
    (h : Ready p pass lane slice old s) :
    WP isa select s (Selected s · p pass lane slice) := by
  unfold select
  refine WP.seq ((check_ok s (h.reads 8 (by simp))).mono ?_)
  rintro a ⟨value, flag, keeps⟩
  have stableA := check_stable h.layout keeps
  refine WP.ite (decide (counter (s.gpr .x23) = s.mem.readW (off (s.gpr .x19) 8) 64))
    (by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_iff]
      exact ReferenceStart.sub_zero_iff _ _) ?_ ?_
  · intro same
    have equal := of_decide_eq_true same
    apply WP.of_runBlock
    simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
    refine ⟨?_, stableA.ready, stableA.work_eq, stableA.regs, keeps.rd, keeps.wr,
      ?_, keeps.sp, ?_⟩
    · rw [keeps.mem]; exact h.cached equal
    · rw [keeps.mem]; exact Frame.refl _ _
    · rw [stableA.regs .x19 (by simp [FillCompress.loopRegs]), keeps.mem]; exact equal.symm
  · intro _
    have write : InRegions a.wr (off (a.gpr .x19) 8) 8 := by
      rw [keeps.wr, stableA.regs .x19 (by simp [FillCompress.loopRegs])]; exact h.write
    refine WP.seq ((save_ready a stableA.ready write).mono ?_)
    intro b saved
    have words : AddressHeader.Words p pass lane slice (wanted s) b := by
      apply saved.words (stableA.words h.layout h.words)
      rw [value, counter_nat]; rfl
    have reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (b.rd ++ b.wr) (off (b.gpr .x19) d) 8 := by
      rw [saved.rd, saved.wr, saved.regs]; exact stableA.reads h.reads
    refine (AddressCalls.code_ok p pass lane slice (wanted s) b saved.ready reads words).mono ?_
    rintro t ⟨generated, mx⟩
    have workB : AddressCalls.work b = AddressCalls.work s := saved.work_eq.trans stableA.work_eq
    have regsB (r : Reg) (hr : r ∈ FillCompress.loopRegs) : b.gpr r = s.gpr r :=
      (congrFun saved.regs r).trans (stableA.regs r hr)
    have regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r :=
      fun r hr => (generated.regs r hr).trans (regsB r hr)
    have firstFrame : Frame (writes s) s.mem b.mem := by
      have frame := saved.frame
      rw [stableA.regs .x19 (by simp [FillCompress.loopRegs]), keeps.mem] at frame
      exact frame.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp [writes])
    have finalFrame : Frame (writes s) b.mem t.mem := by
      have frame := generated.frame
      rw [AddressCalls.writes, workB, saved.sp.trans keeps.sp] at frame
      exact frame.mono (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp [writes])
    refine ⟨?_, generated.ready, generated.work.trans workB, regs,
      generated.rd.trans (saved.rd.trans keeps.rd), generated.wr.trans (saved.wr.trans keeps.wr),
      firstFrame.trans finalFrame, mx.trans (saved.sp.trans keeps.sp), ?_⟩
    · have block := generated.block
      rw [workB] at block
      exact block
    · have preserved : t.mem.readW (off (b.gpr .x19) 8) 64 = b.mem.readW (off (b.gpr .x19) 8) 64 :=
        generated.frame.readW (r := ⟨b.gpr .x19, 272⟩)
          (Offset.contains_base _ (by decide) (by decide)) (by
            intro r hr
            simp only [AddressCalls.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact saved.ready.frameWork
            · exact saved.ready.frameStack) (by decide)
      rw [generated.regs .x19 (by simp [FillCompress.loopRegs]), preserved, saved.regs, saved.mem,
        Mem.readW_writeW_self64, value]

end VG.Proof.Argon2.AArch64.AddressCache

end

end


@[expose] public section

section

/-! Short mask computations for the public addressing-mode predicate. -/

namespace VG.Proof.Argon2.AArch64.AddressMode

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressMode
open VG.Impl.Argon2.AArch64

theorem zero_nat (x : Addr) : x.toNat < 1 ↔ x = 0#64 := by
  constructor
  · intro h; exact BitVec.eq_of_toNat_eq (Nat.lt_one_iff.mp h)
  · intro h; rw [h]; decide

theorem borrow_lt (a b : Nat) :
    (if decide (b ≤ a) = true then (0 : Addr) else -1) =
      Divide.mask (decide (a < b)) := by
  by_cases h : a < b
  · simp only [show ¬b ≤ a by omega_using [h], decide_false, Bool.false_eq_true,
      ite_false, h, decide_true, Divide.mask, ite_true]
  · simp only [show b ≤ a by omega_using [h], decide_true, ite_true,
      h, decide_false, Divide.mask, Bool.false_eq_true, ite_false]

theorem kind_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 112) 8) :
    WP isa (.block kind) s fun t =>
      t.gpr .x6 = Divide.mask (decide (s.mem.readW (off (s.gpr .x19) 112) 64 = 1)) ∧
      t.gpr .x4 = Divide.mask (decide (s.mem.readW (off (s.gpr .x19) 112) 64 = 2)) ∧
      Divide.Keeps [.x8, .x6, .x4, .x12, .x13, .x14, .x15] s t := by
  simp only [off] at hr
  apply WP.of_runBlock
  simp only [kind, off, show 112 % 8 = 0 ∧ 112 < 4096 * 8 from by decide, hr, and_self,
    show (1#64).toNat = 1 from rfl, Instructions.mov, Instructions.load, Instructions.logici, Instructions.logic,
    Instructions.comparei, Instructions.compare, Instructions.sbb, Instructions.imm, Instructions.mark,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.read, Size.bytes, Size.bits,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_write, RegUpd.c_addWithCarry,

    BitVec.setWidth_eq, Bool.toNat_true, sub_value, sub_carry, borrow_mask, borrow_lt,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (1#16).setWidth 64 = 1#64 from rfl,
    show (2#16).setWidth 64 = 2#64 from rfl,
    show 1 < 65536 from by decide, show 2 < 65536 from by decide,
    show 0 < 4096 from by decide, show (63 : Nat) < 64 from by decide,
    BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    borrow_lt,  zero_nat, BitVec.xor_eq_zero_iff,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]
  all_goals rfl

theorem pass_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8) :
    WP isa (.block pass) s fun t =>
      t.gpr .x5 = Divide.mask (decide (s.mem.readW (off (s.gpr .x19) 0) 64 = 0#64)) ∧
      Divide.Keeps [.x5, .x13, .x14, .x15] s t := by
  simp only [off, BitVec.add_zero] at hr
  apply WP.of_runBlock
  simp only [pass, off, show 0 % 8 = 0 ∧ 0 < 4096 * 8 from by decide, hr, and_self,
    show (1#64).toNat = 1 from rfl, Instructions.mov, Instructions.load,
    Instructions.comparei, Instructions.compare, Instructions.sbb, Instructions.imm, Instructions.mark,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.read, Size.bytes, Size.bits,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_write, RegUpd.c_addWithCarry,

    BitVec.setWidth_eq, Bool.toNat_true, sub_value, sub_carry, borrow_mask, borrow_lt,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (1#16).setWidth 64 = 1#64 from rfl,

    show 1 < 65536 from by decide,
    show 0 < 4096 from by decide, show (63 : Nat) < 64 from by decide,
    BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    borrow_lt,  zero_nat,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem slice_ok (s : State) : WP isa (.block slice) s fun t =>
    t.gpr .x6 = (s.gpr .x6 ||| ((s.gpr .x4 &&& s.gpr .x5) &&&
      Divide.mask (decide ((s.gpr .x22).toNat < 2)))) &&& 1 ∧
    Divide.Keeps [.x4, .x7, .x6, .x12, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [slice,  show (2#64).toNat = 2 from rfl, Instructions.mov,  Instructions.logici, Instructions.logic,
    Instructions.comparei, Instructions.compare, Instructions.sbb, Instructions.imm, Instructions.mark,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec,   State.read,  Size.bits,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_write, RegUpd.c_addWithCarry,

    BitVec.setWidth_eq, Bool.toNat_true, sub_value, sub_carry, borrow_mask, borrow_lt,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (1#16).setWidth 64 = 1#64 from rfl,
    show (2#16).setWidth 64 = 2#64 from rfl,
    show 1 < 65536 from by decide, show 2 < 65536 from by decide,
    show 0 < 4096 from by decide, show (63 : Nat) < 64 from by decide,
    BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    borrow_lt,
      Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.AArch64.AddressMode

end

/-! Merged from `Proof.Argon2.AArch64.FillKernelInvariant`. -/
section
/-! Each active-cell update retains the frame and matrix allocation invariant. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

theorem Done.frame_word {s t : State} {p : Params} {pass lane slice index : Nat}
    (h : Ready p pass lane slice index s) (done : Done s t p pass lane slice index)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 16 ∨ 24 ≤ d) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.regs .x19 (by simp [FillCompress.loopRegs])]
  have sub : Region.Sub ⟨off (s.gpr .x19) d, 8⟩ ⟨s.gpr .x19, 272⟩ := Offset.sub_base _ bound
  have currentSub : Region.Sub ⟨current s p lane slice index, 1024⟩ ⟨matrix s, p.blocks * 1024⟩ :=
    cell_sub p _ h.bounds.lanesPositive h.bounds.laneBound
      (Proof.Argon2.column_lt p h.bounds.lanesPositive h.bounds.sliceBound h.bounds.indexBound)
  exact done.frame.readW (r := ⟨off (s.gpr .x19) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ((h.layout.matrixFrame.sub_left currentSub).symm).sub_left sub
    · exact h.layout.frameWork.sub_left sub
    · exact h.layout.frameStack.sub_left sub
    · exact Offset.disjoint _ separate (by omega_using [bound]) (by decide)) (by decide)

theorem Done.retains {s t : State} {p : Params} {pass lane slice index : Nat}
    (h : Ready p pass lane slice index s) (done : Done s t p pass lane slice index) :
    Ready p pass lane slice index t := by
  have bp := done.regs .x19 (by simp [FillCompress.loopRegs])
  have sp := done.sp
  have matrix' : matrix t = matrix s := done.frame_word h 232 (by decide) (by decide)
  have work' : work t = work s := done.frame_word h 248 (by decide) (by decide)
  refine ⟨?_, h.bounds, ?_, (done.frame_word h 0 (by decide) (by decide)).trans h.passWord,
    (done.frame_word h 184 (by decide) (by decide)).trans h.lanesWord⟩
  · constructor
    · rw [done.rd, done.wr, bp]; exact h.layout.frameRead
    · rw [done.wr, bp]; exact h.layout.frameWrite
    · rw [matrix', done.wr]; exact h.layout.matrixWrite
    · rw [work', done.wr]; exact h.layout.workWrite
    · rw [matrix', work']; exact h.layout.matrixWork
    · rw [matrix', bp]; exact h.layout.matrixFrame
    · rw [matrix', sp]; exact h.layout.matrixStack
    · rw [bp, work']; exact h.layout.frameWork
    · rw [bp, sp]; exact h.layout.frameStack
    · rw [sp, work']; exact h.layout.stackWork
  · exact ⟨(done.regs .x24 (by simp [FillCompress.loopRegs])).trans h.position.current,
      (done.regs .x20 (by simp [FillCompress.loopRegs])).trans h.position.laneLength,
      (done.regs .x21 (by simp [FillCompress.loopRegs])).trans h.position.segmentLength,
      (done.regs .x22 (by simp [FillCompress.loopRegs])).trans h.position.slice,
      (done.regs .x23 (by simp [FillCompress.loopRegs])).trans h.position.index⟩

end VG.Proof.Argon2.AArch64.FillKernel
end

/-! Merged from `Proof.Argon2.AArch64.AddressMode`. -/
section
/-! The segment mode is exactly the reviewed Argon2d/i/id addressing predicate. -/

namespace VG.Proof.Argon2.AArch64.AddressMode

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressMode

def value (s : State) : Addr :=
  let kind := s.mem.readW (off (s.gpr .x19) 112) 64
  let pass := s.mem.readW (off (s.gpr .x19) 0) 64
  (Divide.mask (decide (kind = 1)) ||| ((Divide.mask (decide (kind = 2)) &&&
    Divide.mask (decide (pass = 0#64))) &&& Divide.mask (decide ((s.gpr .x22).toNat < 2)))) &&& 1

def changed : List Reg := [.x8, .x4, .x5, .x6, .x7, .x12, .x13, .x14, .x15]

theorem code_ok (s : State)
    (kindRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 112) 8)
    (passRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8) :
    WP isa code s fun t => t.gpr .x6 = value s ∧ Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((kind_ok s kindRead).mono ?_)
  rintro a ⟨i, id, ka⟩
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) 0) 8 := by
    rw [ka.rd, ka.wr, ka.regs .x19 (by decide)]; exact passRead
  refine WP.seq ((pass_ok a read).mono ?_)
  rintro b ⟨zero, kb⟩
  refine (slice_ok b).mono ?_
  rintro t ⟨result, kt⟩
  refine ⟨?_, ((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kt.mono (by decide))⟩
  rw [result, kb.regs .x6 (by decide), i, kb.regs .x4 (by decide), id, zero,
    ka.mem, ka.regs .x19 (by decide), kb.regs .x22 (by decide), ka.regs .x22 (by decide)]
  rfl

theorem masks : ∀ a b c d : Bool,
    (Divide.mask a ||| ((Divide.mask b &&& Divide.mask c) &&& Divide.mask d)) &&& 1 =
      (BitVec.ofBool (a || (b && c && d))).setWidth 64 := by decide +kernel

theorem variants : ∀ v : Spec.Argon2.Variant, ∀ a b : Bool,
    (decide (BitVec.ofNat 64 v.code = (1 : Addr)) ||
      (decide (BitVec.ofNat 64 v.code = (2 : Addr)) && a && b)) =
    ((v == .i) || ((v == .id) && a && b)) := by
  intro v
  cases v <;> decide +kernel

theorem value_spec (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (kindWord : s.mem.readW (off (s.gpr .x19) 112) 64 = BitVec.ofNat 64 p.variant.code)
    (passWord : s.mem.readW (off (s.gpr .x19) 0) 64 = BitVec.ofNat 64 pass)
    (sliceWord : s.gpr .x22 = BitVec.ofNat 64 slice)
    (passBound : pass < 2 ^ 64) (sliceBound : slice < 2 ^ 64) :
    value s = (BitVec.ofBool (Spec.Argon2.independent p pass slice)).setWidth 64 := by
  have passZero : BitVec.ofNat 64 pass = 0#64 ↔ pass = 0 := ReferenceMap.word_zero pass passBound
  unfold value
  rw [kindWord, passWord, sliceWord, masks,
    ReferenceMap.word_nat slice sliceBound]
  simp only [passZero]
  unfold Spec.Argon2.independent
  rw [variants, Bool.beq_eq_decide_eq pass 0]

theorem code_spec_ok (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (kindRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 112) 8)
    (passRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8)
    (kindWord : s.mem.readW (off (s.gpr .x19) 112) 64 = BitVec.ofNat 64 p.variant.code)
    (passWord : s.mem.readW (off (s.gpr .x19) 0) 64 = BitVec.ofNat 64 pass)
    (sliceWord : s.gpr .x22 = BitVec.ofNat 64 slice)
    (passBound : pass < 2 ^ 64) (sliceBound : slice < 2 ^ 64) :
    WP isa code s fun t => t.gpr .x6 =
      (BitVec.ofBool (Spec.Argon2.independent p pass slice)).setWidth 64 ∧ Divide.Keeps changed s t :=
  (code_ok s kindRead passRead).mono (fun _ h =>
    ⟨h.1.trans (value_spec s p pass slice kindWord passWord sliceWord passBound sliceBound), h.2⟩)

end VG.Proof.Argon2.AArch64.AddressMode
end

/-! Merged from `Proof.Argon2.AArch64.AddressCacheState`. -/
section
/-! Merged from `Proof.Argon2.AArch64.AddressCache`. -/
section
/-! Complete cached random-word selection against RFC 9106's address block. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCache

structure Done (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  selected : Selected s t p pass lane slice
  random : t.gpr .x0 =
    (addressBlock p pass lane slice (wanted s))[(s.gpr .x23).toNat % 128]'(Nat.mod_lt _ (by decide))

theorem code_ok (p : Params) (pass lane slice old : Nat) (s : State)
    (h : Ready p pass lane slice old s) :
    WP isa code s (Done s · p pass lane slice) := by
  unfold code
  refine WP.seq ((selected_ok p pass lane slice old s h).mono ?_)
  intro a selected
  refine (word_ok a selected.layout).mono ?_
  rintro t ⟨random, keeps⟩
  have regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r := by
    intro r hr
    have ne : r ∉ [Reg.x3, .x8, .x0, .x12, .x13, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (keeps.regs r ne).trans (selected.regs r hr)
  have bp := keeps.regs .x19 (by decide)
  have sp := keeps.sp
  have work' : AddressCalls.work t = AddressCalls.work a := by
    unfold AddressCalls.work; rw [bp, keeps.mem]
  have layout : AddressCalls.Ready t := by
    constructor
    · rw [keeps.rd, keeps.wr, bp]; exact selected.layout.frameRead
    · rw [work', keeps.wr]; exact selected.layout.workWrite
    · rw [bp, work']; exact selected.layout.frameWork
    · rw [bp, sp]; exact selected.layout.frameStack
    · rw [sp, work']; exact selected.layout.stackWork
  refine ⟨⟨?_, layout, work'.trans selected.work_eq, regs,
    keeps.rd.trans selected.rd, keeps.wr.trans selected.wr, ?_,
    keeps.sp.trans selected.sp, ?_⟩, ?_⟩
  · rw [keeps.mem]; exact selected.block
  · rw [keeps.mem]; exact selected.frame
  · rw [bp, keeps.mem]; exact selected.counterWord
  · rw [selected.work_eq, selected.regs .x23 (by simp [FillCompress.loopRegs]), selected.block] at random
    exact random

end VG.Proof.Argon2.AArch64.AddressCache
end

/-! Retain the filling header and allocation across independent-address regeneration. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Spec.Argon2

theorem Selected.frame_word {s t : State} {p : Params} {pass lane slice : Nat}
    (layout : AddressCalls.Ready s) (h : Selected s t p pass lane slice)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 8 ∨ 16 ≤ d) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [h.regs .x19 (by simp [FillCompress.loopRegs])]
  have sub : Region.Sub ⟨off (s.gpr .x19) d, 8⟩ ⟨s.gpr .x19, 272⟩ := Offset.sub_base _ bound
  exact h.frame.readW (r := ⟨off (s.gpr .x19) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact layout.frameWork.sub_left sub
    · exact layout.frameStack.sub_left sub
    · exact Offset.disjoint _ separate (by omega_using [bound]) (by decide)) (by decide)

theorem Selected.words {s t : State} {p : Params} {pass lane slice old : Nat}
    (ready : Ready p pass lane slice old s) (h : Selected s t p pass lane slice) :
    AddressHeader.Words p pass lane slice (wanted s) t := by
  exact ⟨(h.frame_word ready.layout 0 (by decide) (by decide)).trans ready.words.passWord,
    (h.regs .x24 (by simp [FillCompress.loopRegs])).trans ready.words.laneWord,
    (h.regs .x22 (by simp [FillCompress.loopRegs])).trans ready.words.sliceWord,
    (h.frame_word ready.layout 240 (by decide) (by decide)).trans ready.words.blocksWord,
    (h.frame_word ready.layout 72 (by decide) (by decide)).trans ready.words.passesWord,
    (h.frame_word ready.layout 112 (by decide) (by decide)).trans ready.words.variantWord,
    h.counterWord.trans (counter_nat _)⟩

end VG.Proof.Argon2.AArch64.AddressCache
end

/-! Merged from `Proof.Argon2.AArch64.AddressCacheMatrix`. -/
section
/-! Independent-address generation leaves every matrix cell intact. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Spec.Argon2

theorem Selected.filling_ready {s t : State} {p : Params} {pass lane slice index : Nat}
    (cacheLayout : AddressCalls.Ready s) (h : FillKernel.Ready p pass lane slice index s)
    (done : Selected s t p pass lane slice) : FillKernel.Ready p pass lane slice index t := by
  have bp := done.regs .x19 (by simp [FillCompress.loopRegs])
  have sp := done.sp
  have matrix' : FillKernel.matrix t = FillKernel.matrix s := done.frame_word cacheLayout 232 (by decide) (by decide)
  have work' : FillKernel.work t = FillKernel.work s := done.frame_word cacheLayout 248 (by decide) (by decide)
  refine ⟨?_, h.bounds, ?_, (done.frame_word cacheLayout 0 (by decide) (by decide)).trans h.passWord,
    (done.frame_word cacheLayout 184 (by decide) (by decide)).trans h.lanesWord⟩
  · constructor
    · rw [done.rd, done.wr, bp]; exact h.layout.frameRead
    · rw [done.wr, bp]; exact h.layout.frameWrite
    · rw [matrix', done.wr]; exact h.layout.matrixWrite
    · rw [work', done.wr]; exact h.layout.workWrite
    · rw [matrix', work']; exact h.layout.matrixWork
    · rw [matrix', bp]; exact h.layout.matrixFrame
    · rw [matrix', sp]; exact h.layout.matrixStack
    · rw [bp, work']; exact h.layout.frameWork
    · rw [bp, sp]; exact h.layout.frameStack
    · rw [sp, work']; exact h.layout.stackWork
  · exact ⟨(done.regs .x24 (by simp [FillCompress.loopRegs])).trans h.position.current,
      (done.regs .x20 (by simp [FillCompress.loopRegs])).trans h.position.laneLength,
      (done.regs .x21 (by simp [FillCompress.loopRegs])).trans h.position.segmentLength,
      (done.regs .x22 (by simp [FillCompress.loopRegs])).trans h.position.slice,
      (done.regs .x23 (by simp [FillCompress.loopRegs])).trans h.position.index⟩

theorem Selected.represents {s t : State} {p : Params} {pass lane slice index : Nat}
    (cacheLayout : AddressCalls.Ready s) (h : FillKernel.Ready p pass lane slice index s)
    (matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩)
    (done : Selected s t p pass lane slice) (blocks : Array Block)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks blocks) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks blocks := by
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word cacheLayout 232 (by decide) (by decide)
  rw [base]
  refine ⟨represented.size, ?_⟩
  intro k hk
  have kept : blockAt t.mem (Proof.Argon2.matrixCell (FillKernel.matrix s) k) =
      blockAt s.mem (Proof.Argon2.matrixCell (FillKernel.matrix s) k) := by
    apply FillCompress.block_frame done.frame
    intro r hr
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact matrixWork.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)
    · exact h.layout.matrixStack.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)
    · exact (h.layout.matrixFrame.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)).sub_right
        (Offset.sub_base _ (by decide))
  exact kept.trans (represented.block k hk)

end VG.Proof.Argon2.AArch64.AddressCache
end

/-! Merged from `Proof.Argon2.AArch64.AddressCacheInvariant`. -/
section
/-! Cache validity does not depend on the current index, so advancing an index
retains it. Counter zero requires no cached contents; every other counter
identifies its specified independent-address block.
-/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Spec.Argon2

structure Invariant (p : Params) (pass lane slice old : Nat) (s : State) : Prop where
  layout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  write : InRegions s.wr (off (s.gpr .x19) 8) 8
  words : AddressHeader.Words p pass lane slice old s
  bound : old < 2 ^ 64
  cached : old = 0 ∨ blockAt s.mem (off (AddressCalls.work s) 6144) = addressBlock p pass lane slice old

theorem wanted_bound (s : State) : wanted s < 2 ^ 64 := by
  unfold wanted
  have := (s.gpr .x23).isLt
  omega_using []

theorem Invariant.ready {p : Params} {pass lane slice old : Nat} {s : State}
    (h : Invariant p pass lane slice old s) : Ready p pass lane slice old s := by
  refine ⟨h.layout, h.reads, h.write, h.words, ?_⟩
  intro same
  have word : BitVec.ofNat 64 (wanted s) = BitVec.ofNat 64 old := by
    unfold wanted
    rw [← counter_nat]; exact same.trans h.words.counterWord
  have equal := (ReferenceMap.word_eq _ _ (wanted_bound s) h.bound).mp word
  rcases h.cached with zero | cached
  · exfalso
    exact counter_ne_zero _ (same.trans (h.words.counterWord.trans (by rw [zero]; rfl)))
  · rw [← equal] at cached
    exact cached

theorem Selected.invariant {s t : State} {p : Params} {pass lane slice old : Nat}
    (ready : Ready p pass lane slice old s) (h : Selected s t p pass lane slice) :
    Invariant p pass lane slice (wanted s) t := by
  have bp := h.regs .x19 (by simp [FillCompress.loopRegs])
  refine ⟨h.layout, ?_, ?_, h.words ready, wanted_bound s, Or.inr ?_⟩
  · rw [h.rd, h.wr, bp]; exact ready.reads
  · rw [h.wr, bp]; exact ready.write
  · rw [h.work_eq]; exact h.block

theorem Invariant.of_state {p : Params} {pass lane slice old : Nat} {s t : State}
    (h : Invariant p pass lane slice old s)
    (regs : ∀ r ∈ [Reg.x19, .x24, .x22], t.gpr r = s.gpr r)
    (sp : t.sp = s.sp) (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
    Invariant p pass lane slice old t := by
  have bp := regs .x19 (by simp)
  have work : AddressCalls.work t = AddressCalls.work s := by
    unfold AddressCalls.work; rw [mem, bp]
  refine ⟨?_, ?_, ?_, ?_, h.bound, ?_⟩
  · constructor
    · rw [rd, wr, bp]; exact h.layout.frameRead
    · rw [wr, work]; exact h.layout.workWrite
    · rw [bp, work]; exact h.layout.frameWork
    · rw [bp, sp]; exact h.layout.frameStack
    · rw [sp, work]; exact h.layout.stackWork
  · rw [rd, wr, bp]; exact h.reads
  · rw [wr, bp]; exact h.write
  · exact ⟨by rw [mem, bp]; exact h.words.passWord,
      (regs .x24 (by simp)).trans h.words.laneWord,
      (regs .x22 (by simp)).trans h.words.sliceWord,
      by rw [mem, bp]; exact h.words.blocksWord,
      by rw [mem, bp]; exact h.words.passesWord,
      by rw [mem, bp]; exact h.words.variantWord,
      by rw [mem, bp]; exact h.words.counterWord⟩
  · rw [mem, work]; exact h.cached

theorem Invariant.of_keeps {p : Params} {pass lane slice old : Nat} {s t : State}
    (h : Invariant p pass lane slice old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    Invariant p pass lane slice old t := by
  apply h.of_state _ k.sp k.mem k.rd k.wr
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact k.regs _ (by decide)

end VG.Proof.Argon2.AArch64.AddressCache
end

/-! Retain the source invariants while selecting the public addressing mode. -/

namespace VG.Proof.Argon2.AArch64.RandomSource

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.RandomSource

structure Ready (p : Params) (pass lane slice index old : Nat) (s : State) : Prop where
  filling : FillKernel.Ready p pass lane slice index s
  cache : AddressCache.Invariant p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩

theorem Ready.of_keeps {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : Ready p pass lane slice index old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    Ready p pass lane slice index old t := by
  refine ⟨h.filling.of_keeps k, h.cache.of_keeps k, ?_⟩
  have matrix : FillKernel.matrix t = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [k.mem, k.regs .x19 (by decide)]
  have work : AddressCalls.work t = AddressCalls.work s := by
    unfold AddressCalls.work; rw [k.mem, k.regs .x19 (by decide)]
  rw [matrix, work]; exact h.matrixWork

theorem test_ok (s : State) : WP isa (.block test) s fun t =>
    eval (.zero .x .x15) t = some (decide (s.gpr .x6 = 0#64)) ∧
      Divide.Keeps [.x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [test, Impl.Argon2.AArch64.Instructions.comparei,
    Impl.Argon2.AArch64.Instructions.compare, Impl.Argon2.AArch64.Instructions.imm,
    show 0 < 65536 from by decide, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, Size.bits, Nat.reduceMul, Nat.reduceLT,
    show (63 : Nat) < 64 from by decide, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, BitVec.setWidth_eq,
    Bool.toNat_true, sub_value, show (0#16).setWidth 64 = 0#64 from rfl, BitVec.sub_zero, reduceCtorEq, ite_true, ite_false,
    eval, Bool.beq_eq_decide_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem bool_zero : ∀ b : Bool, decide ((BitVec.ofBool b).setWidth 64 = 0#64) = !b := by
  decide +kernel

theorem prepare_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : Ready p pass lane slice index old s) : WP isa prepare s fun t =>
      eval (.zero .x .x15) t = some (!independent p pass slice) ∧ Divide.Keeps ReferenceMap.changed s t := by
  unfold prepare
  refine WP.seq ((AddressMode.code_spec_ok s p pass slice
    (h.cache.reads 112 (by simp)) (h.cache.reads 0 (by simp))
    h.cache.words.variantWord h.filling.passWord h.filling.position.slice
    (Nat.lt_trans h.filling.bounds.passBound (by decide))
    (Nat.lt_trans h.filling.bounds.sliceBound (by decide))).mono ?_)
  rintro a ⟨mode, keeps⟩
  refine (test_ok a).mono ?_
  rintro t ⟨flag, tested⟩
  refine ⟨?_, (keeps.mono (by decide)).trans (tested.mono (by decide))⟩
  rw [flag, mode, bool_zero]

end VG.Proof.Argon2.AArch64.RandomSource

end

end


/-! Merged from `Proof.Argon2.AArch64.DependentWordState`. -/

@[expose] public section

section
/-! The dependent source hands the filling step its random word and unchanged matrix. -/

namespace VG.Proof.Argon2.AArch64.DependentWord

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.DependentWord

theorem state_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (dependent : independent p pass slice = false) : WP isa code s fun t =>
      t.gpr .x0 = Proof.Argon2.FillStep.random p pass lane slice index state.memory ∧
      FillKernel.Ready p pass lane slice index t ∧
      Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory ∧
      Divide.Keeps ReferenceMap.changed s t := by
  refine (code_spec_ok s p pass lane slice index h state represented dependent).mono ?_
  rintro t ⟨random, keeps⟩
  refine ⟨random, h.of_keeps keeps, ?_, keeps⟩
  have base : FillKernel.matrix t = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .x19 (by decide)]
  rw [keeps.mem, base]; exact represented

end VG.Proof.Argon2.AArch64.DependentWord
end

/-! Both random sources satisfy the same filling-step postcondition. -/

namespace VG.Proof.Argon2.AArch64.RandomSource

open VG VG.AArch64 VG.Spec.Argon2

def writes (s : State) : List Region := AddressCache.writes s

structure Done (s t : State) (p : Params) (pass lane slice index : Nat) (state : FillState) : Prop where
  random : t.gpr .x0 = Proof.Argon2.FillStep.random p pass lane slice index state.memory
  ready : ∃ old, Ready p pass lane slice index old t
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s) s.mem t.mem
  sp : t.sp = s.sp

theorem Ready.index_nat {p : Params} {pass lane slice index old : Nat} {s : State}
    (h : Ready p pass lane slice index old s) : (s.gpr .x23).toNat = index := by
  rw [h.filling.position.index, ReferenceMap.word_nat index h.filling.bounds.index_bound64]

theorem independent_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (mode : independent p pass slice = true) :
    WP isa Impl.Argon2.AArch64.AddressCache.code s (Done s · p pass lane slice index state) := by
  refine (AddressCache.code_ok p pass lane slice old s h.cache.ready).mono ?_
  intro t done
  have base : FillKernel.matrix t = FillKernel.matrix s :=
    done.selected.frame_word h.cache.layout 232 (by decide) (by decide)
  have nextReady : Ready p pass lane slice index (AddressCache.wanted s) t := by
    refine ⟨done.selected.filling_ready h.cache.layout h.filling,
      done.selected.invariant h.cache.ready, ?_⟩
    rw [base, done.selected.work_eq]; exact h.matrixWork
  refine ⟨?_, ⟨_, nextReady⟩,
    done.selected.represents h.cache.layout h.filling h.matrixWork state.memory represented,
    done.selected.regs, done.selected.rd, done.selected.wr, done.selected.frame, done.selected.sp⟩
  have random := done.random
  unfold AddressCache.wanted at random
  rw [h.index_nat] at random
  unfold Proof.Argon2.FillStep.random
  simp only [mode, ite_true]
  exact random

theorem dependent_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (mode : independent p pass slice = false) :
    WP isa Impl.Argon2.AArch64.DependentWord.code s (Done s · p pass lane slice index state) := by
  refine (DependentWord.state_ok s p pass lane slice index h.filling state represented mode).mono ?_
  rintro t ⟨random, _, matrix, keeps⟩
  refine ⟨random, ⟨old, h.of_keeps keeps⟩, matrix, ?_, keeps.rd, keeps.wr, ?_, keeps.sp⟩
  · intro r hr
    apply keeps.regs
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [keeps.mem]; exact Frame.refl _ _

theorem code_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.RandomSource.code s (Done s · p pass lane slice index state) := by
  unfold Impl.Argon2.AArch64.RandomSource.code
  refine WP.seq ((prepare_ok s p pass lane slice index old h).mono ?_)
  rintro a ⟨flag, keeps⟩
  have next := h.of_keeps keeps
  have representedA : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks state.memory := by
    have base : FillKernel.matrix a = FillKernel.matrix s := by
      unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .x19 (by decide)]
    rw [base, keeps.mem]; exact represented
  have finish {t : State} (done : Done a t p pass lane slice index state) :
      Done s t p pass lane slice index state := by
    refine ⟨done.random, done.ready, done.represented, ?_, done.rd.trans keeps.rd,
      done.wr.trans keeps.wr, ?_, done.sp.trans keeps.sp⟩
    · intro r hr
      have ne : r ∉ ReferenceMap.changed := by
        simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (done.regs r hr).trans (keeps.regs r ne)
    · have frame := done.frame
      unfold writes AddressCache.writes AddressCalls.work at frame ⊢
      rw [keeps.mem, keeps.regs .x19 (by decide), keeps.sp] at frame
      exact frame
  refine WP.ite (!independent p pass slice) flag ?_ ?_
  · intro mode
    have dependent : independent p pass slice = false := by
      cases eq : independent p pass slice <;> simp_all
    exact (dependent_ok a p pass lane slice index old next state representedA dependent).mono
      (fun _ done => finish done)
  · intro mode
    have independent : independent p pass slice = true := by
      cases eq : independent p pass slice <;> simp_all
    exact (independent_ok a p pass lane slice index old next state representedA independent).mono
      (fun _ done => finish done)

end VG.Proof.Argon2.AArch64.RandomSource

end

end


/-! Merged from `Proof.Argon2.AArch64.RandomSourceState`. -/

@[expose] public section

section
/-! Frame words and public allocation pointers survive random-word dispatch. -/

namespace VG.Proof.Argon2.AArch64.RandomSource

open VG VG.AArch64 VG.Spec.Argon2

theorem Done.frame_word {s t : State} {p : Params} {pass lane slice index old : Nat} {state : FillState}
    (h : Ready p pass lane slice index old s) (done : Done s t p pass lane slice index state)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 8 ∨ 16 ≤ d) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.regs .x19 (by simp [FillCompress.loopRegs])]
  have sub : Region.Sub ⟨off (s.gpr .x19) d, 8⟩ ⟨s.gpr .x19, 272⟩ := Offset.sub_base _ bound
  exact done.frame.readW (r := ⟨off (s.gpr .x19) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [writes, AddressCache.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.cache.layout.frameWork.sub_left sub
    · exact h.cache.layout.frameStack.sub_left sub
    · exact Offset.disjoint _ separate (by omega_using [bound]) (by decide)) (by decide)

end VG.Proof.Argon2.AArch64.RandomSource
end

/-! Merged from `Proof.Argon2.AArch64.FillCacheInvariant`. -/
section
/-! The cell update does not disturb the cached independent-address block. -/

namespace VG.Proof.Argon2.AArch64.RandomSource

open VG VG.AArch64 VG.Spec.Argon2

theorem Ready.after_fill {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : Ready p pass lane slice index old s) (done : FillKernel.Done s t p pass lane slice index) :
    Ready p pass lane slice index old t := by
  have bp := done.regs .x19 (by simp [FillCompress.loopRegs])
  have sp := done.sp
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word h.filling 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work s := done.frame_word h.filling 248 (by decide) (by decide)
  refine ⟨done.retains h.filling, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, h.cache.bound, ?_⟩
    · constructor
      · rw [done.rd, done.wr, bp]; exact h.cache.layout.frameRead
      · rw [done.wr, work]; exact h.cache.layout.workWrite
      · rw [bp, work]; exact h.cache.layout.frameWork
      · rw [bp, sp]; exact h.cache.layout.frameStack
      · rw [sp, work]; exact h.cache.layout.stackWork
    · rw [done.rd, done.wr, bp]; exact h.cache.reads
    · rw [done.wr, bp]; exact h.cache.write
    · exact ⟨(done.frame_word h.filling 0 (by decide) (by decide)).trans h.cache.words.passWord,
        (done.regs .x24 (by simp [FillCompress.loopRegs])).trans h.cache.words.laneWord,
        (done.regs .x22 (by simp [FillCompress.loopRegs])).trans h.cache.words.sliceWord,
        (done.frame_word h.filling 240 (by decide) (by decide)).trans h.cache.words.blocksWord,
        (done.frame_word h.filling 72 (by decide) (by decide)).trans h.cache.words.passesWord,
        (done.frame_word h.filling 112 (by decide) (by decide)).trans h.cache.words.variantWord,
        (done.frame_word h.filling 8 (by decide) (by decide)).trans h.cache.words.counterWord⟩
    · rcases h.cache.cached with zero | cached
      · exact Or.inl zero
      · apply Or.inr
        rw [work]
        have kept : blockAt t.mem (off (AddressCalls.work s) 6144) =
            blockAt s.mem (off (AddressCalls.work s) 6144) := by
          apply FillCompress.block_frame done.frame
          intro r hr
          simp only [FillKernel.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
          have cacheSub : Region.Sub ⟨off (AddressCalls.work s) 6144, 1024⟩ ⟨AddressCalls.work s, 8192⟩ :=
            Offset.sub_base _ (by decide)
          rcases hr with rfl | rfl | rfl | rfl
          · exact (h.matrixWork.symm.sub_left cacheSub).sub_right
              (FillKernel.cell_sub p _ h.filling.bounds.lanesPositive h.filling.bounds.laneBound
                (Proof.Argon2.column_lt p h.filling.bounds.lanesPositive
                  h.filling.bounds.sliceBound h.filling.bounds.indexBound))
          · exact Offset.disjoint_base (AddressCalls.work s) (d := 6144) (n := 1024) (k := 5120)
              (by decide) (by decide)
          · exact h.cache.layout.stackWork.symm.sub_left cacheSub
          · exact (h.cache.layout.frameWork.symm.sub_left cacheSub).sub_right
              (Offset.sub_base _ (by decide))
        exact kept.trans cached
  · rw [base, work]; exact h.matrixWork

end VG.Proof.Argon2.AArch64.RandomSource
end

/-! Merged from `Proof.Argon2.AArch64.FillBlockFrame`. -/
section
/-! Compose scratch writes with a matrix-cell write inside the derive allocation. -/

namespace VG.Proof.Argon2.AArch64.FillBlock

open VG VG.AArch64 VG.Spec.Argon2

def writes (s : State) (p : Params) : List Region :=
  [⟨FillKernel.matrix s, p.blocks * 1024⟩, ⟨AddressCalls.work s, 8192⟩,
    below s.sp 8, ⟨off (s.gpr .x19) 8, 16⟩]

theorem source_frame {s t : State} {p : Params} {pass lane slice index : Nat} {state : FillState}
    (done : RandomSource.Done s t p pass lane slice index state) : Frame (writes s p) s.mem t.mem := by
  apply done.frame.sub
  intro r hr
  simp only [RandomSource.writes, AddressCache.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨⟨off (s.gpr .x19) 8, 16⟩, by simp [writes], Region.sub_prefix (by decide)⟩

theorem kernel_frame {s t : State} {p : Params} {pass lane slice index : Nat}
    (ready : FillKernel.Ready p pass lane slice index s) (done : FillKernel.Done s t p pass lane slice index) :
    Frame (writes s p) s.mem t.mem := by
  apply done.frame.sub
  intro r hr
  simp only [FillKernel.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [writes], FillKernel.cell_sub p _ ready.bounds.lanesPositive ready.bounds.laneBound
      (Proof.Argon2.column_lt p ready.bounds.lanesPositive ready.bounds.sliceBound ready.bounds.indexBound)⟩
  · exact ⟨⟨AddressCalls.work s, 8192⟩, by simp [writes], Region.sub_prefix (by decide)⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], Offset.sub _ (d := 16) (n := 8) (e := 8) (k := 16)
      (by decide) (by decide)⟩

end VG.Proof.Argon2.AArch64.FillBlock
end

/-! Complete active filling cell against the reviewed matrix transition. -/

namespace VG.Proof.Argon2.AArch64.FillBlock

open VG VG.AArch64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass lane slice index : Nat) (state : FillState) : Prop where
  ready : ∃ old, RandomSource.Ready p pass lane slice index old t
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (fillBlock p pass slice lane index state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem
  sp : t.sp = s.sp

theorem code_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillBlock.code s (Done s · p pass lane slice index state) := by
  unfold Impl.Argon2.AArch64.FillBlock.code
  refine WP.seq ((RandomSource.code_ok s p pass lane slice index old h state represented).mono ?_)
  intro a source
  obtain ⟨counter, ready⟩ := source.ready
  have baseA : FillKernel.matrix a = FillKernel.matrix s := source.frame_word h 232 (by decide) (by decide)
  have workA : AddressCalls.work a = AddressCalls.work s := source.frame_word h 248 (by decide) (by decide)
  refine (FillKernel.code_spec_ok a p pass lane slice index ready.filling state source.represented source.random).mono ?_
  rintro t ⟨done, matrix⟩
  have baseT : FillKernel.matrix t = FillKernel.matrix a := done.frame_word ready.filling 232 (by decide) (by decide)
  have workT : AddressCalls.work t = AddressCalls.work a := done.frame_word ready.filling 248 (by decide) (by decide)
  refine ⟨⟨counter, ready.after_fill done⟩, ?_, baseT.trans baseA, workT.trans workA, ?_,
    done.rd.trans source.rd, done.wr.trans source.wr, ?_, done.sp.trans source.sp⟩
  · rw [baseT]; exact matrix
  · intro r hr; exact (done.regs r hr).trans (source.regs r hr)
  · have frame := kernel_frame ready.filling done
    rw [writes, baseA, workA, source.sp,
      source.regs .x19 (by simp [FillCompress.loopRegs])] at frame
    exact (source_frame source).trans frame

end VG.Proof.Argon2.AArch64.FillBlock

end

end


/-! Merged from `Proof.Argon2.AArch64.FillIndex`. -/

@[expose] public section

section
/-! Public segment-index advancement retains the filling and cache allocations. -/

namespace VG.Proof.Argon2.AArch64.FillSegment

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillSegment

theorem advance_ok (s : State)
    (ha : (s.gpr .x23 + 1).toNat < 2 ^ 63) (hb : (s.gpr .x21).toNat < 2 ^ 63) :
    WP isa (.block advance) s fun t =>
      t.gpr .x23 = s.gpr .x23 + 1 ∧
      eval (.nonzero .x .x14) t = some (decide ((s.gpr .x23 + 1).toNat < (s.gpr .x21).toNat)) ∧
      Divide.Keeps [.x23, .x12, .x14, .x15] s t := by
  simp only [advance, List.flatten_cons, List.flatten_nil, List.append_nil]
  apply WP.block_append
  refine (Instructions.addi_ok s .x23 1 (by decide) (by decide) (by decide)).mono ?_
  rintro a ⟨value, ka⟩
  have endEq := ka.regs .x21 (by decide)
  refine (Instructions.compare_ok a .x23 .x21 (by rw [value]; exact ha)
    (by rw [endEq]; exact hb)).mono ?_
  rintro t ⟨flag, kt⟩
  refine ⟨(kt.regs .x23 (by decide)).trans value, ?_, ?_⟩
  · simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag, value, endEq]
    cases decide ((s.gpr .x23 + 1).toNat < (s.gpr .x21).toNat) <;> rfl
  · exact (ka.mono (by decide)).trans (kt.mono (by decide))

theorem advance_nat_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) : WP isa (.block advance) s fun t =>
      t.gpr .x23 = BitVec.ofNat 64 (index + 1) ∧
      eval (.nonzero .x .x14) t = some (decide (index + 1 < p.segmentLen)) ∧ Divide.Keeps [.x23, .x12, .x14, .x15] s t := by
  have inputBound : (s.gpr .x23 + 1).toNat < 2 ^ 63 := by
    rw [h.position.index, show (1 : Addr) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add,
      ReferenceMap.word_nat (index + 1) (by
        have := h.bounds.indexBound
        have := h.bounds.segment_le_lane
        have := h.bounds.laneLength_bound
        omega_arith)]
    have := h.bounds.indexBound
    have := h.bounds.segment_le_lane
    have := h.bounds.laneLength_bound
    omega_arith
  have endBound63 : (s.gpr .x21).toNat < 2 ^ 63 := by
    rw [h.position.segmentLength, ReferenceMap.word_nat p.segmentLen
      (Nat.lt_of_le_of_lt h.bounds.segment_le_lane
        (Nat.lt_trans h.bounds.laneLength_bound (by decide)))]
    have := h.bounds.segment_le_lane
    have := h.bounds.laneLength_bound
    omega_arith
  refine (advance_ok s inputBound endBound63).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have added : s.gpr .x23 + 1 = BitVec.ofNat 64 (index + 1) := by
    rw [h.position.index, BitVec.ofNat_add]; rfl
  have endBound : p.segmentLen < 2 ^ 64 := Nat.lt_of_le_of_lt h.bounds.segment_le_lane
    (Nat.lt_trans h.bounds.laneLength_bound (by decide))
  have indexBound := h.bounds.indexBound
  refine ⟨value.trans added, ?_, keeps⟩
  rw [flag, added, h.position.segmentLength,
    ReferenceMap.word_nat (index + 1) (by omega_using [endBound, indexBound]), ReferenceMap.word_nat p.segmentLen endBound]

theorem next_ready {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : RandomSource.Ready p pass lane slice index old s)
    (k : Divide.Keeps [.x23, .x12, .x14, .x15] s t) (value : t.gpr .x23 = BitVec.ofNat 64 (index + 1))
    (active : index + 1 < p.segmentLen) : RandomSource.Ready p pass lane slice (index + 1) old t := by
  have bp := k.regs .x19 (by decide)
  have sp := k.sp
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [k.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [k.mem, bp]
  have kernelWork : FillKernel.work t = FillKernel.work s := work
  refine ⟨?_, h.cache.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact k.regs _ (by decide)) k.sp k.mem k.rd k.wr, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · constructor
      · rw [k.rd, k.wr, bp]; exact h.filling.layout.frameRead
      · rw [k.wr, bp]; exact h.filling.layout.frameWrite
      · rw [base, k.wr]; exact h.filling.layout.matrixWrite
      · rw [kernelWork, k.wr]; exact h.filling.layout.workWrite
      · rw [base, kernelWork]; exact h.filling.layout.matrixWork
      · rw [base, bp]; exact h.filling.layout.matrixFrame
      · rw [base, sp]; exact h.filling.layout.matrixStack
      · rw [bp, kernelWork]; exact h.filling.layout.frameWork
      · rw [bp, sp]; exact h.filling.layout.frameStack
      · rw [sp, kernelWork]; exact h.filling.layout.stackWork
    · have bounds := h.filling.bounds
      refine ⟨bounds.lanesPositive, bounds.lanesBound, bounds.memoryMinimum, bounds.memoryBound,
        bounds.passBound, bounds.laneBound, bounds.sliceBound, active, ?_⟩
      rcases bounds.active with hp | hs | hi
      · exact Or.inl hp
      · exact Or.inr (Or.inl hs)
      · exact Or.inr (Or.inr (by omega_using [hi]))
    · exact ⟨(k.regs .x24 (by decide)).trans h.filling.position.current,
        (k.regs .x20 (by decide)).trans h.filling.position.laneLength,
        (k.regs .x21 (by decide)).trans h.filling.position.segmentLength,
        (k.regs .x22 (by decide)).trans h.filling.position.slice, value⟩
    · rw [k.mem, bp]; exact h.filling.passWord
    · rw [k.mem, bp]; exact h.filling.lanesWord
  · rw [base, work]; exact h.matrixWork

end VG.Proof.Argon2.AArch64.FillSegment
end

/-! Merged from `Proof.Argon2.AArch64.FillAllocation`. -/
section
/-! Transport the allocation using just its public pointers and permissions. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

theorem Layout.of_preserved {p : Params} {s t : State} (h : Layout p s)
    (bp : t.gpr .x19 = s.gpr .x19) (sp : t.sp = s.sp)
    (base : matrix t = matrix s) (scratch : work t = work s)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Layout p t := by
  constructor
  · rw [rd, wr, bp]; exact h.frameRead
  · rw [wr, bp]; exact h.frameWrite
  · rw [base, wr]; exact h.matrixWrite
  · rw [scratch, wr]; exact h.workWrite
  · rw [base, scratch]; exact h.matrixWork
  · rw [base, bp]; exact h.matrixFrame
  · rw [base, sp]; exact h.matrixStack
  · rw [bp, scratch]; exact h.frameWork
  · rw [bp, sp]; exact h.frameStack
  · rw [sp, scratch]; exact h.stackWork

end VG.Proof.Argon2.AArch64.FillKernel
end

/-! One segment iteration updates the specified cell and advances its public index. -/

namespace VG.Proof.Argon2.AArch64.FillSegment

open VG VG.AArch64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass lane slice index : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (fillBlock p pass slice lane index state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  position : ReferenceMap.Position p lane slice (index + 1) t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x23 → t.gpr r = s.gpr r
  layout : FillKernel.Layout p t
  cache : ∃ old, AddressCache.Invariant p pass lane slice old t
  matrixWork : (⟨FillKernel.matrix t, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work t, 8192⟩
  passWord : t.mem.readW (off (t.gpr .x19) 0) 64 = BitVec.ofNat 64 pass
  lanesWord : t.mem.readW (off (t.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes
  cf : eval (.nonzero .x .x14) t = some (decide (index + 1 < p.segmentLen))
  next : index + 1 < p.segmentLen → ∃ old, RandomSource.Ready p pass lane slice (index + 1) old t

theorem body_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillSegment.body s (Done s · p pass lane slice index state) := by
  unfold Impl.Argon2.AArch64.FillSegment.body
  refine WP.seq ((FillBlock.code_ok s p pass lane slice index old h state represented).mono ?_)
  intro a filled
  obtain ⟨counter, ready⟩ := filled.ready
  refine (advance_nat_ok a p pass lane slice index ready.filling).mono ?_
  rintro t ⟨value, cf, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [keeps.mem, bp]
  refine ⟨?_, base.trans filled.matrix, work.trans filled.work, ?_, keeps.rd.trans filled.rd,
    keeps.wr.trans filled.wr, ?_, keeps.sp.trans filled.sp, ?_, ?_, ?_, ?_, ?_, ?_, cf, ?_⟩
  · rw [keeps.mem, base]; exact filled.represented
  · exact ⟨(keeps.regs .x24 (by decide)).trans ready.filling.position.current,
      (keeps.regs .x20 (by decide)).trans ready.filling.position.laneLength,
      (keeps.regs .x21 (by decide)).trans ready.filling.position.segmentLength,
      (keeps.regs .x22 (by decide)).trans ready.filling.position.slice, value⟩
  · rw [keeps.mem]; exact filled.frame
  · intro r hr ne
    have outside : r ∉ [Reg.x23, .x12, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    exact (keeps.regs r outside).trans (filled.regs r hr)
  · exact ready.filling.layout.of_preserved bp (keeps.sp) base work keeps.rd keeps.wr
  · exact ⟨counter, ready.cache.of_state (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.sp keeps.mem keeps.rd keeps.wr⟩
  · rw [base, work]; exact ready.matrixWork
  · rw [keeps.mem, bp]; exact ready.filling.passWord
  · rw [keeps.mem, bp]; exact ready.filling.lanesWord
  · intro active; exact ⟨counter, next_ready ready keeps value active⟩

end VG.Proof.Argon2.AArch64.FillSegment

end

end


/-! Termination and correctness of the active suffix of one segment. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.FillSegment

open VG VG.AArch64 VG.Spec.Argon2

structure Finished (s t : State) (p : Params) (pass lane slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  position : ReferenceMap.Position p lane slice p.segmentLen t
  layout : FillKernel.Layout p t
  cache : ∃ old, AddressCache.Invariant p pass lane slice old t
  matrixWork : (⟨FillKernel.matrix t, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work t, 8192⟩
  passWord : t.mem.readW (off (t.gpr .x19) 0) 64 = BitVec.ofNat 64 pass
  lanesWord : t.mem.readW (off (t.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x23 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  sp : t.sp = s.sp

theorem Done.finished {s t : State} {p : Params} {pass lane slice index : Nat} {state : FillState}
    (h : Done s t p pass lane slice index state) (last : index + 1 = p.segmentLen) :
    Finished s t p pass lane slice (fillBlock p pass slice lane index state) :=
  ⟨h.represented, h.matrix, h.work, last ▸ h.position, h.layout, h.cache,
    h.matrixWork, h.passWord, h.lanesWord, h.regs, h.rd, h.wr, h.frame, h.sp⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass lane slice index : Nat}
    {state finalState : FillState} (first : Done s a p pass lane slice index state)
    (rest : Finished a t p pass lane slice finalState) : Finished s t p pass lane slice finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work,
    rest.position, rest.layout, rest.cache, rest.matrixWork, rest.passWord, rest.lanesWord,
    ?_, rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.sp.trans first.sp⟩
  · intro r hr ne; exact (rest.regs r hr ne).trans (first.regs r hr ne)
  · have frame := rest.frame
    rw [FillBlock.writes, first.matrix, first.work,
      first.sp,
      first.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)] at frame
    exact first.frame.trans frame

theorem loop_ok (count : Nat) (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endIndex : index + count = p.segmentLen) :
    WP isa Impl.Argon2.AArch64.FillSegment.loop s
      (Finished s · p pass lane slice (Proof.Argon2.segment p pass lane slice index count state)) := by
  induction count generalizing s index old state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := body_ok s p pass lane slice index old h state represented
    rw [Proof.Argon2.segment_succ]
    cases n with
    | zero =>
      have last : index + 1 = p.segmentLen := endIndex
      refine ⟨_, a, .loopExit run ?_, ?_⟩
      · simp only [done.cf, last, Nat.lt_irrefl, decide_false]
      · exact done.finished last
    | succ n =>
      have active : index + 1 < p.segmentLen := by omega_using [endIndex]
      obtain ⟨nextCounter, nextReady⟩ := done.next active
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (index + 1) nextCounter nextReady
        (fillBlock p pass slice lane index state) done.represented (by omega_using []) (by omega_using [endIndex])
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [done.cf, active, decide_true]

end VG.Proof.Argon2.AArch64.FillSegment

end

end


/-! Merged from `Proof.Argon2.AArch64.FillContext`. -/

@[expose] public section

section
/-! A segment context allows its starting and final indices, including an empty suffix. -/

namespace VG.Proof.Argon2.AArch64.FillContext

open VG VG.AArch64 VG.Spec.Argon2

structure Parameters (p : Params) (pass lane slice : Nat) : Prop where
  lanesPositive : 0 < p.lanes
  lanesBound : p.lanes < 2 ^ 32
  memoryMinimum : 8 * p.lanes ≤ p.memory
  memoryBound : p.memory < 2 ^ 32
  passBound : pass < 2 ^ 32
  laneBound : lane < p.lanes
  sliceBound : slice < 4

structure Ready (p : Params) (pass lane slice index old : Nat) (s : State) : Prop where
  parameters : Parameters p pass lane slice
  layout : FillKernel.Layout p s
  cache : AddressCache.Invariant p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  position : ReferenceMap.Position p lane slice index s
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

theorem Ready.activate {p : Params} {pass lane slice index old : Nat} {s : State}
    (h : Ready p pass lane slice index old s) (bound : index < p.segmentLen)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) : RandomSource.Ready p pass lane slice index old s :=
  ⟨⟨h.layout, ⟨h.parameters.lanesPositive, h.parameters.lanesBound, h.parameters.memoryMinimum,
    h.parameters.memoryBound, h.parameters.passBound, h.parameters.laneBound, h.parameters.sliceBound,
    bound, active⟩, h.position, h.cache.words.passWord, h.lanesWord⟩, h.cache, h.matrixWork⟩

theorem Parameters.segment_bound {p : Params} {pass lane slice : Nat} (h : Parameters p pass lane slice) :
    2 ≤ p.segmentLen ∧ p.segmentLen < 2 ^ 64 := by
  have minimum := Proof.Argon2.segmentLen_ge_two p h.lanesPositive h.memoryMinimum
  have le : p.segmentLen ≤ p.blocks := by
    have blocks := Proof.Argon2.blocks_lanes p h.lanesPositive
    have segments := Proof.Argon2.laneLen_segments p h.lanesPositive
    have laneLe : p.laneLen ≤ p.blocks := by rw [blocks]; exact Nat.le_mul_of_pos_left _ h.lanesPositive
    omega_using [segments, laneLe]
  exact ⟨minimum, Nat.lt_of_le_of_lt le
    (Nat.lt_trans (Nat.lt_of_le_of_lt (Proof.Argon2.blocks_le_memory p) h.memoryBound) (by decide))⟩

theorem Ready.of_keeps {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : Ready p pass lane slice index old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    Ready p pass lane slice index old t := by
  have bp := k.regs .x19 (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [k.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [k.mem, bp]
  refine ⟨h.parameters, h.layout.of_preserved bp (k.sp) base work k.rd k.wr,
    h.cache.of_keeps k, ?_, h.position.of_keeps k, ?_⟩
  · rw [base, work]; exact h.matrixWork
  · rw [k.mem, bp]; exact h.lanesWord

theorem finished_context {p : Params} {pass lane slice : Nat} {s t : State} {state : FillState}
    (parameters : Parameters p pass lane slice) (h : FillSegment.Finished s t p pass lane slice state) :
    ∃ old, Ready p pass lane slice p.segmentLen old t := by
  obtain ⟨old, cache⟩ := h.cache
  exact ⟨old, parameters, h.layout, cache, h.matrixWork, h.position, h.lanesWord⟩

end VG.Proof.Argon2.AArch64.FillContext
end

/-! Select index two only in slice zero of pass zero. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.SegmentSetup

def start (pass slice : Nat) : Nat := if pass = 0 ∧ slice = 0 then 2 else 0

theorem start_active (pass slice : Nat) : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ start pass slice := by
  unfold start; split <;> omega_arith

theorem start_le (pass slice : Nat) (g : Nat) (minimum : 2 ≤ g) : start pass slice ≤ g := by
  unfold start; split <;> omega_arith

theorem first_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8) :
    WP isa (.block first) s fun t =>
      eval (.zero .x .x15) t = some (decide (s.mem.readW (off (s.gpr .x19) 0) 64 = 0#64 ∧ s.gpr .x22 = 0#64)) ∧
      Divide.Keeps [.x3, .x13, .x14, .x15] s t := by
  simp only [off, BitVec.add_zero] at hr
  apply WP.of_runBlock
  simp only [first, Impl.Argon2.AArch64.Instructions.load,
    Impl.Argon2.AArch64.Instructions.logic, Impl.Argon2.AArch64.Instructions.mark,
    Impl.Argon2.AArch64.Instructions.mov, Impl.Argon2.AArch64.Instructions.comparei,
    Impl.Argon2.AArch64.Instructions.compare, Impl.Argon2.AArch64.Instructions.imm,
    show 0 < 65536 from by decide, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, addr, State.load, Size.bytes, Size.bits,
    show 0 % 8 = 0 ∧ 0 < 4096 * 8 from by decide, hr, and_self,
    show 0 < 4096 from by decide, Nat.reduceMul, Nat.reduceLT,
    show (63 : Nat) < 64 from by decide, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, BitVec.setWidth_eq, BitVec.add_zero,
    Bool.toNat_true, sub_value, show (0#16).setWidth 64 = 0#64 from rfl,
    BitVec.sub_zero, reduceCtorEq, ite_true, ite_false,
    eval, Bool.beq_eq_decide_eq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', off]
  refine ⟨?_, ?_⟩
  · congr 1
    exact propext BitVec.or_eq_zero_iff
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    all_goals rfl

theorem register_ok (s : State) (register : Reg) (value : Nat) (bound : value < 65536) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.imm register value].flatten) s fun t =>
      t.gpr register = BitVec.ofNat 64 value ∧ Divide.Keeps [register] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.Instructions.imm, bound, ite_true,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits, Nat.reduceMul,
    Nat.reduceLT, BitVec.shiftLeft_zero, RegUpd.gpr_write,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · change (BitVec.ofNat 16 value).setWidth 64 = BitVec.ofNat 64 value
    exact BitVec.setWidth_ofNat_of_le_of_lt (by decide) bound
  · constructor
    · intro r hr
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_write, hr, ite_false]
    all_goals rfl

theorem index_ok (s : State) (pass slice : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8)
    (passWord : s.mem.readW (off (s.gpr .x19) 0) 64 = BitVec.ofNat 64 pass)
    (sliceWord : s.gpr .x22 = BitVec.ofNat 64 slice)
    (passBound : pass < 2 ^ 64) (sliceBound : slice < 2 ^ 64) : WP isa index s fun t =>
      t.gpr .x23 = BitVec.ofNat 64 (start pass slice) ∧ Divide.Keeps [.x3, .x23, .x13, .x14, .x15] s t := by
  unfold index
  refine WP.seq ((first_ok s hr).mono ?_)
  rintro a ⟨flag, keeps⟩
  have firstFlag : eval (.zero .x .x15) a = some (decide (pass = 0 ∧ slice = 0)) := by
    rw [flag, passWord, sliceWord]
    have passZero : BitVec.ofNat 64 pass = 0#64 ↔ pass = 0 := ReferenceMap.word_zero pass passBound
    have sliceZero : BitVec.ofNat 64 slice = 0#64 ↔ slice = 0 := ReferenceMap.word_zero slice sliceBound
    simp only [passZero, sliceZero]
  refine WP.ite (decide (pass = 0 ∧ slice = 0)) firstFlag ?_ ?_
  · intro mode
    refine (register_ok a .x23 2 (by decide)).mono ?_
    rintro t ⟨value, changed⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (changed.mono (by decide))⟩
    unfold start; simp only [of_decide_eq_true mode]; exact value
  · intro mode
    refine (register_ok a .x23 0 (by decide)).mono ?_
    rintro t ⟨value, changed⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (changed.mono (by decide))⟩
    unfold start; simp only [of_decide_eq_false mode, ite_false]; exact value

theorem check_ok (s : State)
    (ha : (s.gpr .x23).toNat < 2 ^ 63) (hb : (s.gpr .x21).toNat < 2 ^ 63) :
    WP isa (.block check) s fun t =>
      eval (.nonzero .x .x14) t = some (decide ((s.gpr .x23).toNat < (s.gpr .x21).toNat)) ∧
      Divide.Keeps [.x14, .x15] s t := by
  simp only [check, List.flatten_cons, List.flatten_nil, List.append_nil]
  refine (Instructions.compare_ok s .x23 .x21 ha hb).mono ?_
  rintro t ⟨value, keeps⟩
  refine ⟨?_, keeps⟩
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, value]
  cases decide ((s.gpr .x23).toNat < (s.gpr .x21).toNat) <;> rfl

end VG.Proof.Argon2.AArch64.SegmentSetup

end

end

/-! Merged from `Proof.Argon2.AArch64.SegmentSetupReset`. -/

@[expose] public section

section
/-! Merged from `Proof.Argon2.AArch64.SegmentSetupReady`. -/
section
/-! Segment setup needs no previously valid cached block. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (pass lane slice : Nat) (s : State) : Prop where
  parameters : FillContext.Parameters p pass lane slice
  layout : FillKernel.Layout p s
  addressLayout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  write : InRegions s.wr (off (s.gpr .x19) 8) 8
  words : ∃ old, AddressHeader.Words p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  laneLength : s.gpr .x20 = BitVec.ofNat 64 p.laneLen
  segmentLength : s.gpr .x21 = BitVec.ofNat 64 p.segmentLen
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

theorem Ready.of_state {p : Params} {pass lane slice : Nat} {s t : State}
    (h : Ready p pass lane slice s)
    (regs : ∀ r ∈ [Reg.x19, .x24, .x20, .x21, .x22], t.gpr r = s.gpr r)
    (sp : t.sp = s.sp) (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Ready p pass lane slice t := by
  have bp := regs .x19 (by simp)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [mem, bp]
  refine ⟨h.parameters, h.layout.of_preserved bp sp base work rd wr, ?_, ?_, ?_, ?_, ?_,
    (regs .x20 (by simp)).trans h.laneLength, (regs .x21 (by simp)).trans h.segmentLength, ?_⟩
  · constructor
    · rw [rd, wr, bp]; exact h.addressLayout.frameRead
    · rw [wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [rd, wr, bp]; exact h.reads
  · rw [wr, bp]; exact h.write
  · obtain ⟨old, words⟩ := h.words
    refine ⟨old, ?_, (regs .x24 (by simp)).trans words.laneWord,
      (regs .x22 (by simp)).trans words.sliceWord, ?_, ?_, ?_, ?_⟩
    all_goals rw [mem, bp]
    · exact words.passWord
    · exact words.blocksWord
    · exact words.passesWord
    · exact words.variantWord
    · exact words.counterWord
  · rw [base, work]; exact h.matrixWork
  · rw [mem, bp]; exact h.lanesWord

theorem Ready.saved {p : Params} {pass lane slice : Nat} {s t : State}
    (h : Ready p pass lane slice s) (saved : AddressCache.Saved s t) : Ready p pass lane slice t := by
  have bp := congrFun saved.regs Reg.x19
  have sp := saved.sp
  have base : FillKernel.matrix t = FillKernel.matrix s := saved.read 232 (by decide) (by decide)
  refine ⟨h.parameters, h.layout.of_preserved bp sp base saved.work_eq saved.rd saved.wr,
    saved.ready, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [saved.rd, saved.wr, bp]; exact h.reads
  · rw [saved.wr, bp]; exact h.write
  · obtain ⟨old, words⟩ := h.words
    exact ⟨(s.gpr .x8).toNat, saved.words words (by simp)⟩
  · rw [base, saved.work_eq]; exact h.matrixWork
  · rw [saved.regs]; exact h.laneLength
  · rw [saved.regs]; exact h.segmentLength
  · exact (saved.read 184 (by decide) (by decide)).trans h.lanesWord

end VG.Proof.Argon2.AArch64.SegmentSetup
end

/-! Reset the counter while preserving the segment header and matrix allocation. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.SegmentSetup

structure Reset (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  ready : Ready p pass lane slice t
  words : AddressHeader.Words p pass lane slice 0 t
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨off (s.gpr .x19) 8, 8⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem reset_ok (s : State) (p : Params) (pass lane slice : Nat) (h : Ready p pass lane slice s) :
    WP isa reset s (Reset s · p pass lane slice) := by
  unfold reset
  refine WP.seq ((register_ok s .x8 0 (by decide)).mono ?_)
  rintro a ⟨value, keeps⟩
  have next := h.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.sp keeps.mem keeps.rd keeps.wr
  refine (AddressCache.save_ready a next.addressLayout next.write).mono ?_
  intro t saved
  obtain ⟨old, words⟩ := next.words
  have matrixA : FillKernel.matrix a = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .x19 (by decide)]
  have workA : AddressCalls.work a = AddressCalls.work s := by
    unfold AddressCalls.work; rw [keeps.mem, keeps.regs .x19 (by decide)]
  refine ⟨next.saved saved, saved.words words value,
    (saved.read 232 (by decide) (by decide)).trans matrixA, saved.work_eq.trans workA,
    ?_, saved.rd.trans keeps.rd, saved.wr.trans keeps.wr, ?_, saved.sp.trans keeps.sp⟩
  · intro r hr
    have ne : r ∉ [Reg.x8] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (congrFun saved.regs r).trans (keeps.regs r ne)
  · have frame := saved.frame
    rw [keeps.mem, keeps.regs .x19 (by decide)] at frame
    exact frame

end VG.Proof.Argon2.AArch64.SegmentSetup
end

/-! The prepared context covers ordinary and empty first-segment suffixes. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.SegmentSetup

structure Prepared (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  context : FillContext.Ready p pass lane slice (start pass slice) 0 t
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x23 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨off (s.gpr .x19) 8, 8⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem prepare_ok (s : State) (p : Params) (pass lane slice : Nat) (h : Ready p pass lane slice s) :
    WP isa prepare s (Prepared s · p pass lane slice) := by
  unfold prepare
  refine WP.seq ((reset_ok s p pass lane slice h).mono ?_)
  intro a reset
  refine (index_ok a pass slice (reset.ready.reads 0 (by simp)) reset.words.passWord reset.words.sliceWord
    (Nat.lt_trans h.parameters.passBound (by decide))
    (Nat.lt_trans h.parameters.sliceBound (by decide))).mono ?_
  rintro t ⟨value, keeps⟩
  have core := reset.ready.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.sp keeps.mem keeps.rd keeps.wr
  have cacheA : AddressCache.Invariant p pass lane slice 0 a :=
    ⟨reset.ready.addressLayout, reset.ready.reads, reset.ready.write, reset.words, by decide, Or.inl rfl⟩
  have cache := cacheA.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.sp keeps.mem keeps.rd keeps.wr
  have base : FillKernel.matrix t = FillKernel.matrix a := by
    unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .x19 (by decide)]
  have work : AddressCalls.work t = AddressCalls.work a := by
    unfold AddressCalls.work; rw [keeps.mem, keeps.regs .x19 (by decide)]
  refine ⟨⟨core.parameters, core.layout, cache, core.matrixWork,
    ⟨cache.words.laneWord, core.laneLength, core.segmentLength, cache.words.sliceWord, value⟩, core.lanesWord⟩,
    base.trans reset.matrix, work.trans reset.work, ?_, keeps.rd.trans reset.rd,
    keeps.wr.trans reset.wr, ?_, keeps.sp.trans reset.sp⟩
  · intro r hr ne
    have outside : r ∉ [Reg.x3, .x23, .x13, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    exact (keeps.regs r outside).trans (reset.regs r hr)
  · rw [keeps.mem]; exact reset.frame

theorem Prepared.represents {p : Params} {pass lane slice : Nat} {s t : State}
    (ready : Ready p pass lane slice s) (h : Prepared s t p pass lane slice) (blocks : Array Block)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks blocks) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks blocks := by
  rw [h.matrix]
  refine ⟨represented.size, ?_⟩
  intro k hk
  apply Eq.trans _ (represented.block k hk)
  apply FillCompress.block_frame h.frame
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact (ready.layout.matrixFrame.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)).sub_right
    (Offset.sub_base _ (by decide))

end VG.Proof.Argon2.AArch64.SegmentSetup
