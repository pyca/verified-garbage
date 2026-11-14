module

public import VerifiedGarbage.Impl.Argon2.X86_64.SegmentSetup
public import VerifiedGarbage.Impl.Argon2.X86_64.FillSegment
public import VerifiedGarbage.Impl.Argon2.X86_64.FillBlock
import VerifiedGarbage.Proof.Argon2.X86_64.FillKernelSpec
public import VerifiedGarbage.Impl.Argon2.X86_64.RandomSource
public import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Proof.Argon2.X86_64.FillKernelStable
public import VerifiedGarbage.Proof.Argon2.X86_64.AddressCacheMeta
public import VerifiedGarbage.Proof.Argon2.X86_64.AddressCallsStage
import VerifiedGarbage.Proof.Argon2.X86_64.ClearBlock
public import VerifiedGarbage.Proof.Argon2.AddressInput
public import VerifiedGarbage.Proof.Argon2.X86_64.Initialize
import VerifiedGarbage.Proof.Argon2.X86_64.AddressHeaderWords
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressSetup
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Argon2.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Argon2.X86_64.AddressCacheWord
public import VerifiedGarbage.Proof.Argon2.X86_64.FillKernel
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Argon2.Dimensions
public import VerifiedGarbage.Proof.Argon2.FillStep
import VerifiedGarbage.Proof.Argon2.X86_64.DependentWord
public import VerifiedGarbage.Proof.Argon2.Segment

/-! ### `Argon2.X86_64.FillSegment`, which only this module used -/

section

/-! ### `Argon2.X86_64.FillSegmentBody`, which only this module used -/

section

/-! ### `Argon2.X86_64.FillBlock`, which only this module used -/

section

/-! ### `Argon2.X86_64.RandomSource`, which only this module used -/

section

/-! ### `Argon2.X86_64.RandomSourcePrepare`, which only this module used -/

section

/-! ### `Argon2.X86_64.AddressCacheSelect`, which only this module used -/

section

/-! ### `Argon2.X86_64.AddressCallsPrepare`, which only this module used -/

section

/-! Merged from `Proof.Argon2.X86_64.AddressHeaderCorrect`. -/

@[expose] public section

section
/-! Merged from `Proof.Argon2.X86_64.AddressHeader`. -/
section
/-! Compose the seven input fields, preserving frame reads across every write. -/

namespace VG.Proof.Argon2.X86_64.AddressHeader

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressHeader

def value (s : State) (i : Nat) : Addr :=
  if i = 1 then s.gpr .rbx else if i = 2 then s.gpr .r14
  else s.mem.readW (off (s.gpr .rbp) (frameOffset i)) 64

def headerMem (s : State) (p : Addr) : Nat → Mem
  | 0 => s.mem
  | n + 1 => (headerMem s p n).writeW (off p (8 * n)) (value s n)

theorem field_ok (s : State) (i : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) (frameOffset i)) 8)
    (hw : InRegions s.wr (off (s.gpr .rdi) (8 * i)) 8) :
    WP isa (.block (field i)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rdi) (8 * i)) (value s i) ∧
      CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  unfold field value
  by_cases one : i = 1
  · simp only [one, ite_true]
    refine (registerWord_ok s 1 .rbx (one ▸ hw)).mono ?_
    rintro t ⟨mem, regs, rd, wr, mx⟩
    exact ⟨mem, ⟨fun r _ => congrFun regs r, rd, wr⟩, mx⟩
  · simp only [one, ite_false]
    by_cases two : i = 2
    · simp only [two, ite_true]
      refine (registerWord_ok s 2 .r14 (two ▸ hw)).mono ?_
      rintro t ⟨mem, regs, rd, wr, mx⟩
      exact ⟨mem, ⟨fun r _ => congrFun regs r, rd, wr⟩, mx⟩
    · simp only [two, ite_false]
      refine (frameWord_ok s i (frameOffset i) hr hw).mono ?_
      rintro t ⟨mem, regs, rd, wr, mx⟩
      exact ⟨mem, ⟨regs, rd, wr⟩, mx⟩

theorem offset_bound : ∀ i < 7, frameOffset i + 8 ≤ 272 := by decide +kernel

theorem offset_read (s : State) (i : Nat)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8) :
    InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) (frameOffset i)) 8 := by
  apply reads
  unfold frameOffset
  split <;> [simp; skip]
  split <;> [simp; skip]
  split <;> [simp; skip]
  split <;> simp

theorem value_kept {s t : State} (keeps : CopyKeeps s t)
    (hf : Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem)
    (sep : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩)
    (i : Nat) (hi : i < 7) : value t i = value s i := by
  unfold value
  rw [keeps.1 .rbx (by decide), keeps.1 .r14 (by decide), keeps.1 .rbp (by decide)]
  have read : t.mem.readW (off (s.gpr .rbp) (frameOffset i)) 64 =
      s.mem.readW (off (s.gpr .rbp) (frameOffset i)) 64 :=
    hf.readW (r := ⟨s.gpr .rbp, 272⟩)
      (Offset.contains_base _ (offset_bound i hi)
        (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) (offset_bound i hi)) (by decide)))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sep) (by decide)
  rw [read]

theorem prefix_ok (n : Nat) (hn : n ≤ 7) (s : State)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    (write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr)
    (sep : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩) :
    WP isa (.block (fields n)) s fun t =>
      t.mem = headerMem s (s.gpr .rdi) n ∧
      Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, Frame.refl _ _, CopyKeeps.refl s, rfl⟩
  | succ n ih =>
    simp only [fields, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega_using [hn])).mono ?_
    rintro a ⟨mem, frame, keeps, mx⟩
    have dest : a.gpr .rdi = s.gpr .rdi := keeps.1 .rdi (by decide)
    have read : InRegions (a.rd ++ a.wr) (off (a.gpr .rbp) (frameOffset n)) 8 := by
      rw [keeps.2.1, keeps.2.2, keeps.1 .rbp (by decide)]
      exact offset_read s n reads
    have writable : InRegions a.wr (off (a.gpr .rdi) (8 * n)) 8 := by
      rw [dest, keeps.2.2]
      exact write _ _ ⟨⟨s.gpr .rdi, 1024⟩, by simp,
        Offset.contains_base _ (d := 8 * n) (n := 8) (k := 1024) (by omega_using [hn]) (by omega_using [hn])⟩
    refine (field_ok a n read writable).mono ?_
    rintro t ⟨mem', keeps', mx'⟩
    have value' := value_kept keeps frame sep n (by omega_using [hn])
    refine ⟨?_, ?_, keeps.trans keeps', mx'.trans mx⟩
    · rw [mem', dest, value', mem]
      rfl
    · rw [mem', dest]
      exact frame.writeW (r := ⟨s.gpr .rdi, 1024⟩) (by simp) _
        (Offset.contains_base _ (by omega_using [hn]) (by omega_using [hn]))

end VG.Proof.Argon2.X86_64.AddressHeader
end

/-! The prepared input agrees with RFC 9106's seven public address words. -/

namespace VG.Proof.Argon2.X86_64.AddressHeader

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressHeader

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
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    (write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr)
    (sep : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩)
    (zero : blockAt s.mem (s.gpr .rdi) = zeroBlock) :
    WP isa code s fun t => blockAt t.mem (s.gpr .rdi) = input s ∧
      Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  refine (prefix_ok 7 (by decide) s reads write sep).mono ?_
  rintro t ⟨mem, frame, keeps, mx⟩
  exact ⟨by rw [mem]; exact headerMem_block s _ zero, frame, keeps, mx⟩

structure Words (p : Params) (pass lane slice counter : Nat) (s : State) : Prop where
  passWord : s.mem.readW (off (s.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass
  laneWord : s.gpr .rbx = BitVec.ofNat 64 lane
  sliceWord : s.gpr .r14 = BitVec.ofNat 64 slice
  blocksWord : s.mem.readW (off (s.gpr .rbp) 240) 64 = BitVec.ofNat 64 p.blocks
  passesWord : s.mem.readW (off (s.gpr .rbp) 72) 64 = BitVec.ofNat 64 p.passes
  variantWord : s.mem.readW (off (s.gpr .rbp) 112) 64 = BitVec.ofNat 64 p.variant.code
  counterWord : s.mem.readW (off (s.gpr .rbp) 8) 64 = BitVec.ofNat 64 counter

theorem input_spec (p : Params) (pass lane slice counter : Nat) (s : State)
    (h : Words p pass lane slice counter s) :
    input s = Proof.Argon2.addressInput p pass lane slice counter := by
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceEqDiff, input, value, frameOffset,
    h.passWord, h.laneWord, h.sliceWord, h.blocksWord,
    h.passesWord, h.variantWord, h.counterWord, Proof.Argon2.addressInput]

end VG.Proof.Argon2.X86_64.AddressHeader
end

/-! Merged from `Proof.Argon2.X86_64.AddressCallsClear`. -/
section
/-! Clear an address-generation block, retaining the allocation invariants. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCalls

structure Cleared (s t : State) (offset : Nat) : Prop where
  block : blockAt t.mem (off (work s) offset) = zeroBlock
  ready : Ready t
  work_eq : work t = work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨off (work s) offset, 1024⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem clearAt_ok (s : State) (h : Ready s) (offset : Nat) (bound : offset + 1024 ≤ 8192) :
    WP isa (clearAt offset) s (Cleared s · offset) := by
  unfold clearAt
  refine WP.seq ((pointer_ok s offset h.frameRead).mono ?_)
  rintro a ⟨dest, keeps⟩
  rw [displacement_eq offset (by omega_using [bound])] at dest
  have write : Covers [⟨a.gpr .rdi, 1024⟩] a.wr := by
    rw [dest, keeps.wr]; exact work_cover s h offset 1024 bound
  refine (ClearBlock.code_ok a write).mono ?_
  rintro t ⟨zero, frame, tk, mx⟩
  have regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := by
    intro r hr
    have ne : r ≠ .rax ∧ r ≠ .rdi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (tk.1 r ne.1).trans (keeps.regs r (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using ne.2))
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
  obtain ⟨ready, work'⟩ := ready_of_frame h offset bound regs rd wr bigger
  rw [dest] at zero
  exact ⟨zero, ready, work', regs, rd, wr, hf, mx.trans keeps.mxcsr⟩

theorem Cleared.full_frame {s t : State} {offset : Nat} (h : Cleared s t offset)
    (bound : offset + 1024 ≤ 8192) : Frame [⟨work s, 8192⟩] s.mem t.mem := by
  apply h.frame.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨work s, 8192⟩, by simp, Offset.sub_base _ bound⟩

theorem frame_word {s t : State} (h : Ready s) (frame : Frame [⟨work s, 8192⟩] s.mem t.mem)
    (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (s.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 :=
  frame.readW (r := ⟨s.gpr .rbp, 272⟩) (Offset.contains_base _ bound (by omega_using [bound]))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.frameWork) (by decide)

end VG.Proof.Argon2.X86_64.AddressCalls
end

/-! Prepare the independent-address input and zero block from arbitrary scratch. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCalls

structure Stable (s t : State) : Prop where
  ready : Ready t
  work_eq : work t = work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨work s, 8192⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem Stable.trans {s a t : State} (h : Stable s a) (k : Stable a t) : Stable s t := by
  have hf := k.frame
  rw [h.work_eq] at hf
  exact ⟨k.ready, k.work_eq.trans h.work_eq, fun r hr => (k.regs r hr).trans (h.regs r hr),
    k.rd.trans h.rd, k.wr.trans h.wr, h.frame.trans hf, k.mxcsr.trans h.mxcsr⟩

theorem Cleared.stable {s t : State} {offset : Nat} (h : Cleared s t offset)
    (bound : offset + 1024 ≤ 8192) : Stable s t :=
  ⟨h.ready, h.work_eq, h.regs, h.rd, h.wr, h.full_frame bound, h.mxcsr⟩

theorem stable_of_frame {s t : State} (h : Ready s)
    (regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (frame : Frame [⟨work s, 8192⟩] s.mem t.mem) (mx : t.mxcsr = s.mxcsr) : Stable s t := by
  have bp := regs .rbp (by simp [calleeSaved])
  have sp := regs .rsp (by simp [calleeSaved])
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
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8) :
    ∀ d ∈ [0, 8, 72, 112, 240], InRegions (t.rd ++ t.wr) (off (t.gpr .rbp) d) 8 := by
  rw [h.rd, h.wr, h.regs .rbp (by simp [calleeSaved])]
  exact reads

theorem Stable.words {s t : State} {p : Params} {pass lane slice counter : Nat} (ready : Ready s) (h : Stable s t)
    (words : AddressHeader.Words p pass lane slice counter s) :
    AddressHeader.Words p pass lane slice counter t := by
  have bp := h.regs .rbp (by simp [calleeSaved])
  have read (d : Nat) (hd : d + 8 ≤ 272) :
      t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
    rw [bp]; exact frame_word ready h.frame d hd
  exact ⟨(read 0 (by decide)).trans words.passWord,
    (h.regs .rbx (by simp [calleeSaved])).trans words.laneWord,
    (h.regs .r14 (by simp [calleeSaved])).trans words.sliceWord,
    (read 240 (by decide)).trans words.blocksWord,
    (read 72 (by decide)).trans words.passesWord,
    (read 112 (by decide)).trans words.variantWord,
    (read 8 (by decide)).trans words.counterWord⟩

theorem pointer_stable {s a : State} (h : Ready s)
    (k : Divide.Keeps [.rdi] s a) : Stable s a := by
  apply stable_of_frame h _ k.rd k.wr _ k.mxcsr
  · intro r hr
    apply k.regs
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [k.mem]; exact Frame.refl _ _

theorem Stable.input {s t : State} (ready : Ready s) (h : Stable s t) :
    AddressHeader.input t = AddressHeader.input s := by
  have value (i : Nat) (hi : i < 7) : AddressHeader.value t i = AddressHeader.value s i := by
    unfold AddressHeader.value
    rw [h.regs .rbx (by simp [calleeSaved]), h.regs .r14 (by simp [calleeSaved]),
      h.regs .rbp (by simp [calleeSaved]),
      frame_word ready h.frame (Impl.Argon2.X86_64.AddressHeader.frameOffset i)
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
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
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
  refine WP.seq ((pointer_ok b 5120 zeroClear.ready.frameRead).mono ?_)
  rintro c ⟨dest, keeps⟩
  rw [displacement_eq 5120 (by decide)] at dest
  have stableC := stableB.trans (pointer_stable zeroClear.ready keeps)
  have dest' : c.gpr .rdi = off (work s) 5120 := by rw [dest, stableB.work_eq]
  have write : Covers [⟨c.gpr .rdi, 1024⟩] c.wr := by
    rw [dest, keeps.wr]; exact work_cover b zeroClear.ready 5120 1024 (by decide)
  have sep : (⟨c.gpr .rbp, 272⟩ : Region).Disjoint ⟨c.gpr .rdi, 1024⟩ := by
    rw [dest', stableC.regs .rbp (by simp [calleeSaved])]
    exact h.frameWork.sub_right (Offset.sub_base _ (by decide))
  have zero : blockAt c.mem (c.gpr .rdi) = zeroBlock := by rw [dest', keeps.mem]; exact inputZero
  refine (AddressHeader.code_ok c (stableC.reads reads) write sep zero).mono ?_
  rintro t ⟨input, frame, tk, mx⟩
  have regs : ∀ r ∈ calleeSaved, t.gpr r = c.gpr r := by
    intro r hr
    apply tk.1
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
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
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    (words : AddressHeader.Words p pass lane slice counter s) :
    WP isa prepare s (Prepared s · p pass lane slice counter) :=
  (prepare_layout_ok s h reads).mono (fun _ k =>
    ⟨k.stable, k.zero, k.input.trans (AddressHeader.input_spec p pass lane slice counter s words)⟩)

end VG.Proof.Argon2.X86_64.AddressCalls

end

end

/-! ### `Argon2.X86_64.AddressCalls`, which only this module used -/

section

/-! Both compression calls produce exactly the reviewed independent-address block. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCalls

def writes (s : State) : List Region := [⟨work s, 8192⟩, below (s.gpr .rsp) 8]

structure Generated (s t : State) (p : Params) (pass lane slice counter : Nat) : Prop where
  block : blockAt t.mem (off (work s) 6144) = addressBlock p pass lane slice counter
  ready : Ready t
  work : work t = work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
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

theorem calls_ok [CompressImpl] (p : Params) (pass lane slice counter : Nat) (s : State) (h : Ready s)
    (zero : blockAt s.mem (off (work s) 7168) = zeroBlock)
    (input : blockAt s.mem (off (work s) 5120) = Proof.Argon2.addressInput p pass lane slice counter) :
    WP isa calls s fun t => Generated s t p pass lane slice counter ∧ ctl t.mxcsr = ctl s.mxcsr := by
  unfold calls
  refine WP.seq ((stage_ok s h 7168 5120 4096 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).mono ?_)
  rintro a ⟨first, mx1⟩
  refine (stage_ok a first.ready 7168 4096 6144 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).mono ?_
  rintro t ⟨second, mx2⟩
  refine ⟨⟨?_, second.ready, second.work.trans first.work,
    fun r hr => (second.regs r hr).trans (first.regs r hr),
    second.rd.trans first.rd, second.wr.trans first.wr, ?_⟩, by rw [mx2, mx1]⟩
  · have result := second.result
    rw [first.work, zero_preserved h first.frame, zero, first.result, zero, input] at result
    rw [Proof.Argon2.addressBlock_eq]
    exact result
  · have next := stage_frame_full (by decide) second.frame
    simp only [writes, first.work, first.regs .rsp (by simp [calleeSaved])] at next
    exact (stage_frame_full (by decide) first.frame).trans next

end VG.Proof.Argon2.X86_64.AddressCalls

end

end


/-! Merged from `Proof.Argon2.X86_64.AddressGeneration`. -/

@[expose] public section

section
/-! Complete independent-address generation against the reviewed algorithm. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCalls

theorem code_ok [CompressImpl] (p : Params) (pass lane slice counter : Nat) (s : State) (h : Ready s)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    (words : AddressHeader.Words p pass lane slice counter s) :
    WP isa code s fun t => Generated s t p pass lane slice counter ∧ ctl t.mxcsr = ctl s.mxcsr := by
  unfold code
  refine WP.seq ((prepare_ok p pass lane slice counter s h reads words).mono ?_)
  intro a prepared
  have zero : blockAt a.mem (off (work a) 7168) = zeroBlock := by
    rw [prepared.stable.work_eq]; exact prepared.zero
  have input : blockAt a.mem (off (work a) 5120) = Proof.Argon2.addressInput p pass lane slice counter := by
    rw [prepared.stable.work_eq]; exact prepared.input
  refine (calls_ok p pass lane slice counter a prepared.stable.ready zero input).mono ?_
  rintro t ⟨generated, mx⟩
  have frame := generated.frame
  rw [writes, prepared.stable.work_eq, prepared.stable.regs .rsp (by simp [calleeSaved])] at frame
  have firstFrame : Frame (writes s) s.mem a.mem :=
    prepared.stable.frame.mono (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      simp [writes])
  refine ⟨⟨?_, generated.ready, generated.work.trans prepared.stable.work_eq,
    fun r hr => (generated.regs r hr).trans (prepared.stable.regs r hr),
    generated.rd.trans prepared.stable.rd, generated.wr.trans prepared.stable.wr,
    firstFrame.trans frame⟩, mx.trans (ctl_eq_of prepared.stable.mxcsr)⟩
  have block := generated.block
  rw [prepared.stable.work_eq] at block
  exact block

end VG.Proof.Argon2.X86_64.AddressCalls
end

/-! Merged from `Proof.Argon2.X86_64.AddressCacheSave`. -/
section
/-! Save the public cache counter without disturbing scratch or header fields. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCache

theorem save_ok (s : State) (hw : InRegions s.wr (off (s.gpr .rbp) 8) 8) :
    WP isa (.block save) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rbp) 8) (s.gpr .rax) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [save, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    ea_at, hw, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

structure Saved (s t : State) : Prop where
  mem : t.mem = s.mem.writeW (off (s.gpr .rbp) 8) (s.gpr .rax)
  regs : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  ready : AddressCalls.Ready t
  work_eq : AddressCalls.work t = AddressCalls.work s
  frame : Frame [⟨off (s.gpr .rbp) 8, 8⟩] s.mem t.mem

theorem save_ready (s : State) (h : AddressCalls.Ready s)
    (hw : InRegions s.wr (off (s.gpr .rbp) 8) 8) : WP isa (.block save) s (Saved s) := by
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
    · rw [regs]; exact h.frameStack
    · rw [regs, work']; exact h.stackWork
  refine ⟨mem, regs, rd, wr, mx, ready, work', ?_⟩
  rw [mem]
  exact (Frame.refl _ _).writeW (r := ⟨off (s.gpr .rbp) 8, 8⟩) (by simp) _
    (Region.contains_self _ _)

theorem Saved.read {s t : State} (h : Saved s t) (d : Nat)
    (hd : d + 8 ≤ 8 ∨ 16 ≤ d) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [h.regs, h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ hd (by omega_using [bound]) (by decide)) (by decide)

theorem Saved.words {s t : State} {p : Params} {pass lane slice old counter : Nat}
    (h : Saved s t) (words : AddressHeader.Words p pass lane slice old s)
    (value : s.gpr .rax = BitVec.ofNat 64 counter) :
    AddressHeader.Words p pass lane slice counter t := by
  refine ⟨(h.read 0 (by decide) (by decide)).trans words.passWord,
    ?_, ?_, (h.read 240 (by decide) (by decide)).trans words.blocksWord,
    (h.read 72 (by decide) (by decide)).trans words.passesWord,
    (h.read 112 (by decide) (by decide)).trans words.variantWord, ?_⟩
  · rw [h.regs]; exact words.laneWord
  · rw [h.regs]; exact words.sliceWord
  · rw [h.regs, h.mem, Mem.readW_writeW_self64, value]

end VG.Proof.Argon2.X86_64.AddressCache
end

/-! Regenerate only when the public one-based block counter changes. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCache

def wanted (s : State) : Nat := (s.gpr .r15).toNat / 128 + 1

def writes (s : State) : List Region :=
  [⟨AddressCalls.work s, 8192⟩, below (s.gpr .rsp) 8, ⟨off (s.gpr .rbp) 8, 8⟩]

structure Ready (p : Params) (pass lane slice old : Nat) (s : State) : Prop where
  layout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  write : InRegions s.wr (off (s.gpr .rbp) 8) 8
  words : AddressHeader.Words p pass lane slice old s
  cached : counter (s.gpr .r15) = s.mem.readW (off (s.gpr .rbp) 8) 64 →
    blockAt s.mem (off (AddressCalls.work s) 6144) = addressBlock p pass lane slice (wanted s)

structure Selected (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  block : blockAt t.mem (off (AddressCalls.work s) 6144) = addressBlock p pass lane slice (wanted s)
  layout : AddressCalls.Ready t
  work_eq : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr
  counterWord : t.mem.readW (off (t.gpr .rbp) 8) 64 = counter (s.gpr .r15)

theorem check_stable {s a : State} (h : AddressCalls.Ready s) (k : Divide.Keeps [.rax] s a) :
    AddressCalls.Stable s a := by
  apply AddressCalls.stable_of_frame h _ k.rd k.wr _ k.mxcsr
  · intro r hr
    apply k.regs
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [k.mem]; exact Frame.refl _ _

theorem selected_ok [CompressImpl] (p : Params) (pass lane slice old : Nat) (s : State)
    (h : Ready p pass lane slice old s) :
    WP isa select s (Selected s · p pass lane slice) := by
  unfold select
  refine WP.seq ((check_ok s (h.reads 8 (by simp))).mono ?_)
  rintro a ⟨value, flag, keeps⟩
  have stableA := check_stable h.layout keeps
  refine WP.ite (decide (counter (s.gpr .r15) = s.mem.readW (off (s.gpr .rbp) 8) 64))
    (by simp only [eval, flag]) ?_ ?_
  · intro same
    have equal := of_decide_eq_true same
    apply WP.of_runBlock
    simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
    refine ⟨?_, stableA.ready, stableA.work_eq, stableA.regs, keeps.rd, keeps.wr,
      ?_, ctl_eq_of keeps.mxcsr, ?_⟩
    · rw [keeps.mem]; exact h.cached equal
    · rw [keeps.mem]; exact Frame.refl _ _
    · rw [stableA.regs .rbp (by simp [calleeSaved]), keeps.mem]; exact equal.symm
  · intro _
    have write : InRegions a.wr (off (a.gpr .rbp) 8) 8 := by
      rw [keeps.wr, stableA.regs .rbp (by simp [calleeSaved])]; exact h.write
    refine WP.seq ((save_ready a stableA.ready write).mono ?_)
    intro b saved
    have words : AddressHeader.Words p pass lane slice (wanted s) b := by
      apply saved.words (stableA.words h.layout h.words)
      rw [value, counter_nat]; rfl
    have reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (b.rd ++ b.wr) (off (b.gpr .rbp) d) 8 := by
      rw [saved.rd, saved.wr, saved.regs]; exact stableA.reads h.reads
    refine (AddressCalls.code_ok p pass lane slice (wanted s) b saved.ready reads words).mono ?_
    rintro t ⟨generated, mx⟩
    have workB : AddressCalls.work b = AddressCalls.work s := saved.work_eq.trans stableA.work_eq
    have regsB (r : Reg) (hr : r ∈ calleeSaved) : b.gpr r = s.gpr r :=
      (congrFun saved.regs r).trans (stableA.regs r hr)
    have regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r :=
      fun r hr => (generated.regs r hr).trans (regsB r hr)
    have firstFrame : Frame (writes s) s.mem b.mem := by
      have frame := saved.frame
      rw [stableA.regs .rbp (by simp [calleeSaved]), keeps.mem] at frame
      exact frame.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp [writes])
    have finalFrame : Frame (writes s) b.mem t.mem := by
      have frame := generated.frame
      rw [AddressCalls.writes, workB, regsB .rsp (by simp [calleeSaved])] at frame
      exact frame.mono (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp [writes])
    refine ⟨?_, generated.ready, generated.work.trans workB, regs,
      generated.rd.trans (saved.rd.trans keeps.rd), generated.wr.trans (saved.wr.trans keeps.wr),
      firstFrame.trans finalFrame, mx.trans (ctl_eq_of (saved.mxcsr.trans keeps.mxcsr)), ?_⟩
    · have block := generated.block
      rw [workB] at block
      exact block
    · have preserved : t.mem.readW (off (b.gpr .rbp) 8) 64 = b.mem.readW (off (b.gpr .rbp) 8) 64 :=
        generated.frame.readW (r := ⟨b.gpr .rbp, 272⟩)
          (Offset.contains_base _ (by decide) (by decide)) (by
            intro r hr
            simp only [AddressCalls.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact saved.ready.frameWork
            · exact saved.ready.frameStack) (by decide)
      rw [generated.regs .rbp (by simp [calleeSaved]), preserved, saved.regs, saved.mem,
        Mem.readW_writeW_self64, value]

end VG.Proof.Argon2.X86_64.AddressCache

end

end


/-! Merged from `Proof.Argon2.X86_64.FillKernelInvariant`. -/

@[expose] public section

section
/-! Each active-cell update retains the frame and matrix allocation invariant. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

theorem Done.frame_word {s t : State} {p : Params} {pass lane slice index : Nat}
    (h : Ready p pass lane slice index s) (done : Done s t p pass lane slice index)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 16 ∨ 24 ≤ d) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [done.regs .rbp (by simp [calleeSaved])]
  have sub : Region.Sub ⟨off (s.gpr .rbp) d, 8⟩ ⟨s.gpr .rbp, 272⟩ := Offset.sub_base _ bound
  have currentSub : Region.Sub ⟨current s p lane slice index, 1024⟩ ⟨matrix s, p.blocks * 1024⟩ :=
    cell_sub p _ h.bounds.lanesPositive h.bounds.laneBound
      (Proof.Argon2.column_lt p h.bounds.lanesPositive h.bounds.sliceBound h.bounds.indexBound)
  exact done.frame.readW (r := ⟨off (s.gpr .rbp) d, 8⟩) (Region.contains_self _ _) (by
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
  have bp := done.regs .rbp (by simp [calleeSaved])
  have sp := done.regs .rsp (by simp [calleeSaved])
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
  · exact ⟨(done.regs .rbx (by simp [calleeSaved])).trans h.position.current,
      (done.regs .r12 (by simp [calleeSaved])).trans h.position.laneLength,
      (done.regs .r13 (by simp [calleeSaved])).trans h.position.segmentLength,
      (done.regs .r14 (by simp [calleeSaved])).trans h.position.slice,
      (done.regs .r15 (by simp [calleeSaved])).trans h.position.index⟩

end VG.Proof.Argon2.X86_64.FillKernel
end

/-! Merged from `Proof.Argon2.X86_64.AddressModeSteps`. -/
section
/-! Short mask computations for the public addressing-mode predicate. -/

namespace VG.Proof.Argon2.X86_64.AddressMode

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressMode

theorem zero_nat (x : Addr) : x.toNat < 1 ↔ x = 0#64 := by
  constructor
  · intro h; exact BitVec.eq_of_toNat_eq (Nat.lt_one_iff.mp h)
  · intro h; rw [h]; decide

theorem xor_nat (x y : Addr) : (x ^^^ y).toNat < 1 ↔ x = y := by
  rw [zero_nat, BitVec.xor_eq_zero_iff]

theorem kind_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 112) 8) :
    WP isa (.block kind) s fun t =>
      t.gpr .r10 = Divide.mask (decide (s.mem.readW (off (s.gpr .rbp) 112) 64 = 1)) ∧
      t.gpr .r8 = Divide.mask (decide (s.mem.readW (off (s.gpr .rbp) 112) 64 = 2)) ∧
      Divide.Keeps [.rax, .r10, .r8] s t := by
  apply WP.of_runBlock
  simp only [kind, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, hr, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags, reduceCtorEq, ite_true, ite_false,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    show BitVec.signExtend 64 (2 : BitVec 32) = (2 : Addr) from rfl,
    Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', Divide.sbb_mask, show (1 : Addr).toNat = 1 from rfl, xor_nat]
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem pass_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8) :
    WP isa (.block pass) s fun t =>
      t.gpr .r9 = Divide.mask (decide (s.mem.readW (off (s.gpr .rbp) 0) 64 = 0#64)) ∧
      Divide.Keeps [.r9] s t := by
  apply WP.of_runBlock
  simp only [pass, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, hr, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags, ite_true,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', Divide.sbb_mask, show (1 : Addr).toNat = 1 from rfl, zero_nat]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  all_goals rfl

theorem slice_ok (s : State) : WP isa (.block slice) s fun t =>
    t.gpr .r10 = (s.gpr .r10 ||| ((s.gpr .r8 &&& s.gpr .r9) &&&
      Divide.mask (decide ((s.gpr .r14).toNat < 2)))) &&& 1 ∧
    Divide.Keeps [.r8, .r11, .r10] s t := by
  apply WP.of_runBlock
  simp only [slice, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
    reduceCtorEq, ite_true, ite_false,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    show BitVec.signExtend 64 (2 : BitVec 32) = (2 : Addr) from rfl,
    Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', Divide.sbb_mask, show (2 : Addr).toNat = 2 from rfl]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.X86_64.AddressMode
end

/-! Merged from `Proof.Argon2.X86_64.AddressMode`. -/
section
/-! The segment mode is exactly the reviewed Argon2d/i/id addressing predicate. -/

namespace VG.Proof.Argon2.X86_64.AddressMode

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressMode

def value (s : State) : Addr :=
  let kind := s.mem.readW (off (s.gpr .rbp) 112) 64
  let pass := s.mem.readW (off (s.gpr .rbp) 0) 64
  (Divide.mask (decide (kind = 1)) ||| ((Divide.mask (decide (kind = 2)) &&&
    Divide.mask (decide (pass = 0#64))) &&& Divide.mask (decide ((s.gpr .r14).toNat < 2)))) &&& 1

def changed : List Reg := [.rax, .r8, .r9, .r10, .r11]

theorem code_ok (s : State)
    (kindRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 112) 8)
    (passRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8) :
    WP isa code s fun t => t.gpr .r10 = value s ∧ Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((kind_ok s kindRead).mono ?_)
  rintro a ⟨i, id, ka⟩
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .rbp) 0) 8 := by
    rw [ka.rd, ka.wr, ka.regs .rbp (by decide)]; exact passRead
  refine WP.seq ((pass_ok a read).mono ?_)
  rintro b ⟨zero, kb⟩
  refine (slice_ok b).mono ?_
  rintro t ⟨result, kt⟩
  refine ⟨?_, ((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kt.mono (by decide))⟩
  rw [result, kb.regs .r10 (by decide), i, kb.regs .r8 (by decide), id, zero,
    ka.mem, ka.regs .rbp (by decide), kb.regs .r14 (by decide), ka.regs .r14 (by decide)]
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
    (kindWord : s.mem.readW (off (s.gpr .rbp) 112) 64 = BitVec.ofNat 64 p.variant.code)
    (passWord : s.mem.readW (off (s.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass)
    (sliceWord : s.gpr .r14 = BitVec.ofNat 64 slice)
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
    (kindRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 112) 8)
    (passRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8)
    (kindWord : s.mem.readW (off (s.gpr .rbp) 112) 64 = BitVec.ofNat 64 p.variant.code)
    (passWord : s.mem.readW (off (s.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass)
    (sliceWord : s.gpr .r14 = BitVec.ofNat 64 slice)
    (passBound : pass < 2 ^ 64) (sliceBound : slice < 2 ^ 64) :
    WP isa code s fun t => t.gpr .r10 =
      (BitVec.ofBool (Spec.Argon2.independent p pass slice)).setWidth 64 ∧ Divide.Keeps changed s t :=
  (code_ok s kindRead passRead).mono (fun _ h =>
    ⟨h.1.trans (value_spec s p pass slice kindWord passWord sliceWord passBound sliceBound), h.2⟩)

end VG.Proof.Argon2.X86_64.AddressMode
end

/-! Merged from `Proof.Argon2.X86_64.AddressCacheState`. -/
section
/-! Merged from `Proof.Argon2.X86_64.AddressCache`. -/
section
/-! Complete cached random-word selection against RFC 9106's address block. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCache

structure Done (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  selected : Selected s t p pass lane slice
  random : t.gpr .rdi =
    (addressBlock p pass lane slice (wanted s))[(s.gpr .r15).toNat % 128]'(Nat.mod_lt _ (by decide))

theorem code_ok [CompressImpl] (p : Params) (pass lane slice old : Nat) (s : State)
    (h : Ready p pass lane slice old s) :
    WP isa code s (Done s · p pass lane slice) := by
  unfold code
  refine WP.seq ((selected_ok p pass lane slice old s h).mono ?_)
  intro a selected
  refine (word_ok a selected.layout).mono ?_
  rintro t ⟨random, keeps⟩
  have regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := by
    intro r hr
    have ne : r ∉ [Reg.rcx, .rax, .rdi] := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (keeps.regs r ne).trans (selected.regs r hr)
  have bp := keeps.regs .rbp (by decide)
  have sp := keeps.regs .rsp (by decide)
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
    (ctl_eq_of keeps.mxcsr).trans selected.mxcsr, ?_⟩, ?_⟩
  · rw [keeps.mem]; exact selected.block
  · rw [keeps.mem]; exact selected.frame
  · rw [bp, keeps.mem]; exact selected.counterWord
  · rw [selected.work_eq, selected.regs .r15 (by simp [calleeSaved]), selected.block] at random
    exact random

end VG.Proof.Argon2.X86_64.AddressCache
end

/-! Retain the filling header and allocation across independent-address regeneration. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2

theorem Selected.frame_word {s t : State} {p : Params} {pass lane slice : Nat}
    (layout : AddressCalls.Ready s) (h : Selected s t p pass lane slice)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 8 ∨ 16 ≤ d) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [h.regs .rbp (by simp [calleeSaved])]
  have sub : Region.Sub ⟨off (s.gpr .rbp) d, 8⟩ ⟨s.gpr .rbp, 272⟩ := Offset.sub_base _ bound
  exact h.frame.readW (r := ⟨off (s.gpr .rbp) d, 8⟩) (Region.contains_self _ _) (by
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
    (h.regs .rbx (by simp [calleeSaved])).trans ready.words.laneWord,
    (h.regs .r14 (by simp [calleeSaved])).trans ready.words.sliceWord,
    (h.frame_word ready.layout 240 (by decide) (by decide)).trans ready.words.blocksWord,
    (h.frame_word ready.layout 72 (by decide) (by decide)).trans ready.words.passesWord,
    (h.frame_word ready.layout 112 (by decide) (by decide)).trans ready.words.variantWord,
    h.counterWord.trans (counter_nat _)⟩

end VG.Proof.Argon2.X86_64.AddressCache
end

/-! Merged from `Proof.Argon2.X86_64.AddressCacheMatrix`. -/
section
/-! Independent-address generation leaves every matrix cell intact. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2

theorem Selected.filling_ready {s t : State} {p : Params} {pass lane slice index : Nat}
    (cacheLayout : AddressCalls.Ready s) (h : FillKernel.Ready p pass lane slice index s)
    (done : Selected s t p pass lane slice) : FillKernel.Ready p pass lane slice index t := by
  have bp := done.regs .rbp (by simp [calleeSaved])
  have sp := done.regs .rsp (by simp [calleeSaved])
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
  · exact ⟨(done.regs .rbx (by simp [calleeSaved])).trans h.position.current,
      (done.regs .r12 (by simp [calleeSaved])).trans h.position.laneLength,
      (done.regs .r13 (by simp [calleeSaved])).trans h.position.segmentLength,
      (done.regs .r14 (by simp [calleeSaved])).trans h.position.slice,
      (done.regs .r15 (by simp [calleeSaved])).trans h.position.index⟩

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

end VG.Proof.Argon2.X86_64.AddressCache
end

/-! Merged from `Proof.Argon2.X86_64.AddressCacheInvariant`. -/
section
/-! Cache validity does not depend on the current index, so advancing an index
retains it. Counter zero requires no cached contents; every other counter
identifies its specified independent-address block.
-/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2

structure Invariant (p : Params) (pass lane slice old : Nat) (s : State) : Prop where
  layout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  write : InRegions s.wr (off (s.gpr .rbp) 8) 8
  words : AddressHeader.Words p pass lane slice old s
  bound : old < 2 ^ 64
  cached : old = 0 ∨ blockAt s.mem (off (AddressCalls.work s) 6144) = addressBlock p pass lane slice old

theorem wanted_bound (s : State) : wanted s < 2 ^ 64 := by
  unfold wanted
  have := (s.gpr .r15).isLt
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
  have bp := h.regs .rbp (by simp [calleeSaved])
  refine ⟨h.layout, ?_, ?_, h.words ready, wanted_bound s, Or.inr ?_⟩
  · rw [h.rd, h.wr, bp]; exact ready.reads
  · rw [h.wr, bp]; exact ready.write
  · rw [h.work_eq]; exact h.block

theorem Invariant.of_state {p : Params} {pass lane slice old : Nat} {s t : State}
    (h : Invariant p pass lane slice old s)
    (regs : ∀ r ∈ [Reg.rsp, .rbp, .rbx, .r14], t.gpr r = s.gpr r)
    (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
    Invariant p pass lane slice old t := by
  have bp := regs .rbp (by simp)
  have sp := regs .rsp (by simp)
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
      (regs .rbx (by simp)).trans h.words.laneWord,
      (regs .r14 (by simp)).trans h.words.sliceWord,
      by rw [mem, bp]; exact h.words.blocksWord,
      by rw [mem, bp]; exact h.words.passesWord,
      by rw [mem, bp]; exact h.words.variantWord,
      by rw [mem, bp]; exact h.words.counterWord⟩
  · rw [mem, work]; exact h.cached

theorem Invariant.of_keeps {p : Params} {pass lane slice old : Nat} {s t : State}
    (h : Invariant p pass lane slice old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    Invariant p pass lane slice old t := by
  apply h.of_state _ k.mem k.rd k.wr
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact k.regs _ (by decide)

end VG.Proof.Argon2.X86_64.AddressCache
end

/-! Retain the source invariants while selecting the public addressing mode. -/

namespace VG.Proof.Argon2.X86_64.RandomSource

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.RandomSource

structure Ready (p : Params) (pass lane slice index old : Nat) (s : State) : Prop where
  filling : FillKernel.Ready p pass lane slice index s
  cache : AddressCache.Invariant p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩

theorem Ready.of_keeps {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : Ready p pass lane slice index old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    Ready p pass lane slice index old t := by
  refine ⟨h.filling.of_keeps k, h.cache.of_keeps k, ?_⟩
  have matrix : FillKernel.matrix t = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [k.mem, k.regs .rbp (by decide)]
  have work : AddressCalls.work t = AddressCalls.work s := by
    unfold AddressCalls.work; rw [k.mem, k.regs .rbp (by decide)]
  rw [matrix, work]; exact h.matrixWork

theorem test_ok (s : State) : WP isa (.block test) s fun t =>
    t.zf = decide (s.gpr .r10 = 0#64) ∧ Divide.Keeps [] s t := by
  apply WP.of_runBlock
  simp only [test, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, show BitVec.signExtend 64 (0 : BitVec 32) = (0 : Addr) from rfl,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · change (s.gpr .r10 - 0#64 == 0#64) = decide (s.gpr .r10 = 0#64)
    rw [BitVec.sub_zero]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro r _; exact congrFun (RegUpd.gpr_arithFlags _ _ _ _) r
  all_goals rfl

theorem bool_zero : ∀ b : Bool, decide ((BitVec.ofBool b).setWidth 64 = 0#64) = !b := by
  decide +kernel

theorem prepare_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : Ready p pass lane slice index old s) : WP isa prepare s fun t =>
      t.zf = !independent p pass slice ∧ Divide.Keeps ReferenceMap.changed s t := by
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

end VG.Proof.Argon2.X86_64.RandomSource

end

end


/-! Merged from `Proof.Argon2.X86_64.DependentWordState`. -/

@[expose] public section

section
/-! The dependent source hands the filling step its random word and unchanged matrix. -/

namespace VG.Proof.Argon2.X86_64.DependentWord

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.DependentWord

theorem state_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (dependent : independent p pass slice = false) : WP isa code s fun t =>
      t.gpr .rdi = Proof.Argon2.FillStep.random p pass lane slice index state.memory ∧
      FillKernel.Ready p pass lane slice index t ∧
      Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory ∧
      Divide.Keeps ReferenceMap.changed s t := by
  refine (code_spec_ok s p pass lane slice index h state represented dependent).mono ?_
  rintro t ⟨random, keeps⟩
  refine ⟨random, h.of_keeps keeps, ?_, keeps⟩
  have base : FillKernel.matrix t = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .rbp (by decide)]
  rw [keeps.mem, base]; exact represented

end VG.Proof.Argon2.X86_64.DependentWord
end

/-! Both random sources satisfy the same filling-step postcondition. -/

namespace VG.Proof.Argon2.X86_64.RandomSource

open VG VG.X86_64 VG.Spec.Argon2

def writes (s : State) : List Region := AddressCache.writes s

structure Done (s t : State) (p : Params) (pass lane slice index : Nat) (state : FillState) : Prop where
  random : t.gpr .rdi = Proof.Argon2.FillStep.random p pass lane slice index state.memory
  ready : ∃ old, Ready p pass lane slice index old t
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr

theorem Ready.index_nat {p : Params} {pass lane slice index old : Nat} {s : State}
    (h : Ready p pass lane slice index old s) : (s.gpr .r15).toNat = index := by
  rw [h.filling.position.index, ReferenceMap.word_nat index h.filling.bounds.index_bound64]

theorem independent_ok [CompressImpl] (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (mode : independent p pass slice = true) :
    WP isa Impl.Argon2.X86_64.AddressCache.code s (Done s · p pass lane slice index state) := by
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
    done.selected.regs, done.selected.rd, done.selected.wr, done.selected.frame, done.selected.mxcsr⟩
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
    WP isa Impl.Argon2.X86_64.DependentWord.code s (Done s · p pass lane slice index state) := by
  refine (DependentWord.state_ok s p pass lane slice index h.filling state represented mode).mono ?_
  rintro t ⟨random, _, matrix, keeps⟩
  refine ⟨random, ⟨old, h.of_keeps keeps⟩, matrix, ?_, keeps.rd, keeps.wr, ?_, ctl_eq_of keeps.mxcsr⟩
  · intro r hr
    apply keeps.regs
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [keeps.mem]; exact Frame.refl _ _

theorem code_ok [CompressImpl] (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.RandomSource.code s (Done s · p pass lane slice index state) := by
  unfold Impl.Argon2.X86_64.RandomSource.code
  refine WP.seq ((prepare_ok s p pass lane slice index old h).mono ?_)
  rintro a ⟨flag, keeps⟩
  have next := h.of_keeps keeps
  have representedA : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks state.memory := by
    have base : FillKernel.matrix a = FillKernel.matrix s := by
      unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .rbp (by decide)]
    rw [base, keeps.mem]; exact represented
  have finish {t : State} (done : Done a t p pass lane slice index state) :
      Done s t p pass lane slice index state := by
    refine ⟨done.random, done.ready, done.represented, ?_, done.rd.trans keeps.rd,
      done.wr.trans keeps.wr, ?_, done.mxcsr.trans (ctl_eq_of keeps.mxcsr)⟩
    · intro r hr
      have ne : r ∉ ReferenceMap.changed := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (done.regs r hr).trans (keeps.regs r ne)
    · have frame := done.frame
      unfold writes AddressCache.writes AddressCalls.work at frame ⊢
      rw [keeps.mem, keeps.regs .rbp (by decide), keeps.regs .rsp (by decide)] at frame
      exact frame
  refine WP.ite (!independent p pass slice) (by simp only [eval, flag]) ?_ ?_
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

end VG.Proof.Argon2.X86_64.RandomSource

end

end


/-! Merged from `Proof.Argon2.X86_64.RandomSourceState`. -/

@[expose] public section

section
/-! Frame words and public allocation pointers survive random-word dispatch. -/

namespace VG.Proof.Argon2.X86_64.RandomSource

open VG VG.X86_64 VG.Spec.Argon2

theorem Done.frame_word {s t : State} {p : Params} {pass lane slice index old : Nat} {state : FillState}
    (h : Ready p pass lane slice index old s) (done : Done s t p pass lane slice index state)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 8 ∨ 16 ≤ d) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [done.regs .rbp (by simp [calleeSaved])]
  have sub : Region.Sub ⟨off (s.gpr .rbp) d, 8⟩ ⟨s.gpr .rbp, 272⟩ := Offset.sub_base _ bound
  exact done.frame.readW (r := ⟨off (s.gpr .rbp) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [writes, AddressCache.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.cache.layout.frameWork.sub_left sub
    · exact h.cache.layout.frameStack.sub_left sub
    · exact Offset.disjoint _ separate (by omega_using [bound]) (by decide)) (by decide)

end VG.Proof.Argon2.X86_64.RandomSource
end

/-! Merged from `Proof.Argon2.X86_64.FillCacheInvariant`. -/
section
/-! The cell update does not disturb the cached independent-address block. -/

namespace VG.Proof.Argon2.X86_64.RandomSource

open VG VG.X86_64 VG.Spec.Argon2

theorem Ready.after_fill {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : Ready p pass lane slice index old s) (done : FillKernel.Done s t p pass lane slice index) :
    Ready p pass lane slice index old t := by
  have bp := done.regs .rbp (by simp [calleeSaved])
  have sp := done.regs .rsp (by simp [calleeSaved])
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
        (done.regs .rbx (by simp [calleeSaved])).trans h.cache.words.laneWord,
        (done.regs .r14 (by simp [calleeSaved])).trans h.cache.words.sliceWord,
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

end VG.Proof.Argon2.X86_64.RandomSource
end

/-! Merged from `Proof.Argon2.X86_64.FillBlockFrame`. -/
section
/-! Compose scratch writes with a matrix-cell write inside the derive allocation. -/

namespace VG.Proof.Argon2.X86_64.FillBlock

open VG VG.X86_64 VG.Spec.Argon2

def writes (s : State) (p : Params) : List Region :=
  [⟨FillKernel.matrix s, p.blocks * 1024⟩, ⟨AddressCalls.work s, 8192⟩,
    below (s.gpr .rsp) 8, ⟨off (s.gpr .rbp) 8, 16⟩]

theorem source_frame {s t : State} {p : Params} {pass lane slice index : Nat} {state : FillState}
    (done : RandomSource.Done s t p pass lane slice index state) : Frame (writes s p) s.mem t.mem := by
  apply done.frame.sub
  intro r hr
  simp only [RandomSource.writes, AddressCache.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨⟨off (s.gpr .rbp) 8, 16⟩, by simp [writes], Region.sub_prefix (by decide)⟩

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

end VG.Proof.Argon2.X86_64.FillBlock
end

/-! Complete active filling cell against the reviewed matrix transition. -/

namespace VG.Proof.Argon2.X86_64.FillBlock

open VG VG.X86_64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass lane slice index : Nat) (state : FillState) : Prop where
  ready : ∃ old, RandomSource.Ready p pass lane slice index old t
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (fillBlock p pass slice lane index state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr

theorem code_ok [CompressImpl] (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillBlock.code s (Done s · p pass lane slice index state) := by
  unfold Impl.Argon2.X86_64.FillBlock.code
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
    done.rd.trans source.rd, done.wr.trans source.wr, ?_, done.mxcsr.trans source.mxcsr⟩
  · rw [baseT]; exact matrix
  · intro r hr; exact (done.regs r hr).trans (source.regs r hr)
  · have frame := kernel_frame ready.filling done
    rw [writes, baseA, workA, source.regs .rsp (by simp [calleeSaved]),
      source.regs .rbp (by simp [calleeSaved])] at frame
    exact (source_frame source).trans frame

end VG.Proof.Argon2.X86_64.FillBlock

end

end


/-! Merged from `Proof.Argon2.X86_64.FillIndex`. -/

@[expose] public section

section
/-! Public segment-index advancement retains the filling and cache allocations. -/

namespace VG.Proof.Argon2.X86_64.FillSegment

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillSegment

theorem advance_ok (s : State) : WP isa (.block advance) s fun t =>
    t.gpr .r15 = s.gpr .r15 + 1 ∧
    t.cf = decide ((s.gpr .r15 + 1).toNat < (s.gpr .r13).toNat) ∧
    Divide.Keeps [.r15] s t := by
  apply WP.of_runBlock
  simp only [advance, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    reduceCtorEq, ite_true, ite_false, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  all_goals rfl

theorem advance_nat_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) : WP isa (.block advance) s fun t =>
      t.gpr .r15 = BitVec.ofNat 64 (index + 1) ∧
      t.cf = decide (index + 1 < p.segmentLen) ∧ Divide.Keeps [.r15] s t := by
  refine (advance_ok s).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have added : s.gpr .r15 + 1 = BitVec.ofNat 64 (index + 1) := by
    rw [h.position.index, BitVec.ofNat_add]; rfl
  have endBound : p.segmentLen < 2 ^ 64 := Nat.lt_of_le_of_lt h.bounds.segment_le_lane
    (Nat.lt_trans h.bounds.laneLength_bound (by decide))
  have indexBound := h.bounds.indexBound
  refine ⟨value.trans added, ?_, keeps⟩
  rw [flag, added, h.position.segmentLength,
    ReferenceMap.word_nat (index + 1) (by omega_using [endBound, indexBound]), ReferenceMap.word_nat p.segmentLen endBound]

theorem next_ready {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : RandomSource.Ready p pass lane slice index old s)
    (k : Divide.Keeps [.r15] s t) (value : t.gpr .r15 = BitVec.ofNat 64 (index + 1))
    (active : index + 1 < p.segmentLen) : RandomSource.Ready p pass lane slice (index + 1) old t := by
  have bp := k.regs .rbp (by decide)
  have sp := k.regs .rsp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [k.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [k.mem, bp]
  have kernelWork : FillKernel.work t = FillKernel.work s := work
  refine ⟨?_, h.cache.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact k.regs _ (by decide)) k.mem k.rd k.wr, ?_⟩
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
    · exact ⟨(k.regs .rbx (by decide)).trans h.filling.position.current,
        (k.regs .r12 (by decide)).trans h.filling.position.laneLength,
        (k.regs .r13 (by decide)).trans h.filling.position.segmentLength,
        (k.regs .r14 (by decide)).trans h.filling.position.slice, value⟩
    · rw [k.mem, bp]; exact h.filling.passWord
    · rw [k.mem, bp]; exact h.filling.lanesWord
  · rw [base, work]; exact h.matrixWork

end VG.Proof.Argon2.X86_64.FillSegment
end

/-! Merged from `Proof.Argon2.X86_64.FillAllocation`. -/
section
/-! Transport the allocation using just its public pointers and permissions. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

theorem Layout.of_preserved {p : Params} {s t : State} (h : Layout p s)
    (bp : t.gpr .rbp = s.gpr .rbp) (sp : t.gpr .rsp = s.gpr .rsp)
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

end VG.Proof.Argon2.X86_64.FillKernel
end

/-! One segment iteration updates the specified cell and advances its public index. -/

namespace VG.Proof.Argon2.X86_64.FillSegment

open VG VG.X86_64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass lane slice index : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (fillBlock p pass slice lane index state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  position : ReferenceMap.Position p lane slice (index + 1) t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .r15 → t.gpr r = s.gpr r
  layout : FillKernel.Layout p t
  cache : ∃ old, AddressCache.Invariant p pass lane slice old t
  matrixWork : (⟨FillKernel.matrix t, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work t, 8192⟩
  passWord : t.mem.readW (off (t.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass
  lanesWord : t.mem.readW (off (t.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes
  cf : t.cf = decide (index + 1 < p.segmentLen)
  next : index + 1 < p.segmentLen → ∃ old, RandomSource.Ready p pass lane slice (index + 1) old t

theorem body_ok [CompressImpl] (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillSegment.body s (Done s · p pass lane slice index state) := by
  unfold Impl.Argon2.X86_64.FillSegment.body
  refine WP.seq ((FillBlock.code_ok s p pass lane slice index old h state represented).mono ?_)
  intro a filled
  obtain ⟨counter, ready⟩ := filled.ready
  refine (advance_nat_ok a p pass lane slice index ready.filling).mono ?_
  rintro t ⟨value, cf, keeps⟩
  have bp := keeps.regs .rbp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [keeps.mem, bp]
  refine ⟨?_, base.trans filled.matrix, work.trans filled.work, ?_, keeps.rd.trans filled.rd,
    keeps.wr.trans filled.wr, ?_, (ctl_eq_of keeps.mxcsr).trans filled.mxcsr, ?_, ?_, ?_, ?_, ?_, ?_, cf, ?_⟩
  · rw [keeps.mem, base]; exact filled.represented
  · exact ⟨(keeps.regs .rbx (by decide)).trans ready.filling.position.current,
      (keeps.regs .r12 (by decide)).trans ready.filling.position.laneLength,
      (keeps.regs .r13 (by decide)).trans ready.filling.position.segmentLength,
      (keeps.regs .r14 (by decide)).trans ready.filling.position.slice, value⟩
  · rw [keeps.mem]; exact filled.frame
  · intro r hr ne
    have outside : r ∉ [Reg.r15] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact ne
    exact (keeps.regs r outside).trans (filled.regs r hr)
  · exact ready.filling.layout.of_preserved bp (keeps.regs .rsp (by decide)) base work keeps.rd keeps.wr
  · exact ⟨counter, ready.cache.of_state (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.mem keeps.rd keeps.wr⟩
  · rw [base, work]; exact ready.matrixWork
  · rw [keeps.mem, bp]; exact ready.filling.passWord
  · rw [keeps.mem, bp]; exact ready.filling.lanesWord
  · intro active; exact ⟨counter, next_ready ready keeps value active⟩

end VG.Proof.Argon2.X86_64.FillSegment

end

end


/-! Termination and correctness of the active suffix of one segment. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.FillSegment

open VG VG.X86_64 VG.Spec.Argon2

structure Finished (s t : State) (p : Params) (pass lane slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  position : ReferenceMap.Position p lane slice p.segmentLen t
  layout : FillKernel.Layout p t
  cache : ∃ old, AddressCache.Invariant p pass lane slice old t
  matrixWork : (⟨FillKernel.matrix t, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work t, 8192⟩
  passWord : t.mem.readW (off (t.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass
  lanesWord : t.mem.readW (off (t.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes
  regs : ∀ r ∈ calleeSaved, r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr

theorem Done.finished {s t : State} {p : Params} {pass lane slice index : Nat} {state : FillState}
    (h : Done s t p pass lane slice index state) (last : index + 1 = p.segmentLen) :
    Finished s t p pass lane slice (fillBlock p pass slice lane index state) :=
  ⟨h.represented, h.matrix, h.work, last ▸ h.position, h.layout, h.cache,
    h.matrixWork, h.passWord, h.lanesWord, h.regs, h.rd, h.wr, h.frame, h.mxcsr⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass lane slice index : Nat}
    {state finalState : FillState} (first : Done s a p pass lane slice index state)
    (rest : Finished a t p pass lane slice finalState) : Finished s t p pass lane slice finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work,
    rest.position, rest.layout, rest.cache, rest.matrixWork, rest.passWord, rest.lanesWord,
    ?_, rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.mxcsr.trans first.mxcsr⟩
  · intro r hr ne; exact (rest.regs r hr ne).trans (first.regs r hr ne)
  · have frame := rest.frame
    rw [FillBlock.writes, first.matrix, first.work,
      first.regs .rsp (by simp [calleeSaved]) (by decide),
      first.regs .rbp (by simp [calleeSaved]) (by decide)] at frame
    exact first.frame.trans frame

theorem loop_ok [CompressImpl] (count : Nat) (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endIndex : index + count = p.segmentLen) :
    WP isa Impl.Argon2.X86_64.FillSegment.loop s
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
      · simp only [eval, done.cf, last, Nat.lt_irrefl, decide_false]
      · exact done.finished last
    | succ n =>
      have active : index + 1 < p.segmentLen := by omega_using [endIndex]
      obtain ⟨nextCounter, nextReady⟩ := done.next active
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (index + 1) nextCounter nextReady
        (fillBlock p pass slice lane index state) done.represented (by omega_using []) (by omega_using [endIndex])
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [eval, done.cf, active, decide_true]

end VG.Proof.Argon2.X86_64.FillSegment

end

end


/-! Merged from `Proof.Argon2.X86_64.SegmentSetupSteps`. -/

@[expose] public section

section
/-! Merged from `Proof.Argon2.X86_64.FillContext`. -/
section
/-! A segment context allows its starting and final indices, including an empty suffix. -/

namespace VG.Proof.Argon2.X86_64.FillContext

open VG VG.X86_64 VG.Spec.Argon2

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
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

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
  have bp := k.regs .rbp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [k.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [k.mem, bp]
  refine ⟨h.parameters, h.layout.of_preserved bp (k.regs .rsp (by decide)) base work k.rd k.wr,
    h.cache.of_keeps k, ?_, h.position.of_keeps k, ?_⟩
  · rw [base, work]; exact h.matrixWork
  · rw [k.mem, bp]; exact h.lanesWord

theorem finished_context {p : Params} {pass lane slice : Nat} {s t : State} {state : FillState}
    (parameters : Parameters p pass lane slice) (h : FillSegment.Finished s t p pass lane slice state) :
    ∃ old, Ready p pass lane slice p.segmentLen old t := by
  obtain ⟨old, cache⟩ := h.cache
  exact ⟨old, parameters, h.layout, cache, h.matrixWork, h.position, h.lanesWord⟩

end VG.Proof.Argon2.X86_64.FillContext
end

/-! Select index two only in slice zero of pass zero. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

def start (pass slice : Nat) : Nat := if pass = 0 ∧ slice = 0 then 2 else 0

theorem start_active (pass slice : Nat) : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ start pass slice := by
  unfold start; split <;> omega_arith

theorem start_le (pass slice : Nat) (g : Nat) (minimum : 2 ≤ g) : start pass slice ≤ g := by
  unfold start; split <;> omega_arith

theorem first_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8) :
    WP isa (.block first) s fun t =>
      t.zf = decide (s.mem.readW (off (s.gpr .rbp) 0) 64 = 0#64 ∧ s.gpr .r14 = 0#64) ∧
      Divide.Keeps [.rcx] s t := by
  apply WP.of_runBlock
  simp only [first, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, hr, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags,
    reduceCtorEq, ite_true, ite_false,
    show BitVec.signExtend 64 (0 : BitVec 32) = (0 : Addr) from rfl,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · change ((s.mem.readW (off (s.gpr .rbp) 0) 64 ||| s.gpr .r14) - 0#64 == 0#64) = _
    rw [BitVec.sub_zero]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, BitVec.or_eq_zero_iff, decide_eq_true_eq]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
    all_goals rfl

theorem register_ok (s : State) (register : Reg) (value : BitVec 32) :
    WP isa (.block [.mov register (.imm value)]) s fun t =>
      t.gpr register = value.signExtend 64 ∧ Divide.Keeps [register] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem index_ok (s : State) (pass slice : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8)
    (passWord : s.mem.readW (off (s.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass)
    (sliceWord : s.gpr .r14 = BitVec.ofNat 64 slice)
    (passBound : pass < 2 ^ 64) (sliceBound : slice < 2 ^ 64) : WP isa index s fun t =>
      t.gpr .r15 = BitVec.ofNat 64 (start pass slice) ∧ Divide.Keeps [.rcx, .r15] s t := by
  unfold index
  refine WP.seq ((first_ok s hr).mono ?_)
  rintro a ⟨flag, keeps⟩
  have firstFlag : a.zf = decide (pass = 0 ∧ slice = 0) := by
    rw [flag, passWord, sliceWord]
    have passZero : BitVec.ofNat 64 pass = 0#64 ↔ pass = 0 := ReferenceMap.word_zero pass passBound
    have sliceZero : BitVec.ofNat 64 slice = 0#64 ↔ slice = 0 := ReferenceMap.word_zero slice sliceBound
    simp only [passZero, sliceZero]
  refine WP.ite (decide (pass = 0 ∧ slice = 0)) (by simp only [eval, firstFlag]) ?_ ?_
  · intro mode
    refine (register_ok a .r15 2).mono ?_
    rintro t ⟨value, changed⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (changed.mono (by decide))⟩
    unfold start; simp only [of_decide_eq_true mode]; exact value
  · intro mode
    refine (register_ok a .r15 0).mono ?_
    rintro t ⟨value, changed⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (changed.mono (by decide))⟩
    unfold start; simp only [of_decide_eq_false mode, ite_false]; exact value

theorem check_ok (s : State) : WP isa (.block check) s fun t =>
    t.cf = decide ((s.gpr .r15).toNat < (s.gpr .r13).toNat) ∧ Divide.Keeps [] s t := by
  apply WP.of_runBlock
  simp only [check, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.cf_arithFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r _; exact congrFun (RegUpd.gpr_arithFlags _ _ _ _) r
  all_goals rfl

end VG.Proof.Argon2.X86_64.SegmentSetup
end

/-! Merged from `Proof.Argon2.X86_64.SegmentSetupReset`. -/
section
/-! Merged from `Proof.Argon2.X86_64.SegmentSetupReady`. -/
section
/-! Segment setup needs no previously valid cached block. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : Params) (pass lane slice : Nat) (s : State) : Prop where
  parameters : FillContext.Parameters p pass lane slice
  layout : FillKernel.Layout p s
  addressLayout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  write : InRegions s.wr (off (s.gpr .rbp) 8) 8
  words : ∃ old, AddressHeader.Words p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  laneLength : s.gpr .r12 = BitVec.ofNat 64 p.laneLen
  segmentLength : s.gpr .r13 = BitVec.ofNat 64 p.segmentLen
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

theorem Ready.of_state {p : Params} {pass lane slice : Nat} {s t : State}
    (h : Ready p pass lane slice s)
    (regs : ∀ r ∈ [Reg.rbp, .rsp, .rbx, .r12, .r13, .r14], t.gpr r = s.gpr r)
    (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Ready p pass lane slice t := by
  have bp := regs .rbp (by simp)
  have sp := regs .rsp (by simp)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [mem, bp]
  refine ⟨h.parameters, h.layout.of_preserved bp sp base work rd wr, ?_, ?_, ?_, ?_, ?_,
    (regs .r12 (by simp)).trans h.laneLength, (regs .r13 (by simp)).trans h.segmentLength, ?_⟩
  · constructor
    · rw [rd, wr, bp]; exact h.addressLayout.frameRead
    · rw [wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [rd, wr, bp]; exact h.reads
  · rw [wr, bp]; exact h.write
  · obtain ⟨old, words⟩ := h.words
    refine ⟨old, ?_, (regs .rbx (by simp)).trans words.laneWord,
      (regs .r14 (by simp)).trans words.sliceWord, ?_, ?_, ?_, ?_⟩
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
  have bp := congrFun saved.regs Reg.rbp
  have sp := congrFun saved.regs Reg.rsp
  have base : FillKernel.matrix t = FillKernel.matrix s := saved.read 232 (by decide) (by decide)
  refine ⟨h.parameters, h.layout.of_preserved bp sp base saved.work_eq saved.rd saved.wr,
    saved.ready, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [saved.rd, saved.wr, bp]; exact h.reads
  · rw [saved.wr, bp]; exact h.write
  · obtain ⟨old, words⟩ := h.words
    exact ⟨(s.gpr .rax).toNat, saved.words words (by simp)⟩
  · rw [base, saved.work_eq]; exact h.matrixWork
  · rw [saved.regs]; exact h.laneLength
  · rw [saved.regs]; exact h.segmentLength
  · exact (saved.read 184 (by decide) (by decide)).trans h.lanesWord

end VG.Proof.Argon2.X86_64.SegmentSetup
end

/-! Reset the counter while preserving the segment header and matrix allocation. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

structure Reset (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  ready : Ready p pass lane slice t
  words : AddressHeader.Words p pass lane slice 0 t
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨off (s.gpr .rbp) 8, 8⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem reset_ok (s : State) (p : Params) (pass lane slice : Nat) (h : Ready p pass lane slice s) :
    WP isa reset s (Reset s · p pass lane slice) := by
  unfold reset
  refine WP.seq ((register_ok s .rax 0).mono ?_)
  rintro a ⟨value, keeps⟩
  have next := h.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.mem keeps.rd keeps.wr
  refine (AddressCache.save_ready a next.addressLayout next.write).mono ?_
  intro t saved
  obtain ⟨old, words⟩ := next.words
  have matrixA : FillKernel.matrix a = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .rbp (by decide)]
  have workA : AddressCalls.work a = AddressCalls.work s := by
    unfold AddressCalls.work; rw [keeps.mem, keeps.regs .rbp (by decide)]
  refine ⟨next.saved saved, saved.words words value,
    (saved.read 232 (by decide) (by decide)).trans matrixA, saved.work_eq.trans workA,
    ?_, saved.rd.trans keeps.rd, saved.wr.trans keeps.wr, ?_, saved.mxcsr.trans keeps.mxcsr⟩
  · intro r hr
    have ne : r ∉ [Reg.rax] := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (congrFun saved.regs r).trans (keeps.regs r ne)
  · have frame := saved.frame
    rw [keeps.mem, keeps.regs .rbp (by decide)] at frame
    exact frame

end VG.Proof.Argon2.X86_64.SegmentSetup
end

/-! The prepared context covers ordinary and empty first-segment suffixes. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

structure Prepared (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  context : FillContext.Ready p pass lane slice (start pass slice) 0 t
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ calleeSaved, r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨off (s.gpr .rbp) 8, 8⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

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
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.mem keeps.rd keeps.wr
  have cacheA : AddressCache.Invariant p pass lane slice 0 a :=
    ⟨reset.ready.addressLayout, reset.ready.reads, reset.ready.write, reset.words, by decide, Or.inl rfl⟩
  have cache := cacheA.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.mem keeps.rd keeps.wr
  have base : FillKernel.matrix t = FillKernel.matrix a := by
    unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .rbp (by decide)]
  have work : AddressCalls.work t = AddressCalls.work a := by
    unfold AddressCalls.work; rw [keeps.mem, keeps.regs .rbp (by decide)]
  refine ⟨⟨core.parameters, core.layout, cache, core.matrixWork,
    ⟨cache.words.laneWord, core.laneLength, core.segmentLength, cache.words.sliceWord, value⟩, core.lanesWord⟩,
    base.trans reset.matrix, work.trans reset.work, ?_, keeps.rd.trans reset.rd,
    keeps.wr.trans reset.wr, ?_, keeps.mxcsr.trans reset.mxcsr⟩
  · intro r hr ne
    have outside : r ∉ [Reg.rcx, .r15] := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
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

end VG.Proof.Argon2.X86_64.SegmentSetup
