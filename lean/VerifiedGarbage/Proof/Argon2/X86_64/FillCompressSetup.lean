module

public import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressCall
import VerifiedGarbage.Proof.Argon2.X86_64.FillWriteCover
public import VerifiedGarbage.Impl.Argon2.X86_64.FillCompress
public import VerifiedGarbage.Proof.Argon2.X86_64.Memory
public import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.X86_64.Initialize

/-! ### `Argon2.X86_64.FillCompressOperation`, which only this module used -/

section

/-! Merged from `Proof.Argon2.X86_64.FillCompressArgs`. -/

@[expose] public section

section
/-! Save the current cell across G and reload the block-write arguments. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillCompress

theorem saveCurrent_ok (s : State)
    (hw : InRegions s.wr (off (s.gpr .rbp) 16) 8) :
    WP isa (.block saveCurrent) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rbp) 16) (s.gpr .r10) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [saveCurrent, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.store64, ea_at, hw, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem compressArgs_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8) :
    WP isa (.block compressArgs) s fun t =>
      t.gpr .rcx = s.mem.readW (off (s.gpr .rbp) 248) 64 ∧
      t.gpr .rdx = s.mem.readW (off (s.gpr .rbp) 248) 64 + 4096 ∧
      Divide.Keeps [.rcx, .rdx] s t := by
  apply WP.of_runBlock
  simp only [compressArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, State.load64, ea_at, hr, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left',
    show BitVec.signExtend 64 (4096 : BitVec 32) = (4096 : Addr) from rfl]
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
  all_goals rfl

theorem writeArgs_ok (s : State)
    (destRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 16) 8)
    (workRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8)
    (passRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8) :
    WP isa (.block writeArgs) s fun t =>
      t.gpr .rdi = s.mem.readW (off (s.gpr .rbp) 16) 64 ∧
      t.gpr .rsi = s.mem.readW (off (s.gpr .rbp) 248) 64 + 4096 ∧
      t.gpr .r9 = s.mem.readW (off (s.gpr .rbp) 0) 64 ∧
      Divide.Keeps [.rdi, .rsi, .r9] s t := by
  apply WP.of_runBlock
  simp only [writeArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, State.load64, ea_at, destRead, workRead, passRead, execAlu,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    show BitVec.signExtend 64 (4096 : BitVec 32) = (4096 : Addr) from rfl]
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.X86_64.FillCompress
end

/-! Compression followed by first/later-pass writing, preserving the frame
slots and the old destination cell across the compression call. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillCompress

def callWrites (s : State) : List Region :=
  [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩, below (s.gpr .rsp) 8]

def destination (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 16) 64

def pass (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 0) 64

structure OperationReady (s : State) : Prop where
  call : CallReady s
  frameRead : ∀ d ∈ [0, 16, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  workWord : s.mem.readW (off (s.gpr .rbp) 248) 64 = s.gpr .rcx
  outputPointer : s.gpr .rcx + 4096 = s.gpr .rdx
  destinationWrite : Covers [⟨destination s, 1024⟩] s.wr
  frameSafe : ∀ r ∈ callWrites s, (⟨s.gpr .rbp, 272⟩ : Region).Disjoint r
  destinationSafe : ∀ r ∈ callWrites s, (⟨destination s, 1024⟩ : Region).Disjoint r

structure OperationDone (s t : State) : Prop where
  block : blockAt t.mem (destination s) =
    let next := Spec.Argon2.compress (blockAt s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rsi))
    if pass s = 0 then next else xorBlock next (blockAt s.mem (destination s))
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (⟨destination s, 1024⟩ :: callWrites s) s.mem t.mem

theorem frame_word {s t : State} (h : OperationReady s) (called : Called s t)
    (d : Nat) (hd : d + 8 ≤ 272) :
    t.mem.readW (off (s.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 :=
  called.frame.readW (r := ⟨s.gpr .rbp, 272⟩)
    (Offset.contains_base _ hd (by omega_using [hd])) h.frameSafe (by decide)

theorem destination_unchanged {s t : State} (h : OperationReady s) (called : Called s t) :
    blockAt t.mem (destination s) = blockAt s.mem (destination s) := by
  apply Vector.ext
  intro i hi
  have read : t.mem.readW (off (destination s) (8 * i)) 64 =
      s.mem.readW (off (destination s) (8 * i)) 64 :=
    called.frame.readW (r := ⟨destination s, 1024⟩)
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) h.destinationSafe (by decide)
  rw [← blockAt_get t.mem (destination s) ⟨i, hi⟩,
    ← blockAt_get s.mem (destination s) ⟨i, hi⟩] at read
  exact read

theorem operation_ok [CompressImpl] (s : State) (h : OperationReady s) :
    WP isa operation s fun t => OperationDone s t ∧ ctl t.mxcsr = ctl s.mxcsr := by
  unfold operation
  refine WP.seq ((call_ok s h.call).mono ?_)
  rintro a ⟨called, mx1⟩
  have bp : a.gpr .rbp = s.gpr .rbp := called.regs .rbp (by simp [calleeSaved])
  have reads (d : Nat) (hd : d ∈ [0, 16, 248]) :
      InRegions (a.rd ++ a.wr) (off (a.gpr .rbp) d) 8 := by
    rw [called.rd, called.wr, bp]; exact h.frameRead d hd
  refine WP.seq ((WP.with_mx (by lit_decide) (writeArgs_ok a (reads 16 (by simp))
    (reads 248 (by simp)) (reads 0 (by simp)))).mono ?_)
  rintro b ⟨⟨dest, src, counter, keeps⟩, mx2⟩
  have dest' : b.gpr .rdi = destination s := by
    rw [dest, bp, frame_word h called 16 (by decide), destination]
  have src' : b.gpr .rsi = s.gpr .rdx := by
    rw [src, bp, frame_word h called 248 (by decide), h.workWord, h.outputPointer]
  have counter' : b.gpr .r9 = pass s := by
    rw [counter, bp, frame_word h called 0 (by decide), pass]
  have readable : Covers [⟨b.gpr .rsi, 1024⟩] (b.rd ++ b.wr) := by
    rw [src', keeps.rd, keeps.wr, called.rd, called.wr]
    intro p n hp
    obtain ⟨r, hr, hc⟩ := h.call.output p n hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have writable : Covers [⟨b.gpr .rdi, 1024⟩] b.wr := by
    rw [dest', keeps.wr, called.wr]; exact h.destinationWrite
  have sep : (⟨b.gpr .rsi, 1024⟩ : Region).Disjoint ⟨b.gpr .rdi, 1024⟩ := by
    rw [src', dest']; exact (h.destinationSafe _ (by simp [callWrites])).symm
  refine (WP.with_mx (by lit_decide) (FillWrite.code_cover_ok b readable writable sep)).mono ?_
  rintro t ⟨⟨value, frame, tk, _⟩, mx3⟩
  refine ⟨⟨?_, ?_, tk.2.1.trans (keeps.rd.trans called.rd),
    tk.2.2.trans (keeps.wr.trans called.wr), ?_⟩, by rw [mx3, mx2]; exact mx1⟩
  · rw [dest', src', counter', keeps.mem, called.result, destination_unchanged h called] at value
    exact value
  · intro r hr
    have ne : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have nk : r ∉ [Reg.rdi, .rsi, .r9] := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (tk.1 r ne).trans ((keeps.regs r nk).trans (called.regs r hr))
  · rw [dest'] at frame
    rw [keeps.mem] at frame
    exact (called.frame.mono (by intro r hr; exact List.mem_cons_of_mem _ hr)).trans
      (frame.mono (by simp))

end VG.Proof.Argon2.X86_64.FillCompress

end

end


/-! Establish compression-and-write invariants from the frame and allocations. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillCompress

def work (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 248) 64

def prefixWrites (s : State) : List Region := [⟨off (s.gpr .rbp) 16, 8⟩]

structure Ready (s : State) : Prop where
  frameRead : ∀ d ∈ [0, 16, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  frameWrite : InRegions s.wr (off (s.gpr .rbp) 16) 8
  leftRead : Covers [⟨s.gpr .rdi, 1024⟩] (s.rd ++ s.wr)
  rightRead : Covers [⟨s.gpr .rsi, 1024⟩] (s.rd ++ s.wr)
  destinationWrite : Covers [⟨s.gpr .r10, 1024⟩] s.wr
  workWrite : Covers [⟨work s, 5120⟩] s.wr
  leftWork : (⟨s.gpr .rdi, 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  rightWork : (⟨s.gpr .rsi, 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  destinationWork : (⟨s.gpr .r10, 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  frameWork : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨work s, 5120⟩
  leftFrame : (⟨s.gpr .rdi, 1024⟩ : Region).Disjoint ⟨s.gpr .rbp, 272⟩
  rightFrame : (⟨s.gpr .rsi, 1024⟩ : Region).Disjoint ⟨s.gpr .rbp, 272⟩
  destinationFrame : (⟨s.gpr .r10, 1024⟩ : Region).Disjoint ⟨s.gpr .rbp, 272⟩
  stackLeft : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rdi, 1024⟩
  stackRight : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rsi, 1024⟩
  stackWork : (below (s.gpr .rsp) 8).Disjoint ⟨work s, 5120⟩
  destinationStack : (⟨s.gpr .r10, 1024⟩ : Region).Disjoint (below (s.gpr .rsp) 8)
  frameStack : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint (below (s.gpr .rsp) 8)

structure Prepared (s t : State) : Prop where
  ready : OperationReady t
  dest : destination t = s.gpr .r10
  counter : pass t = pass s
  scratch : t.gpr .rcx = work s
  output : t.gpr .rdx = work s + 4096
  left : t.gpr .rdi = s.gpr .rdi
  right : t.gpr .rsi = s.gpr .rsi
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (prefixWrites s) s.mem t.mem
  leftBlock : blockAt t.mem (t.gpr .rdi) = blockAt s.mem (s.gpr .rdi)
  rightBlock : blockAt t.mem (t.gpr .rsi) = blockAt s.mem (s.gpr .rsi)
  oldBlock : blockAt t.mem (destination t) = blockAt s.mem (s.gpr .r10)

theorem block_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (p : Addr) (sep : ∀ r ∈ rs, (⟨p, 1024⟩ : Region).Disjoint r) :
    blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  have read : m'.readW (off p (8 * i)) 64 = m.readW (off p (8 * i)) 64 :=
    hf.readW (r := ⟨p, 1024⟩) (Offset.contains_base p (by omega_using [hi]) (by omega_using [hi])) sep (by decide)
  rw [← blockAt_get m' p ⟨i, hi⟩, ← blockAt_get m p ⟨i, hi⟩] at read
  exact read

theorem work_cover (s : State) (h : Ready s) (d n : Nat) (hd : d + n ≤ 5120) :
    Covers [⟨off (work s) d, n⟩] s.wr := by
  have sub : Covers [⟨off (work s) d, n⟩] [⟨work s, 5120⟩] := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨work s, 5120⟩, by simp, d, rfl, hd⟩
  exact fun p n hp => h.workWrite p n (sub p n hp)

theorem prepared_of_setup (s a b : State) (h : Ready s)
    (mem : a.mem = s.mem.writeW (off (s.gpr .rbp) 16) (s.gpr .r10))
    (regs : a.gpr = s.gpr) (rd : a.rd = s.rd) (wr : a.wr = s.wr)
    (scratch : b.gpr .rcx = a.mem.readW (off (a.gpr .rbp) 248) 64)
    (output : b.gpr .rdx = a.mem.readW (off (a.gpr .rbp) 248) 64 + 4096)
    (keeps : Divide.Keeps [.rcx, .rdx] a b) : Prepared s b := by
  have g (r : Reg) (hr : r ∉ [Reg.rcx, .rdx]) : b.gpr r = s.gpr r :=
    (keeps.regs r hr).trans (congrFun regs r)
  have brd : b.rd = s.rd := keeps.rd.trans rd
  have bwr : b.wr = s.wr := keeps.wr.trans wr
  have bm : b.mem = s.mem.writeW (off (s.gpr .rbp) 16) (s.gpr .r10) := keeps.mem.trans mem
  have unchanged (d : Nat) (sep : d + 8 ≤ 16 ∨ 24 ≤ d) (bound : d + 8 ≤ 272) :
      b.mem.readW (off (b.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
    rw [bm, g .rbp (by decide)]
    exact Mem.readW_writeW_sep (Offset.sep _ sep (by omega_using [bound]) (by decide)) (by decide)
  have work' : b.gpr .rcx = work s := by
    rw [scratch, regs, mem]
    exact Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)
  have out' : b.gpr .rdx = work s + 4096 := by
    rw [output, regs, mem,
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), work]
  have dest : destination b = s.gpr .r10 := by
    unfold destination
    rw [bm, g .rbp (by decide), Mem.readW_writeW_self64]
  have counter : pass b = pass s := unchanged 0 (by decide) (by decide)
  have frame : Frame (prefixWrites s) s.mem b.mem := by
    rw [bm]
    exact (Frame.refl _ _).writeW (r := ⟨off (s.gpr .rbp) 16, 8⟩) (by simp [prefixWrites]) _
      (Region.contains_self _ _)
  have cellFrame (p : Addr) (sep : (⟨p, 1024⟩ : Region).Disjoint ⟨s.gpr .rbp, 272⟩) :
      blockAt b.mem p = blockAt s.mem p :=
    block_frame frame p (by
      intro r hr
      simp only [prefixWrites, List.mem_singleton] at hr
      subst r
      exact sep.sub_right (Offset.sub_base _ (by decide)))
  have tempSub : Region.Sub ⟨work s + 4096, 1024⟩ ⟨work s, 5120⟩ :=
    Offset.sub_base _ (by decide)
  have scratchSub : Region.Sub ⟨work s, 4096⟩ ⟨work s, 5120⟩ := Region.sub_prefix (by decide)
  refine ⟨?_, dest, counter, work', out', g .rdi (by decide), g .rsi (by decide), ?_, brd, bwr,
    frame, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [g .rdi (by decide), brd, bwr]; exact h.leftRead
      · rw [g .rsi (by decide), brd, bwr]; exact h.rightRead
      · rw [out', bwr]; exact work_cover s h 4096 1024 (by decide)
      · rw [work', bwr]
        simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
          using work_cover s h 0 4096 (by decide)
      · rw [g .rdi (by decide), work']; exact h.leftWork.sub_right scratchSub
      · rw [g .rsi (by decide), work']; exact h.rightWork.sub_right scratchSub
      · rw [out', work']; exact Offset.disjoint_base _ (by decide) (by decide)
      · rw [g .rsp (by decide), g .rdi (by decide)]; exact h.stackLeft
      · rw [g .rsp (by decide), g .rsi (by decide)]; exact h.stackRight
      · rw [g .rsp (by decide), out']; exact h.stackWork.sub_right tempSub
      · rw [g .rsp (by decide), work']; exact h.stackWork.sub_right scratchSub
    · intro d hd
      rw [brd, bwr, g .rbp (by decide)]; exact h.frameRead d hd
    · rw [unchanged 248 (by decide) (by decide), work']; rfl
    · rw [work', out']
    · rw [dest, bwr]; exact h.destinationWrite
    · intro r hr
      simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [g .rbp (by decide), out']; exact h.frameWork.sub_right tempSub
      · rw [g .rbp (by decide), work']; exact h.frameWork.sub_right scratchSub
      · rw [g .rbp (by decide), g .rsp (by decide)]; exact h.frameStack
    · intro r hr
      rw [dest]
      simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [out']; exact h.destinationWork.sub_right tempSub
      · rw [work']; exact h.destinationWork.sub_right scratchSub
      · rw [g .rsp (by decide)]; exact h.destinationStack
  · intro r hr
    apply g r
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [g .rdi (by decide)]; exact cellFrame _ h.leftFrame
  · rw [g .rsi (by decide)]; exact cellFrame _ h.rightFrame
  · rw [dest]; exact cellFrame _ h.destinationFrame

theorem setup_ok (s : State) (h : Ready s) :
    WP isa setup s (Prepared s) := by
  unfold setup
  refine WP.seq ((saveCurrent_ok s h.frameWrite).mono ?_)
  rintro a ⟨mem, regs, rd, wr, _⟩
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .rbp) 248) 8 := by
    rw [rd, wr, regs]; exact h.frameRead 248 (by simp)
  refine (compressArgs_ok a read).mono ?_
  rintro b ⟨scratch, output, keeps⟩
  exact prepared_of_setup s a b h mem regs rd wr scratch output keeps

end VG.Proof.Argon2.X86_64.FillCompress
