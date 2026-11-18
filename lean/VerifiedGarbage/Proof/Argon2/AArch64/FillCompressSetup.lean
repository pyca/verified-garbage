module

public import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressCall
public import VerifiedGarbage.Impl.Argon2.AArch64.FillCompress
public import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.AArch64.Initialize
import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Argon2.AArch64.FillWritePrefix
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Argon2.AArch64.CountCandidates
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Argon2.AArch64.FillWriteCover`, which this module and modules that import it used -/

section

/-! Merged from `Proof.Argon2.AArch64.FillWrite`. -/

@[expose] public section

section
/-! Whole-block first-pass copying and later-pass XOR, with a frame proof. -/

namespace VG.Proof.Argon2.AArch64.FillWrite

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillWrite

theorem code_ok (s : State)
    (hs : (⟨s.gpr .x1, 1024⟩ : Region) ∈ s.rd ++ s.wr)
    (hw : (⟨s.gpr .x0, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩) :
    WP isa code s fun t =>
      blockAt t.mem (s.gpr .x0) =
        (if s.gpr .x5 = 0 then blockAt s.mem (s.gpr .x1)
          else xorBlock (blockAt s.mem (s.gpr .x1)) (blockAt s.mem (s.gpr .x0))) ∧
      Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.sp = s.sp := by
  unfold code
  refine WP.seq ((CountCandidates.compare_ok s).mono ?_)
  rintro a ⟨flag, ka⟩
  have src : a.gpr .x1 = s.gpr .x1 := ka.regs .x1 (by simp)
  have dest : a.gpr .x0 = s.gpr .x0 := ka.regs .x0 (by simp)
  have hs' : (⟨a.gpr .x1, 1024⟩ : Region) ∈ a.rd ++ a.wr := by
    rw [src, ka.rd, ka.wr]; exact hs
  have hw' : (⟨a.gpr .x0, 1024⟩ : Region) ∈ a.wr := by
    rw [dest, ka.wr]; exact hw
  have hd' : (⟨a.gpr .x1, 1024⟩ : Region).Disjoint ⟨a.gpr .x0, 1024⟩ := by
    rw [src, dest]; exact hd
  refine WP.ite (decide (s.gpr .x5 = 0)) (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag, Bool.beq_eq_decide_eq]) ?_ ?_
  · intro h
    have zero := of_decide_eq_true h
    refine (prefix_ok false 64 (by decide) a hs' hw' hd').mono ?_
    rintro t ⟨written, frame, gpr, rd, wr, mx⟩
    have keeps : CopyKeeps a t := ⟨fun r _ _ _ _ => congrFun gpr r, rd, wr⟩
    refine ⟨?_, ?_, ?_, mx.trans ka.sp⟩
    · rw [dest] at written
      rw [ite_eq_left zero, written_block written]
      simp only [result, Bool.false_eq_true, ite_false, ka.mem, src]
    · rw [dest, ka.mem] at frame; exact frame
    · exact (show CopyKeeps s a from ⟨fun r _ h13 h14 h15 => ka.regs r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨h13, h14, h15⟩), ka.rd, ka.wr⟩).trans keeps
  · intro h
    have nonzero := of_decide_eq_false h
    refine (prefix_ok true 64 (by decide) a hs' hw' hd').mono ?_
    rintro t ⟨written, frame, gpr, rd, wr, mx⟩
    have keeps : CopyKeeps a t := ⟨fun r _ _ _ _ => congrFun gpr r, rd, wr⟩
    refine ⟨?_, ?_, ?_, mx.trans ka.sp⟩
    · rw [dest] at written
      rw [ite_eq_right nonzero, written_block written]
      simp only [result, ite_true, ka.mem, src]
    · rw [dest, ka.mem] at frame; exact frame
    · exact (show CopyKeeps s a from ⟨fun r _ h13 h14 h15 => ka.regs r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨h13, h14, h15⟩), ka.rd, ka.wr⟩).trans keeps

end VG.Proof.Argon2.AArch64.FillWrite
end

/-! Use block writes in a matrix allocation with larger permission regions. -/

namespace VG.Proof.Argon2.AArch64.FillWrite

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillWrite

theorem code_cover_ok (s : State)
    (hs : Covers [⟨s.gpr .x1, 1024⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨s.gpr .x0, 1024⟩] s.wr)
    (hd : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩) :
    WP isa code s fun t =>
      blockAt t.mem (s.gpr .x0) =
        (if s.gpr .x5 = 0 then blockAt s.mem (s.gpr .x1)
          else xorBlock (blockAt s.mem (s.gpr .x1)) (blockAt s.mem (s.gpr .x0))) ∧
      Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.sp = s.sp := by
  let a := s.withRegions [⟨s.gpr .x1, 1024⟩] [⟨s.gpr .x0, 1024⟩]
  obtain ⟨tr, t, he, value, frame, keeps, mx⟩ := code_ok a (by simp [a]) (by simp [a]) hd
  have cover : Covers (a.rd ++ a.wr) (s.rd ++ s.wr) := by
    intro p n ⟨r, hr, hc⟩
    change r ∈ [⟨s.gpr .x1, 1024⟩, ⟨s.gpr .x0, 1024⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs p n ⟨_, by simp, hc⟩
    · obtain ⟨r, hr, hc⟩ := hw p n ⟨_, by simp, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  have he' := Exec.widen (rd := s.rd) (wr := s.wr) he cover hw
  simp only [a, State.withRegions_withRegions, State.withRegions_self] at he'
  refine ⟨tr, t.withRegions s.rd s.wr, he', value, frame, ?_, mx⟩
  exact ⟨keeps.1, rfl, rfl⟩

end VG.Proof.Argon2.AArch64.FillWrite

end

end

/-! ### `Argon2.AArch64.FillCompressOperation`, which only this module used -/

section

/-! Merged from `Proof.Argon2.AArch64.FillCompressArgs`. -/

@[expose] public section

section
/-! Save the current cell across G and reload the block-write arguments. -/
namespace VG.Proof.Argon2.AArch64.FillCompress
open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillCompress
open VG.Impl.Argon2.AArch64

theorem saveCurrent_ok (s : State)
    (hw : InRegions s.wr (off (s.gpr .x19) 16) 8) :
    WP isa (.block saveCurrent) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x19) 16) (s.gpr .x6) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [saveCurrent, Instructions.store, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, State.store, State.read, Size.bytes, and_self, Option.bind_some, Size.bits, BitVec.setWidth_eq, hw,
    show 16 % 8 = 0 ∧ 16 < 4096 * 8 from by decide,
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial⟩

theorem compressArgs_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8) :
    WP isa (.block compressArgs) s fun t =>
      t.gpr .x3 = s.mem.readW (off (s.gpr .x19) 248) 64 ∧
      t.gpr .x2 = s.mem.readW (off (s.gpr .x19) 248) 64 + 4096 ∧ Divide.Keeps [.x3, .x2, .x12, .x15] s t := by
  simp only [off] at hr
  apply WP.of_runBlock
  simp only [compressArgs, Instructions.load, Instructions.mov, Instructions.addi,
    Instructions.imm, Instructions.mark, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, Size.bytes, off, and_self, Option.map_some, Option.bind_some,
    State.read, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    hr,
    show 248 % 8 = 0 ∧ 248 < 4096 * 8 from by decide,
    show 0 < 4096 from by decide,
    show ¬4096 < 4096 from by decide,
    show 4096 < 65536 from by decide,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero, BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem writeArgs_ok (s : State)
    (destRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 16) 8)
    (workRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8)
    (passRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8) :
    WP isa (.block writeArgs) s fun t =>
      t.gpr .x0 = s.mem.readW (off (s.gpr .x19) 16) 64 ∧
      t.gpr .x1 = s.mem.readW (off (s.gpr .x19) 248) 64 + 4096 ∧
      t.gpr .x5 = s.mem.readW (off (s.gpr .x19) 0) 64 ∧ Divide.Keeps [.x0, .x1, .x5, .x12, .x15] s t := by
  simp only [off, BitVec.add_zero] at destRead workRead passRead
  apply WP.of_runBlock
  simp only [writeArgs, Instructions.load, Instructions.mov, Instructions.addi,
    Instructions.imm, Instructions.mark, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, Size.bytes, off, and_self, Option.map_some, Option.bind_some,
    State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, Size.bits, BitVec.setWidth_eq,
    show 16 % 8 = 0 ∧ 16 < 4096 * 8 from by decide,
    show 0 % 8 = 0 ∧ 0 < 4096 * 8 from by decide, BitVec.add_zero,
    destRead, workRead, passRead,
    show 248 % 8 = 0 ∧ 248 < 4096 * 8 from by decide,
    show 0 < 4096 from by decide,
    show ¬4096 < 4096 from by decide,
    show 4096 < 65536 from by decide,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero, BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.AArch64.FillCompress
end

/-! Compression followed by first/later-pass writing, preserving the frame
slots and the old destination cell across the compression call. -/

namespace VG.Proof.Argon2.AArch64.FillCompress

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillCompress

def callWrites (s : State) : List Region :=
  [⟨s.gpr .x2, 1024⟩, ⟨s.gpr .x3, 4096⟩, below s.sp 8]

def destination (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 16) 64

def pass (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 0) 64

structure OperationReady (s : State) : Prop where
  call : CallReady s
  frameRead : ∀ d ∈ [0, 16, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  workWord : s.mem.readW (off (s.gpr .x19) 248) 64 = s.gpr .x3
  outputPointer : s.gpr .x3 + 4096 = s.gpr .x2
  destinationWrite : Covers [⟨destination s, 1024⟩] s.wr
  frameSafe : ∀ r ∈ callWrites s, (⟨s.gpr .x19, 272⟩ : Region).Disjoint r
  destinationSafe : ∀ r ∈ callWrites s, (⟨destination s, 1024⟩ : Region).Disjoint r

structure OperationDone (s t : State) : Prop where
  block : blockAt t.mem (destination s) =
    let next := Spec.Argon2.compress (blockAt s.mem (s.gpr .x0)) (blockAt s.mem (s.gpr .x1))
    if pass s = 0 then next else xorBlock next (blockAt s.mem (destination s))
  regs : ∀ r ∈ loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (⟨destination s, 1024⟩ :: callWrites s) s.mem t.mem

theorem frame_word {s t : State} (h : OperationReady s) (called : Called s t)
    (d : Nat) (hd : d + 8 ≤ 272) :
    t.mem.readW (off (s.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 :=
  called.frame.readW (r := ⟨s.gpr .x19, 272⟩)
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

theorem operation_ok (s : State) (h : OperationReady s) :
    WP isa operation s (OperationDone s) := by
  unfold operation
  refine WP.seq ((call_ok _ s h.call).mono ?_)
  intro a called
  have bp : a.gpr .x19 = s.gpr .x19 := called.regs .x19 (by simp [loopRegs])
  have reads (d : Nat) (hd : d ∈ [0, 16, 248]) :
      InRegions (a.rd ++ a.wr) (off (a.gpr .x19) d) 8 := by
    rw [called.rd, called.wr, bp]; exact h.frameRead d hd
  refine WP.seq ((writeArgs_ok a (reads 16 (by simp)) (reads 248 (by simp))
    (reads 0 (by simp))).mono ?_)
  rintro b ⟨dest, src, counter, keeps⟩
  have dest' : b.gpr .x0 = destination s := by
    rw [dest, bp, frame_word h called 16 (by decide), destination]
  have src' : b.gpr .x1 = s.gpr .x2 := by
    rw [src, bp, frame_word h called 248 (by decide), h.workWord, h.outputPointer]
  have counter' : b.gpr .x5 = pass s := by
    rw [counter, bp, frame_word h called 0 (by decide), pass]
  have readable : Covers [⟨b.gpr .x1, 1024⟩] (b.rd ++ b.wr) := by
    rw [src', keeps.rd, keeps.wr, called.rd, called.wr]
    intro p n hp
    obtain ⟨r, hr, hc⟩ := h.call.output p n hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have writable : Covers [⟨b.gpr .x0, 1024⟩] b.wr := by
    rw [dest', keeps.wr, called.wr]; exact h.destinationWrite
  have sep : (⟨b.gpr .x1, 1024⟩ : Region).Disjoint ⟨b.gpr .x0, 1024⟩ := by
    rw [src', dest']; exact (h.destinationSafe _ (by simp [callWrites])).symm
  refine (FillWrite.code_cover_ok b readable writable sep).mono ?_
  rintro t ⟨value, frame, tk, tsp⟩
  refine ⟨?_, ?_, tk.2.1.trans (keeps.rd.trans called.rd),
    tk.2.2.trans (keeps.wr.trans called.wr), tsp.trans (keeps.sp.trans called.sp), ?_⟩
  · rw [dest', src', counter', keeps.mem, called.result, destination_unchanged h called] at value
    exact value
  · intro r hr
    have safe : r ≠ .x8 ∧ r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x15 ∧
        r ∉ [Reg.x0, .x1, .x5, .x12, .x15] := by
      simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (tk.1 r safe.1 safe.2.1 safe.2.2.1 safe.2.2.2.1).trans
      ((keeps.regs r safe.2.2.2.2).trans (called.regs r hr))
  · rw [dest'] at frame
    rw [keeps.mem] at frame
    exact (called.frame.mono (by intro r hr; exact List.mem_cons_of_mem _ hr)).trans
      (frame.mono (by simp))

end VG.Proof.Argon2.AArch64.FillCompress

end

end


/-! Establish compression-and-write invariants from the frame and allocations. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.FillCompress

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillCompress

def work (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 248) 64

def prefixWrites (s : State) : List Region := [⟨off (s.gpr .x19) 16, 8⟩]

structure Ready (s : State) : Prop where
  frameRead : ∀ d ∈ [0, 16, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  frameWrite : InRegions s.wr (off (s.gpr .x19) 16) 8
  leftRead : Covers [⟨s.gpr .x0, 1024⟩] (s.rd ++ s.wr)
  rightRead : Covers [⟨s.gpr .x1, 1024⟩] (s.rd ++ s.wr)
  destinationWrite : Covers [⟨s.gpr .x6, 1024⟩] s.wr
  workWrite : Covers [⟨work s, 5120⟩] s.wr
  leftWork : (⟨s.gpr .x0, 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  rightWork : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  destinationWork : (⟨s.gpr .x6, 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  frameWork : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨work s, 5120⟩
  leftFrame : (⟨s.gpr .x0, 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩
  rightFrame : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩
  destinationFrame : (⟨s.gpr .x6, 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩
  stackLeft : (below s.sp 8).Disjoint ⟨s.gpr .x0, 1024⟩
  stackRight : (below s.sp 8).Disjoint ⟨s.gpr .x1, 1024⟩
  stackWork : (below s.sp 8).Disjoint ⟨work s, 5120⟩
  destinationStack : (⟨s.gpr .x6, 1024⟩ : Region).Disjoint (below s.sp 8)
  frameStack : (⟨s.gpr .x19, 272⟩ : Region).Disjoint (below s.sp 8)

structure Prepared (s t : State) : Prop where
  ready : OperationReady t
  dest : destination t = s.gpr .x6
  counter : pass t = pass s
  scratch : t.gpr .x3 = work s
  output : t.gpr .x2 = work s + 4096
  left : t.gpr .x0 = s.gpr .x0
  right : t.gpr .x1 = s.gpr .x1
  regs : ∀ r ∈ loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (prefixWrites s) s.mem t.mem
  leftBlock : blockAt t.mem (t.gpr .x0) = blockAt s.mem (s.gpr .x0)
  rightBlock : blockAt t.mem (t.gpr .x1) = blockAt s.mem (s.gpr .x1)
  oldBlock : blockAt t.mem (destination t) = blockAt s.mem (s.gpr .x6)

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
    (mem : a.mem = s.mem.writeW (off (s.gpr .x19) 16) (s.gpr .x6))
    (regs : a.gpr = s.gpr) (rd : a.rd = s.rd) (wr : a.wr = s.wr) (sp : a.sp = s.sp)
    (scratch : b.gpr .x3 = a.mem.readW (off (a.gpr .x19) 248) 64)
    (output : b.gpr .x2 = a.mem.readW (off (a.gpr .x19) 248) 64 + 4096)
    (keeps : Divide.Keeps [.x3, .x2, .x12, .x15] a b) : Prepared s b := by
  have g (r : Reg) (hr : r ∉ [Reg.x3, .x2, .x12, .x15]) : b.gpr r = s.gpr r :=
    (keeps.regs r hr).trans (congrFun regs r)
  have brd : b.rd = s.rd := keeps.rd.trans rd
  have bwr : b.wr = s.wr := keeps.wr.trans wr
  have bsp : b.sp = s.sp := keeps.sp.trans sp
  have bm : b.mem = s.mem.writeW (off (s.gpr .x19) 16) (s.gpr .x6) := keeps.mem.trans mem
  have unchanged (d : Nat) (sep : d + 8 ≤ 16 ∨ 24 ≤ d) (bound : d + 8 ≤ 272) :
      b.mem.readW (off (b.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
    rw [bm, g .x19 (by decide)]
    exact Mem.readW_writeW_sep (Offset.sep _ sep (by omega_using [bound]) (by decide)) (by decide)
  have work' : b.gpr .x3 = work s := by
    rw [scratch, regs, mem]
    exact Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)
  have out' : b.gpr .x2 = work s + 4096 := by
    rw [output, regs, mem,
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), work]
  have dest : destination b = s.gpr .x6 := by
    unfold destination
    rw [bm, g .x19 (by decide), Mem.readW_writeW_self64]
  have counter : pass b = pass s := unchanged 0 (by decide) (by decide)
  have frame : Frame (prefixWrites s) s.mem b.mem := by
    rw [bm]
    exact (Frame.refl _ _).writeW (r := ⟨off (s.gpr .x19) 16, 8⟩) (by simp [prefixWrites]) _
      (Region.contains_self _ _)
  have cellFrame (p : Addr) (sep : (⟨p, 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩) :
      blockAt b.mem p = blockAt s.mem p :=
    block_frame frame p (by
      intro r hr
      simp only [prefixWrites, List.mem_singleton] at hr
      subst r
      exact sep.sub_right (Offset.sub_base _ (by decide)))
  have tempSub : Region.Sub ⟨work s + 4096, 1024⟩ ⟨work s, 5120⟩ :=
    Offset.sub_base _ (by decide)
  have scratchSub : Region.Sub ⟨work s, 4096⟩ ⟨work s, 5120⟩ := Region.sub_prefix (by decide)
  refine ⟨?_, dest, counter, work', out', g .x0 (by decide), g .x1 (by decide), ?_, brd, bwr, bsp,
    frame, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [g .x0 (by decide), brd, bwr]; exact h.leftRead
      · rw [g .x1 (by decide), brd, bwr]; exact h.rightRead
      · rw [out', bwr]; exact work_cover s h 4096 1024 (by decide)
      · rw [work', bwr]
        simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
          using work_cover s h 0 4096 (by decide)
      · rw [g .x0 (by decide), work']; exact h.leftWork.sub_right scratchSub
      · rw [g .x1 (by decide), work']; exact h.rightWork.sub_right scratchSub
      · rw [out', work']; exact Offset.disjoint_base _ (by decide) (by decide)
      · rw [bsp, g .x0 (by decide)]; exact h.stackLeft
      · rw [bsp, g .x1 (by decide)]; exact h.stackRight
      · rw [bsp, out']; exact h.stackWork.sub_right tempSub
      · rw [bsp, work']; exact h.stackWork.sub_right scratchSub
    · intro d hd
      rw [brd, bwr, g .x19 (by decide)]; exact h.frameRead d hd
    · rw [unchanged 248 (by decide) (by decide), work']; rfl
    · rw [work', out']
    · rw [dest, bwr]; exact h.destinationWrite
    · intro r hr
      simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [g .x19 (by decide), out']; exact h.frameWork.sub_right tempSub
      · rw [g .x19 (by decide), work']; exact h.frameWork.sub_right scratchSub
      · rw [g .x19 (by decide), bsp]; exact h.frameStack
    · intro r hr
      rw [dest]
      simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [out']; exact h.destinationWork.sub_right tempSub
      · rw [work']; exact h.destinationWork.sub_right scratchSub
      · rw [bsp]; exact h.destinationStack
  · intro r hr
    apply g r
    simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [g .x0 (by decide)]; exact cellFrame _ h.leftFrame
  · rw [g .x1 (by decide)]; exact cellFrame _ h.rightFrame
  · rw [dest]; exact cellFrame _ h.destinationFrame

theorem setup_ok (s : State) (h : Ready s) :
    WP isa setup s (Prepared s) := by
  unfold setup
  refine WP.seq ((saveCurrent_ok s h.frameWrite).mono ?_)
  rintro a ⟨mem, regs, rd, wr, sp⟩
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) 248) 8 := by
    rw [rd, wr, regs]; exact h.frameRead 248 (by simp)
  refine (compressArgs_ok a read).mono ?_
  rintro b ⟨scratch, output, keeps⟩
  exact prepared_of_setup s a b h mem regs rd wr sp scratch output keeps

end VG.Proof.Argon2.AArch64.FillCompress
