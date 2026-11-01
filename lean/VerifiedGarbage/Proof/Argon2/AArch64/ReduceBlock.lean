module

public import VerifiedGarbage.Impl.Argon2.AArch64.ReduceBlock
public import VerifiedGarbage.Proof.Argon2.AArch64.FillWritePrefix
import VerifiedGarbage.Proof.Argon2.FinalReduction
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Argon2.Contract

/-! # The final block XOR as a loop of eight-word passes

Each pass XORs eight words at the advancing pointers `x0` and `x1` and counts
`x14` down from sixteen; the pointers are restored after the last pass. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.ReduceBlock

open VG VG.AArch64 VG.Spec.Argon2
open VG.Proof.Argon2.AArch64.FillWrite (result result_get frame_extend source_read old_read)

theorem word_ok (s : State) (i : Nat) (hi : i < 8)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x1) (8 * i)) 8)
    (hw : InRegions s.wr (off (s.gpr .x0) (8 * i)) 8)
    (ho : InRegions (s.rd ++ s.wr) (off (s.gpr .x0) (8 * i)) 8) :
    WP isa (.block (Impl.Argon2.AArch64.ReduceBlock.word i)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x0) (8 * i))
        (s.mem.readW (off (s.gpr .x1) (8 * i)) 64 ^^^ s.mem.readW (off (s.gpr .x0) (8 * i)) 64) ∧
      (∀ r, r ≠ .x8 → r ≠ .x13 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hoff : (8 * i) % 8 = 0 ∧ 8 * i < 4096 * 8 := by omega
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.ReduceBlock.word, runBlock_cons, runStep_some, runBlock_nil, exec, addr, hoff,
      State.load, State.store, State.read, Size.bits, Size.bytes,
      off, hr, hw, ho, and_self,
      RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
      BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
      Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, trivial, trivial, rfl⟩
  intro r h8 h13
  simp only [h8, h13, ite_false]

/-- The XOR of the two blocks, as `FillWrite` writes it on later passes. -/
abbrev R (m : Mem) (src dest : Addr) : Block := result true m src dest

/-- The words of one pass: `n` words at the pointers of pass `j`. -/
theorem words_ok (m₀ : Mem) (dest src : Addr) (j : Nat) (hj : j < 16) (s : State)
    (hs : Covers [⟨src, 1024⟩] (s.rd ++ s.wr)) (hw : Covers [⟨dest, 1024⟩] s.wr)
    (hd : (⟨src, 1024⟩ : Region).Disjoint ⟨dest, 1024⟩)
    (pd : s.gpr .x0 = off dest (64 * j)) (ps : s.gpr .x1 = off src (64 * j))
    (written : Written s.mem dest (R m₀ src dest) (8 * j))
    (frame : Frame [⟨dest, 8 * (8 * j)⟩] m₀ s.mem) (n : Nat) (hn : n ≤ 8) :
    WP isa (.block (Impl.Argon2.AArch64.ReduceBlock.words n)) s fun t =>
      Written t.mem dest (R m₀ src dest) (8 * j + n) ∧
      Frame [⟨dest, 8 * (8 * j + n)⟩] m₀ t.mem ∧
      (∀ r, r ≠ .x8 → r ≠ .x13 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction n with
  | zero => exact WP.block_nil ⟨written, frame, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    simp only [Impl.Argon2.AArch64.ReduceBlock.words, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨writtenT, frameT, regs, rd, wr, mx⟩
    have k : 8 * j + n < 128 := by omega
    have at_ (p : Addr) (r : Reg) (hr : s.gpr r = off p (64 * j)) :
        off (s.gpr r) (8 * n) = off p (8 * (8 * j + n)) := by
      rw [hr]
      exact Offset.add_add_eq p (by omega)
    have dest' : off (t.gpr .x0) (8 * n) = off dest (8 * (8 * j + n)) := by
      rw [regs .x0 (by decide) (by decide)]; exact at_ dest .x0 pd
    have src' : off (t.gpr .x1) (8 * n) = off src (8 * (8 * j + n)) := by
      rw [regs .x1 (by decide) (by decide)]; exact at_ src .x1 ps
    have write : InRegions t.wr (off (t.gpr .x0) (8 * n)) 8 := by
      rw [dest', wr]
      exact hw _ _ ⟨⟨dest, 1024⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    have read : InRegions (t.rd ++ t.wr) (off (t.gpr .x1) (8 * n)) 8 := by
      rw [src', rd, wr]
      exact hs _ _ ⟨⟨src, 1024⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    have old : InRegions (t.rd ++ t.wr) (off (t.gpr .x0) (8 * n)) 8 := by
      obtain ⟨r, hr, hc⟩ := write
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    refine (word_ok t n (by omega) read write old).mono ?_
    rintro u ⟨mem, regs', rd', wr', mx'⟩
    have v : t.mem.readW (off (t.gpr .x1) (8 * n)) 64 ^^^ t.mem.readW (off (t.gpr .x0) (8 * n)) 64 =
        (R m₀ src dest)[(⟨8 * j + n, k⟩ : Fin 128)] := by
      rw [R, result_get, src', dest', source_read frameT (by omega) hd ⟨8 * j + n, k⟩,
        old_read frameT (Nat.le_refl _) k]
      rfl
    refine ⟨?_, ?_, fun r h8 h13 => (regs' r h8 h13).trans (regs r h8 h13),
      rd'.trans rd, wr'.trans wr, mx'.trans mx⟩
    · rw [mem, v, dest']
      exact written_step k writtenT
    · rw [mem, dest', show 8 * (8 * j + (n + 1)) = 8 * (8 * j + n + 1) by omega]
      exact (frame_extend frameT (Nat.le_succ _)).writeW
        (r := ⟨dest, 8 * (8 * j + n + 1)⟩) (by simp) _
        (Offset.contains_base _ (by omega) (by omega))

theorem advance_ok (s : State) :
    WP isa (.block Impl.Argon2.AArch64.ReduceBlock.advance) s fun t =>
      t.gpr .x0 = s.gpr .x0 + 64 ∧ t.gpr .x1 = s.gpr .x1 + 64 ∧ t.gpr .x14 = s.gpr .x14 - 1 ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x14 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.ReduceBlock.advance, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 64 < 4096 from by decide, show 1 < 4096 from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro r h0 h1 h14
  simp only [h0, h1, h14, ite_false]

/-- After `j` passes. -/
structure Inv (s₀ : State) (j : Nat) (s : State) : Prop where
  bound : j ≤ 16
  dest : s.gpr .x0 = off (s₀.gpr .x0) (64 * j)
  src : s.gpr .x1 = off (s₀.gpr .x1) (64 * j)
  count : s.gpr .x14 = BitVec.ofNat 64 (16 - j)
  written : Written s.mem (s₀.gpr .x0) (R s₀.mem (s₀.gpr .x1) (s₀.gpr .x0)) (8 * j)
  frame : Frame [⟨s₀.gpr .x0, 8 * (8 * j)⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x8 → r ≠ .x13 → r ≠ .x14 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem body_ok (s₀ : State) (j : Nat) (hj : j < 16) (s : State) (h : Inv s₀ j s)
    (hs : Covers [⟨s₀.gpr .x1, 1024⟩] (s₀.rd ++ s₀.wr)) (hw : Covers [⟨s₀.gpr .x0, 1024⟩] s₀.wr)
    (hd : (⟨s₀.gpr .x1, 1024⟩ : Region).Disjoint ⟨s₀.gpr .x0, 1024⟩) :
    WP isa Impl.Argon2.AArch64.ReduceBlock.body s (Inv s₀ (j + 1)) := by
  unfold Impl.Argon2.AArch64.ReduceBlock.body
  refine WP.seq ((words_ok s₀.mem (s₀.gpr .x0) (s₀.gpr .x1) j hj s (by rw [h.rd, h.wr]; exact hs)
    (by rw [h.wr]; exact hw) hd h.dest h.src h.written h.frame 8 (Nat.le_refl _)).mono ?_)
  rintro a ⟨written, frame, regsA, rdA, wrA, spA⟩
  refine (advance_ok a).mono ?_
  rintro t ⟨dst, sr, cnt, regsT, mem, rd, wr, sp⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, rd.trans (rdA.trans h.rd), wr.trans (wrA.trans h.wr),
    sp.trans (spA.trans h.sp)⟩
  · rw [dst, regsA .x0 (by decide) (by decide), h.dest, show (64 : Addr) = BitVec.ofNat 64 64 from rfl]
    exact Offset.add_add_eq _ (by omega)
  · rw [sr, regsA .x1 (by decide) (by decide), h.src, show (64 : Addr) = BitVec.ofNat 64 64 from rfl]
    exact Offset.add_add_eq _ (by omega)
  · rw [cnt, regsA .x14 (by decide) (by decide), h.count, show (1 : Addr) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  · rw [mem]; exact written
  · rw [mem]; exact frame
  · intro r h0 h1 h8 h13 h14
    rw [regsT r h0 h1 h14, regsA r h8 h13]
    exact h.regs r h0 h1 h8 h13 h14

theorem loop_ok (s₀ : State) (s : State) (h : Inv s₀ 0 s)
    (hs : Covers [⟨s₀.gpr .x1, 1024⟩] (s₀.rd ++ s₀.wr)) (hw : Covers [⟨s₀.gpr .x0, 1024⟩] s₀.wr)
    (hd : (⟨s₀.gpr .x1, 1024⟩ : Region).Disjoint ⟨s₀.gpr .x0, 1024⟩) :
    WP isa (.loop Impl.Argon2.AArch64.ReduceBlock.body (.nonzero .x .x14)) s (Inv s₀ 16) := by
  refine WP.loop (M := isa) (fun k s => ∃ j, k = 16 - j ∧ j < 16 ∧ Inv s₀ j s)
    ?_ 16 s ⟨0, rfl, by decide, h⟩
  rintro k s ⟨j, rfl, hj, h⟩
  refine (body_ok s₀ j hj s h hs hw hd).mono ?_
  intro t next
  have flag : eval (.nonzero .x .x14) t = some (decide (16 - (j + 1) ≠ 0)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, next.count]
    congr 1
    rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff, ne_eq, ne_eq]
    refine not_congr ⟨fun eq => ?_, fun eq => by rw [eq]; rfl⟩
    have num := congrArg BitVec.toNat eq
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 16 - (j + 1) < 2 ^ 64),
      show (0 : Addr).toNat = 0 from rfl] using num
  by_cases done : j + 1 = 16
  · refine .inl ⟨?_, done ▸ next⟩
    simpa only [show 16 - (j + 1) = 0 by omega, ne_eq, not_true_eq_false, decide_false] using flag
  · refine .inr ⟨?_, 16 - (j + 1), by omega, j + 1, rfl, by omega, next⟩
    change eval (.nonzero .x .x14) t = some true
    rw [flag]
    exact congrArg some (decide_eq_true (by omega : 16 - (j + 1) ≠ 0))

theorem setup_ok (s : State) :
    WP isa (.block Impl.Argon2.AArch64.ReduceBlock.setup) s (Inv s 0) := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.ReduceBlock.setup, runBlock_cons, runStep_some, runBlock_nil, exec,
    Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, ?_, ?_, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · rw [RegUpd.gpr_write_of_ne (h := by decide)]; exact (BitVec.add_zero _).symm
  · rw [RegUpd.gpr_write_of_ne (h := by decide)]; exact (BitVec.add_zero _).symm
  · intro i hi; exact absurd hi (by omega)
  · exact Frame.refl _ _
  · intro r _ _ _ _ h14
    exact RegUpd.gpr_write_of_ne _ _ _ h14

theorem restore_ok (s : State) :
    WP isa (.block Impl.Argon2.AArch64.ReduceBlock.restore) s fun t =>
      t.gpr .x0 = s.gpr .x0 - 1024 ∧ t.gpr .x1 = s.gpr .x1 - 1024 ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.ReduceBlock.restore, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 1024 < 4096 from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro r h0 h1
  simp only [h0, h1, ite_false]

theorem code_ok (s : State)
    (read : Covers [⟨s.gpr .x1, 1024⟩] (s.rd ++ s.wr))
    (write : Covers [⟨s.gpr .x0, 1024⟩] s.wr)
    (separate : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩) :
    WP isa Impl.Argon2.AArch64.ReduceBlock.code s fun t =>
      blockAt t.mem (s.gpr .x0) = xorBlock (blockAt s.mem (s.gpr .x0)) (blockAt s.mem (s.gpr .x1)) ∧
      Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem ∧ FillWrite.CopyKeeps s t ∧ t.sp = s.sp := by
  unfold Impl.Argon2.AArch64.ReduceBlock.code
  refine WP.seq ((setup_ok s).mono ?_)
  intro a ha
  refine WP.seq ((loop_ok s a ha read write separate).mono ?_)
  intro b hb
  refine (restore_ok b).mono ?_
  rintro t ⟨dst, sr, regs, mem, rd, wr, sp⟩
  refine ⟨?_, ?_, ⟨?_, rd.trans hb.rd, wr.trans hb.wr⟩, sp.trans hb.sp⟩
  · rw [mem, written_block hb.written, R, FillWrite.result]
    exact Proof.Argon2.xorBlock_comm _ _
  · rw [mem]; exact hb.frame
  · intro r h8 h13 h14 _
    by_cases h0 : r = .x0
    · subst h0; rw [dst, hb.dest]; exact BitVec.add_sub_cancel _ _
    by_cases h1 : r = .x1
    · subst h1; rw [sr, hb.src]; exact BitVec.add_sub_cancel _ _
    rw [regs r h0 h1]
    exact hb.regs r h0 h1 h8 h13 h14

end VG.Proof.Argon2.AArch64.ReduceBlock
