module

public import VerifiedGarbage.Impl.Argon2.AArch64.ReductionInit
public import VerifiedGarbage.Proof.Argon2.AArch64.Initialize
public import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitClearMemory
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Argon2.AArch64.ClearBlock
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Argon2.Contract

/-! # Clearing the reduction accumulator in a loop of sixteen-word passes

Each pass stores the zero in `x8` to sixteen words at the advancing pointer
`x0` and counts `x9` down from eight; `x0` is restored after the last pass. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.ReductionClear

open VG VG.AArch64 VG.Spec.Argon2

/-- The stores of one pass: `n` words at the pointer of pass `j`. -/
theorem words_ok (m₀ : Mem) (dest : Addr) (j : Nat) (hj : j < 8) (s : State)
    (write : Covers [⟨dest, 1024⟩] s.wr) (zero : s.gpr .x8 = 0)
    (pd : s.gpr .x0 = off dest (128 * j)) (mem : s.mem = MemoryInit.clearMem m₀ dest (16 * j))
    (n : Nat) (hn : n ≤ 16) :
    WP isa (.block (Impl.Argon2.AArch64.ClearBlock.words n)) s fun t =>
      t.mem = MemoryInit.clearMem m₀ dest (16 * j + n) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction n with
  | zero => exact WP.block_nil ⟨mem, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    simp only [Impl.Argon2.AArch64.ClearBlock.words, List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro a ⟨memA, regs, rd, wr, mx⟩
    have at_ : off (a.gpr .x0) (8 * n) = dest + BitVec.ofNat 64 (8 * (16 * j + n)) := by
      rw [regs, pd]
      exact Offset.add_add_eq dest (by omega)
    have hw : InRegions a.wr (off (a.gpr .x0) (8 * n)) 8 := by
      rw [at_, wr]
      exact write _ _ ⟨⟨dest, 1024⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    refine (ClearBlock.word_ok a n (by omega) hw).mono ?_
    rintro t ⟨memT, regsT, rdT, wrT, mxT⟩
    refine ⟨?_, regsT.trans regs, rdT.trans rd, wrT.trans wr, mxT.trans mx⟩
    rw [memT, at_, memA, regs, zero]
    rfl

theorem setup_ok (s : State) :
    WP isa (.block Impl.Argon2.AArch64.ReductionInit.clearSetup) s fun t =>
      t.gpr .x8 = 0 ∧ t.gpr .x9 = 8 ∧ (∀ r, r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.ReductionInit.clearSetup, runBlock_cons, runStep_some,
    runBlock_nil, exec, Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro r h8 h9
  simp only [h8, h9, ite_false]

theorem advance_ok (s : State) :
    WP isa (.block Impl.Argon2.AArch64.ReductionInit.clearAdvance) s fun t =>
      t.gpr .x0 = s.gpr .x0 + 128 ∧ t.gpr .x9 = s.gpr .x9 - 1 ∧
      (∀ r, r ≠ .x0 → r ≠ .x9 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.ReductionInit.clearAdvance, runBlock_cons, runStep_some,
    runBlock_nil, exec, State.read, Size.bits,
    show 128 < 4096 from by decide, show 1 < 4096 from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro r h0 h9
  simp only [h0, h9, ite_false]

/-- After `j` passes. -/
structure Inv (s₀ : State) (j : Nat) (s : State) : Prop where
  bound : j ≤ 8
  dest : s.gpr .x0 = off (s₀.gpr .x0) (128 * j)
  count : s.gpr .x9 = BitVec.ofNat 64 (8 - j)
  zero : s.gpr .x8 = 0
  mem : s.mem = MemoryInit.clearMem s₀.mem (s₀.gpr .x0) (16 * j)
  regs : ∀ r, r ≠ .x0 → r ≠ .x8 → r ≠ .x9 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem body_ok (s₀ : State) (j : Nat) (hj : j < 8) (s : State) (h : Inv s₀ j s)
    (write : Covers [⟨s₀.gpr .x0, 1024⟩] s₀.wr) :
    WP isa Impl.Argon2.AArch64.ReductionInit.clearBody s (Inv s₀ (j + 1)) := by
  unfold Impl.Argon2.AArch64.ReductionInit.clearBody
  refine WP.seq ((words_ok s₀.mem (s₀.gpr .x0) j hj s (by rw [h.wr]; exact write) h.zero h.dest
    h.mem 16 (Nat.le_refl _)).mono ?_)
  rintro a ⟨memA, regsA, rdA, wrA, spA⟩
  refine (advance_ok a).mono ?_
  rintro t ⟨dst, cnt, regsT, mem, rd, wr, sp⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, rd.trans (rdA.trans h.rd), wr.trans (wrA.trans h.wr),
    sp.trans (spA.trans h.sp)⟩
  · rw [dst, regsA, h.dest, show (128 : Addr) = BitVec.ofNat 64 128 from rfl]
    exact Offset.add_add_eq _ (by omega)
  · rw [cnt, regsA, h.count, show (1 : Addr) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  · rw [regsT .x8 (by decide) (by decide), regsA]; exact h.zero
  · rw [mem, memA, show 16 * (j + 1) = 16 * j + 16 by omega]
  · intro r h0 h8 h9
    rw [regsT r h0 h9, regsA]
    exact h.regs r h0 h8 h9

theorem loop_ok (s₀ : State) (s : State) (h : Inv s₀ 0 s)
    (write : Covers [⟨s₀.gpr .x0, 1024⟩] s₀.wr) :
    WP isa (.loop Impl.Argon2.AArch64.ReductionInit.clearBody (.nonzero .x .x9)) s (Inv s₀ 8) := by
  refine WP.loop (M := isa) (fun k s => ∃ j, k = 8 - j ∧ j < 8 ∧ Inv s₀ j s)
    ?_ 8 s ⟨0, rfl, by decide, h⟩
  rintro k s ⟨j, rfl, hj, h⟩
  refine (body_ok s₀ j hj s h write).mono ?_
  intro t next
  have flag : eval (.nonzero .x .x9) t = some (decide (8 - (j + 1) ≠ 0)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, next.count]
    congr 1
    rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff, ne_eq, ne_eq]
    refine not_congr ⟨fun eq => ?_, fun eq => by rw [eq]; rfl⟩
    have num := congrArg BitVec.toNat eq
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 - (j + 1) < 2 ^ 64),
      show (0 : Addr).toNat = 0 from rfl] using num
  by_cases done : j + 1 = 8
  · refine .inl ⟨?_, done ▸ next⟩
    simpa only [show 8 - (j + 1) = 0 by omega, ne_eq, not_true_eq_false, decide_false] using flag
  · refine .inr ⟨?_, 8 - (j + 1), by omega, j + 1, rfl, by omega, next⟩
    change eval (.nonzero .x .x9) t = some true
    rw [flag]
    exact congrArg some (decide_eq_true (by omega : 8 - (j + 1) ≠ 0))

theorem restore_ok (s : State) :
    WP isa (.block [.subImm .x .x0 .x0 1024]) s fun t =>
      t.gpr .x0 = s.gpr .x0 - 1024 ∧ (∀ r, r ≠ .x0 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 1024 < 4096 from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro r h0
  simp only [h0, ite_false]

/-- The statement of `ClearBlock.code_ok`, for the loop. -/
theorem code_ok (s : State) (write : Covers [⟨s.gpr .x0, 1024⟩] s.wr) :
    WP isa Impl.Argon2.AArch64.ReductionInit.clear s fun t => blockAt t.mem (s.gpr .x0) = zeroBlock ∧
      Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.sp = s.sp := by
  unfold Impl.Argon2.AArch64.ReductionInit.clear
  refine WP.seq ((setup_ok s).mono ?_)
  rintro a ⟨zero, count, regsA, memA, rdA, wrA, spA⟩
  have dest : a.gpr .x0 = s.gpr .x0 := regsA .x0 (by decide) (by decide)
  have ha : Inv a 0 a := ⟨by decide, (BitVec.add_zero _).symm, count, zero, rfl,
    fun _ _ _ _ => rfl, rfl, rfl, rfl⟩
  refine WP.seq ((loop_ok a a ha (by rw [dest, wrA]; exact write)).mono ?_)
  intro b hb
  refine (restore_ok b).mono ?_
  rintro t ⟨dst, regs, mem, rd, wr, sp⟩
  have cleared : t.mem = MemoryInit.clearMem s.mem (s.gpr .x0) 128 := by
    rw [mem, hb.mem, memA, dest]
  refine ⟨?_, ?_, ⟨?_, rd.trans (hb.rd.trans rdA), wr.trans (hb.wr.trans wrA)⟩,
    sp.trans (hb.sp.trans spA)⟩
  · rw [cleared]
    apply Vector.ext
    intro i hi
    change (blockAt _ _)[(⟨i, hi⟩ : Fin 128)] = zeroBlock[(⟨i, hi⟩ : Fin 128)]
    rw [blockAt_get, MemoryInit.clearMem_word _ _ 128 i (by decide) hi]
    simp only [zeroBlock, Fin.getElem_fin, Vector.getElem_replicate]
  · rw [cleared]
    exact MemoryInit.clearMem_frame _ _ 128 (by decide)
  · intro r h8 h9
    by_cases h0 : r = .x0
    · subst h0; rw [dst, hb.dest, dest]; exact BitVec.add_sub_cancel _ _
    rw [regs r h0, hb.regs r h0 h8 h9, regsA r h8 h9]

end VG.Proof.Argon2.AArch64.ReductionClear
