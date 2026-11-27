module

public import VerifiedGarbage.Impl.Argon2.AArch64.FillFinish
public import VerifiedGarbage.Impl.Argon2.AArch64.FillIterations
public import VerifiedGarbage.Impl.Argon2.AArch64.FillIteration
public import VerifiedGarbage.Impl.Argon2.AArch64.FillSlices
public import VerifiedGarbage.Impl.Argon2.AArch64.FillSlice
public import VerifiedGarbage.Impl.Argon2.AArch64.FillLanes
public import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetupPrepare
import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetup
public import VerifiedGarbage.Proof.Argon2.Slices
import VerifiedGarbage.Proof.Argon2.AArch64.Instructions
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Argon2.Serialization
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Impl.Argon2.AArch64.FinalReduction
public import VerifiedGarbage.Proof.Argon2.AArch64.Initialize
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT
import VerifiedGarbage.Proof.Argon2.AArch64.ReduceBlockLit
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Impl.Argon2.AArch64.FinalReduction
meta import VerifiedGarbage.Proof.Argon2.AArch64.Initialize
meta import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT
meta import VerifiedGarbage.Proof.Argon2.AArch64.ReduceBlockLit
meta import VerifiedGarbage.Proof.Argon2.Dimensions
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.Argon2.AArch64.MemoryInit
meta import VerifiedGarbage.Impl.Argon2.AArch64.MemoryInit
meta import VerifiedGarbage.Impl.Argon2.AArch64.FillLanes
meta import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetupPrepare
meta import VerifiedGarbage.Proof.Argon2.AArch64.Instructions
public import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressCall
public import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Backend
public import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Correct
import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Lit
public import VerifiedGarbage.Impl.Argon2.AArch64.FinalOutput
public import VerifiedGarbage.Proof.Argon2.AArch64.ReduceLane
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceCount
meta import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressCall
meta import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Backend
meta import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Correct
meta import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Lit
meta import VerifiedGarbage.Impl.Argon2.AArch64.FinalOutput
meta import VerifiedGarbage.Proof.Argon2.AArch64.ReduceLane
meta import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceCount
public import VerifiedGarbage.Impl.Argon2.AArch64.ReductionInit
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Argon2.AArch64.ReductionInit
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Argon2.Contract

/-! ### `Argon2.AArch64.FinishReady`, which this module and modules that import it used -/

section

/-! ### `Argon2.AArch64.ReductionClear`, which this module and modules that import it used -/

section

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
    refine (ih (by omega_using [hn])).mono ?_
    rintro a ⟨memA, regs, rd, wr, mx⟩
    have at_ : off (a.gpr .x0) (8 * n) = dest + BitVec.ofNat 64 (8 * (16 * j + n)) := by
      rw [regs, pd]
      exact Offset.add_add_eq dest (by omega_using [])
    have hw : InRegions a.wr (off (a.gpr .x0) (8 * n)) 8 := by
      rw [at_, wr]
      exact write _ _ ⟨⟨dest, 1024⟩, by simp, Offset.contains_base _ (by omega_using [hj, hn]) (by omega_using [hj, hn])⟩
    refine (ClearBlock.word_ok a n (by omega_using [hn]) hw).mono ?_
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
  refine ⟨by omega_using [hj], ?_, ?_, ?_, ?_, ?_, rd.trans (rdA.trans h.rd), wr.trans (wrA.trans h.wr),
    sp.trans (spA.trans h.sp)⟩
  · rw [dst, regsA, h.dest, show (128 : Addr) = BitVec.ofNat 64 128 from rfl]
    exact Offset.add_add_eq _ (by omega_using [])
  · rw [cnt, regsA, h.count, show (1 : Addr) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega_using [hj])]
    congr 1
  · rw [regsT .x8 (by decide) (by decide), regsA]; exact h.zero
  · rw [mem, memA, show 16 * (j + 1) = 16 * j + 16 by omega_using []]
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
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [] : 8 - (j + 1) < 2 ^ 64),
      show (0 : Addr).toNat = 0 from rfl] using num
  by_cases done : j + 1 = 8
  · refine .inl ⟨?_, done ▸ next⟩
    simpa only [show 8 - (j + 1) = 0 by omega_using [done], ne_eq, not_true_eq_false, decide_false] using flag
  · refine .inr ⟨?_, 8 - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, done], next⟩
    change eval (.nonzero .x .x9) t = some true
    rw [flag]
    exact congrArg some (decide_eq_true (by omega_using [hj, done] : 8 - (j + 1) ≠ 0))

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

end

end

/-! ### `Argon2.AArch64.ReductionLoopState`, which this module and modules that import it used -/

section

/-! Public loop metadata survives accumulator writes and register-only advancement. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.ReductionState

open VG VG.AArch64 VG.Spec.Argon2

theorem Ready.of_state {p : Params} {s t : State} (h : Ready p s)
    (bp : t.gpr .x19 = s.gpr .x19) (length : t.gpr .x20 = s.gpr .x20)
    (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Ready p t := by
  have base : matrix t = matrix s := by unfold matrix; rw [mem, bp]
  refine ⟨h.positive, h.minimum, h.bound, ?_, ?_, ?_, length.trans h.length⟩
  · rw [rd, wr, bp]; exact h.read
  · rw [base, wr]; exact h.write
  · rw [base, bp]; exact h.frame

theorem Represents.of_state {p : Params} {s t : State} {memory : Array Block} {acc : Block}
    (h : Represents p memory acc s) (bp : t.gpr .x19 = s.gpr .x19) (mem : t.mem = s.mem) :
    Represents p memory acc t := by
  have base : matrix t = matrix s := by unfold matrix; rw [mem, bp]
  constructor
  · rw [mem, base]; exact h.accumulator
  · rw [mem, base]; exact h.last

theorem frame_word {p : Params} {s t : State} {memory : Array Block} {acc : Block}
    (h : Ready p s) (done : ReduceLane.Done s t p memory acc) (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.regs .x19 (by simp [FillCompress.loopRegs])]
  exact done.frame.readW (r := ⟨s.gpr .x19, 272⟩) (Offset.contains_base _ bound (by omega_using [bound]))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact h.frame.symm.sub_right (Region.sub_prefix (by
          have nonempty := Proof.Argon2.lastIndex_bounds p h.positive h.minimum 0 h.positive
          omega_using [nonempty]))) (by decide)

end VG.Proof.Argon2.AArch64.ReductionState

end

end

/-! ### `Argon2.AArch64.FinalOutputReady`, which only this module used -/

section

/-! ### `Argon2.AArch64.FinalCall`, which only this module used -/

section

/-! The final H′ call accepts a complete reduced block and a public tag length. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.FinalCall

open VG VG.AArch64
open VG.Impl.Argon2.AArch64.HPrime (code)
open VG.Spec.Blake2 (bytesAt)

structure CallReady (len : Nat) (s : State) : Prop where
  stackMinimum : 16 ≤ s.sp.toNat
  positive : 1 ≤ len
  bound : len < 2 ^ 32
  input : Covers [⟨s.gpr .x0, 1024⟩] (s.rd ++ s.wr)
  output : Covers [⟨s.gpr .x2, len⟩] s.wr
  work : (⟨s.gpr .x4, 16384⟩ : Region) ∈ s.wr
  inputWork : (⟨s.gpr .x0, 1024⟩ : Region).Disjoint ⟨s.gpr .x4, 16384⟩
  outputWork : (⟨s.gpr .x2, len⟩ : Region).Disjoint ⟨s.gpr .x4, 16384⟩
  stackInput : (below s.sp 16).Disjoint ⟨s.gpr .x0, 1024⟩
  stackOutput : (below s.sp 16).Disjoint ⟨s.gpr .x2, len⟩
  stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x4, 16384⟩

structure Called (len : Nat) (s t : State) : Prop where
  digest : bytesAt t.mem (s.gpr .x2) len = Spec.Argon2.hPrime len (bytesAt s.mem (s.gpr .x0) 1024)
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .x2, len⟩, ⟨s.gpr .x4, 16384⟩, below s.sp 16] s.mem t.mem

theorem hPrime_call_hyps (len : Nat) (s : State) (h : CallReady len s)
    (inputLength : s.gpr .x1 = 1024) (outputLength : s.gpr .x3 = BitVec.ofNat 64 len) :
    HPrime.localContract.pre (s.callEntry.withRegions [⟨s.gpr .x0, 1024⟩]
      [⟨s.gpr .x2, len⟩, ⟨s.gpr .x4, 16384⟩]) ∧
    Covers [⟨s.gpr .x0, 1024⟩, ⟨s.gpr .x2, len⟩, ⟨s.gpr .x4, 16384⟩] (s.rd ++ s.wr) ∧
    Covers [⟨s.gpr .x2, len⟩, ⟨s.gpr .x4, 16384⟩] s.wr := by
  have length : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.bound (by decide))]
  have g : ∀ r, r ∉ linkRegs → s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr s hr
  refine ⟨?_, ?_, ?_⟩
  · simp only [HPrime.localContract, HPrime.inputR, HPrime.outputR, HPrime.workR,
      HPrime.stackR, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp,
      g _ (by decide : Reg.x0 ∉ linkRegs), g _ (by decide : Reg.x1 ∉ linkRegs),
      g _ (by decide : Reg.x2 ∉ linkRegs), g _ (by decide : Reg.x3 ∉ linkRegs),
      g _ (by decide : Reg.x4 ∉ linkRegs), State.callEntry_sp,
      inputLength, outputLength, length]
    exact ⟨rfl, trivial, by decide, h.positive, h.bound, h.stackMinimum,
      h.inputWork, h.outputWork, h.stackInput, h.stackOutput, h.stackWork⟩
  · intro p n hp
    rcases hp with ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.input p n ⟨_, List.mem_singleton_self _, hc⟩
    · obtain ⟨r, hr, hc⟩ := h.output p n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · exact ⟨_, List.mem_append_right _ h.work, hc⟩
  · intro p n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.output p n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, h.work, hc⟩

theorem hPrime_depth (v : HPrime.Backend) : (code v.hash).aarch64Depth = 1 := by
  simp only [code, Impl.Argon2.AArch64.HPrime.first,
    Impl.Argon2.AArch64.HPrime.chooseLength, Impl.Argon2.AArch64.HPrime.init,
    Impl.Argon2.AArch64.HPrime.absorbFixed, Impl.Argon2.AArch64.HPrime.update,
    Impl.Argon2.AArch64.HPrime.absorbInput, Impl.Argon2.AArch64.HPrime.finishInput,
    Impl.Argon2.AArch64.HPrime.finalize, Impl.Argon2.AArch64.HPrime.finishOutput,
    Impl.Argon2.AArch64.HPrime.extendDigest, Impl.Argon2.AArch64.HPrime.emitPrefix,
    Impl.Argon2.AArch64.HPrime.copy, Impl.Argon2.AArch64.HPrime.chain,
    Impl.Argon2.AArch64.HPrime.next, Impl.Argon2.AArch64.HPrime.copyRemaining,
    Code.aarch64Depth, v.ok.initDepth, v.ok.updateDepth, v.ok.finalizeDepth]
  rfl

theorem hPrime_call_ok (v : HPrime.Backend) (name : String)
    (len : Nat) (s : State) (h : CallReady len s) (inputLength : s.gpr .x1 = 1024)
    (outputLength : s.gpr .x3 = BitVec.ofNat 64 len) :
    WP isa (.call name (code v.hash)) s (Called len s) := by
  obtain ⟨pre, cover, writes⟩ := hPrime_call_hyps len s h inputLength outputLength
  refine WP.callF (k := HPrime.localContract) (HPrime.code_correct v) pre cover writes ?_
    (by rw [hPrime_depth]; decide)
  intro t rd wr sp frame regs digest
  change bytesAt t.mem (s.callEntry.gpr .x2) (s.callEntry.gpr .x3).toNat =
    Spec.Argon2.hPrime (s.callEntry.gpr .x3).toNat
      (bytesAt s.mem (s.callEntry.gpr .x0) (s.callEntry.gpr .x1).toNat) at digest
  rw [State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), inputLength, outputLength,
    show (1024 : Addr).toNat = 1024 from rfl,
    show (BitVec.ofNat 64 len).toNat = len from by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.bound (by decide))]] at digest
  refine ⟨digest, ?_, sp, rd, wr, ?_⟩
  · intro r hr
    have preserved : r ∈ VG.AArch64.preserved ∧ r ≠ .x30 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact regs r preserved.1 preserved.2
  · simpa only [hPrime_depth, Nat.mul_one, List.cons_append, List.nil_append] using frame

end VG.Proof.Argon2.AArch64.FinalCall

end

end


/-! Merged from `Proof.Argon2.AArch64.FinalOutputArgs`. -/

@[expose] public section

section
/-! Load the public final-call pointers and tag length from the enclosing frame. -/

namespace VG.Proof.Argon2.AArch64.FinalOutput

open VG VG.AArch64 VG.Spec.Argon2

def output (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 256) 64

def work (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 248) 64

def changed : List Reg := [.x0, .x1, .x2, .x3, .x4]

structure Arguments (s t : State) : Prop where
  input : t.gpr .x0 = ReductionState.matrix s
  inputLength : t.gpr .x1 = 1024
  output : t.gpr .x2 = output s
  outputLength : t.gpr .x3 = s.mem.readW (off (s.gpr .x19) 264) 64
  work : t.gpr .x4 = work s
  keeps : Divide.Keeps changed s t

theorem args_ok (s : State) (read : ∀ d ∈ [232, 256, 264, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8) :
    WP isa (.block Impl.Argon2.AArch64.FinalOutput.args) s (Arguments s) := by
  have input := read 232 (by simp)
  have out := read 256 (by simp)
  have len := read 264 (by simp)
  have scratch := read 248 (by simp)
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.FinalOutput.args,
    Impl.Argon2.AArch64.Instructions.load, Impl.Argon2.AArch64.Instructions.imm,
    show 1024 < 65536 from by decide, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.load, addr, Size.bytes, Size.bits,
    show 232 % 8 = 0 ∧ 232 < 4096 * 8 from by decide,
    show 256 % 8 = 0 ∧ 256 < 4096 * 8 from by decide,
    show 264 % 8 = 0 ∧ 264 < 4096 * 8 from by decide,
    show 248 % 8 = 0 ∧ 248 < 4096 * 8 from by decide, and_self,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (1024#16).setWidth 64 = 1024#64 from rfl,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    input, out, len, scratch, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · constructor
    · intro r hr
      simp only [changed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
    all_goals rfl

theorem Arguments.regs {s t : State} (h : Arguments s t) (r : Reg) (hr : r ∈ FillCompress.loopRegs) : t.gpr r = s.gpr r := by
  have unchanged : r ∉ changed := by
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact h.keeps.regs r unchanged

end VG.Proof.Argon2.AArch64.FinalOutput
end

/-! Final output uses matrix block zero and the original disjoint hash scratch allocation. -/

namespace VG.Proof.Argon2.AArch64.FinalOutput

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  stackMinimum : 16 ≤ s.sp.toNat
  positive : 1 ≤ p.tagLen
  bound : p.tagLen < 2 ^ 32
  reads : ∀ d ∈ [232, 256, 264, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  tagWord : s.mem.readW (off (s.gpr .x19) 264) 64 = BitVec.ofNat 64 p.tagLen
  input : Covers [⟨ReductionState.matrix s, 1024⟩] (s.rd ++ s.wr)
  outputWrite : Covers [⟨output s, p.tagLen⟩] s.wr
  workWrite : (⟨work s, 16384⟩ : Region) ∈ s.wr
  inputWork : (⟨ReductionState.matrix s, 1024⟩ : Region).Disjoint ⟨work s, 16384⟩
  outputWork : (⟨output s, p.tagLen⟩ : Region).Disjoint ⟨work s, 16384⟩
  stackInput : (below s.sp 16).Disjoint ⟨ReductionState.matrix s, 1024⟩
  stackOutput : (below s.sp 16).Disjoint ⟨output s, p.tagLen⟩
  stackWork : (below s.sp 16).Disjoint ⟨work s, 16384⟩

theorem Arguments.ready {p : Params} {s t : State} (h : Ready p s) (a : Arguments s t) :
    FinalCall.CallReady p.tagLen t := by
  have sp := a.keeps.sp
  constructor
  · rw [sp]; exact h.stackMinimum
  · exact h.positive
  · exact h.bound
  · rw [a.input, a.keeps.rd, a.keeps.wr]; exact h.input
  · rw [a.output, a.keeps.wr]; exact h.outputWrite
  · rw [a.work, a.keeps.wr]; exact h.workWrite
  · rw [a.input, a.work]; exact h.inputWork
  · rw [a.output, a.work]; exact h.outputWork
  · rw [a.input, sp]; exact h.stackInput
  · rw [a.output, sp]; exact h.stackOutput
  · rw [a.work, sp]; exact h.stackWork

end VG.Proof.Argon2.AArch64.FinalOutput

end

end

/-! ### `Argon2.AArch64.FillLaneAdvance`, which this module and modules that import it used -/

section

/-! Lane advancement retains the allocation and public segment parameters. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.FillLanes

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillLanes

theorem advance_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 184) 8)
    (ha : (s.gpr .x24 + 1).toNat < 2 ^ 63)
    (hb : (s.mem.readW (off (s.gpr .x19) 184) 64).toNat < 2 ^ 63) :
    WP isa (.block advance) s fun t => t.gpr .x24 = s.gpr .x24 + 1 ∧
      eval (.nonzero .x .x14) t = some (decide ((s.gpr .x24 + 1).toNat <
        (s.mem.readW (off (s.gpr .x19) 184) 64).toNat)) ∧
      Divide.Keeps [.x24, .x12, .x13, .x14, .x15] s t := by
  simp only [advance, List.flatten_cons, List.flatten_nil, List.append_nil]
  apply WP.block_append
  refine (Instructions.addi_ok s .x24 1 (by decide) (by decide) (by decide)).mono ?_
  rintro u ⟨value, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have read : InRegions (u.rd ++ u.wr) (off (u.gpr .x19) 184) 8 := by
    rw [keeps.rd, keeps.wr, bp]; exact hr
  have left : (u.gpr .x24).toNat < 2 ^ 63 := by rw [value]; exact ha
  have right : (u.mem.readW (off (u.gpr .x19) 184) 64).toNat < 2 ^ 63 := by
    rw [keeps.mem, bp]; exact hb
  refine (Instructions.comparem_ok u .x24 .x19 184 (by decide) (by decide) (by decide)
    read left right).mono ?_
  rintro t ⟨flag, changed⟩
  refine ⟨(changed.regs .x24 (by decide)).trans value, ?_,
    (keeps.mono (by decide)).trans (changed.mono (by decide))⟩
  rw [flag, value, keeps.mem, bp]
  rfl

theorem context_ready {p : Params} {pass lane slice index old : Nat} {s : State}
    (h : FillContext.Ready p pass lane slice index old s) : SegmentSetup.Ready p pass lane slice s :=
  ⟨h.parameters, h.layout, h.cache.layout, h.cache.reads, h.cache.write, ⟨old, h.cache.words⟩,
    h.matrixWork, h.position.laneLength, h.position.segmentLength, h.lanesWord⟩

theorem finished_ready {p : Params} {pass lane slice : Nat} {s t : State} {state : FillState}
    (parameters : FillContext.Parameters p pass lane slice) (h : FillSegment.Finished s t p pass lane slice state) :
    SegmentSetup.Ready p pass lane slice t := by
  obtain ⟨old, context⟩ := FillContext.finished_context parameters h
  exact context_ready context

theorem change_lane_ready {p : Params} {pass lane slice newLane : Nat} {s t : State}
    (h : SegmentSetup.Ready p pass lane slice s) (k : Divide.Keeps [.x24, .x12, .x13, .x14, .x15] s t)
    (value : t.gpr .x24 = BitVec.ofNat 64 newLane) (active : newLane < p.lanes) :
    SegmentSetup.Ready p pass newLane slice t := by
  have bp := k.regs .x19 (by decide)
  have sp := k.sp
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [k.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [k.mem, bp]
  refine ⟨{ h.parameters with laneBound := active }, h.layout.of_preserved bp sp base work k.rd k.wr,
    ?_, ?_, ?_, ?_, ?_, (k.regs .x20 (by decide)).trans h.laneLength,
    (k.regs .x21 (by decide)).trans h.segmentLength, ?_⟩
  · constructor
    · rw [k.rd, k.wr, bp]; exact h.addressLayout.frameRead
    · rw [k.wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [k.rd, k.wr, bp]; exact h.reads
  · rw [k.wr, bp]; exact h.write
  · obtain ⟨old, words⟩ := h.words
    refine ⟨old, ?_, value, (k.regs .x22 (by decide)).trans words.sliceWord, ?_, ?_, ?_, ?_⟩
    all_goals rw [k.mem, bp]
    · exact words.passWord
    · exact words.blocksWord
    · exact words.passesWord
    · exact words.variantWord
    · exact words.counterWord
  · rw [base, work]; exact h.matrixWork
  · rw [k.mem, bp]; exact h.lanesWord

end VG.Proof.Argon2.AArch64.FillLanes

end

end

/-! Merged from `Proof.Argon2.AArch64.ReduceLanesBody`. -/

@[expose] public section

section
/-! One reduction iteration advances a public lane and preserves the accumulator invariant. -/

namespace VG.Proof.Argon2.AArch64.ReduceLanes

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Ready (p : Params) (lane : Nat) (s : State) : Prop where
  allocation : ReductionState.Ready p s
  active : lane < p.lanes
  lanesBound : p.lanes < 2 ^ 32
  laneWord : s.gpr .x24 = BitVec.ofNat 64 lane
  lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 184) 8
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

structure Done (s t : State) (p : Params) (lane : Nat) (memory : Array Block) (acc : Block) : Prop where
  represented : ReductionState.Represents p memory acc t
  base : matrix t = matrix s
  laneWord : t.gpr .x24 = BitVec.ofNat 64 (lane + 1)
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  sp : t.sp = s.sp
  cf : eval (.nonzero .x .x14) t = some (decide (lane + 1 < p.lanes))
  next : lane + 1 < p.lanes → Ready p (lane + 1) t

theorem body_ok (s : State) (p : Params) (lane : Nat) (h : Ready p lane s)
    (memory : Array Block) (acc : Block) (represented : ReductionState.Represents p memory acc s) :
    WP isa Impl.Argon2.AArch64.ReduceLanes.body s
      (Done s · p lane memory (xorBlock acc (memory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock))) := by
  unfold Impl.Argon2.AArch64.ReduceLanes.body Impl.Argon2.AArch64.ReduceLanes.advance
  refine WP.seq ((ReduceLane.code_ok s p lane h.allocation h.active h.laneWord memory acc represented).mono ?_)
  intro a reduced
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) 184) 8 := by
    rw [reduced.rd, reduced.wr, reduced.regs .x19 (by simp [FillCompress.loopRegs])]; exact h.lanesRead
  have word := (ReductionState.frame_word h.allocation reduced 184 (by decide)).trans h.lanesWord
  have added : a.gpr .x24 + 1 = BitVec.ofNat 64 (lane + 1) := by
    rw [reduced.regs .x24 (by simp [FillCompress.loopRegs]), h.laneWord, BitVec.ofNat_add]; rfl
  have laneBound := h.active
  have lanesBound := h.lanesBound
  have left : (a.gpr .x24 + 1).toNat < 2 ^ 63 := by
    rw [added, ReferenceMap.word_nat (lane + 1) (by omega_using [laneBound, lanesBound])]; omega_using [laneBound, lanesBound]
  have right : (a.mem.readW (off (a.gpr .x19) 184) 64).toNat < 2 ^ 63 := by
    rw [word, ReferenceMap.word_nat p.lanes (by omega_using [lanesBound])]; omega_using [lanesBound]
  refine (FillLanes.advance_ok a read left right).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have base : matrix t = matrix a := by unfold matrix; rw [keeps.mem, bp]
  have nextWord := value.trans added
  refine ⟨reduced.represented.of_state bp keeps.mem, base.trans reduced.base, nextWord,
    ?_, keeps.rd.trans reduced.rd, keeps.wr.trans reduced.wr, ?_, keeps.sp.trans reduced.sp, ?_, ?_⟩
  · intro r hr bx
    have outside : r ∉ [Reg.x24, .x12, .x13, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    exact (keeps.regs r outside).trans (reduced.regs r hr)
  · rw [keeps.mem]; exact reduced.frame
  · rw [flag, added, word, ReferenceMap.word_nat (lane + 1) (by have bound := h.lanesBound; have active := h.active; omega_using [laneBound, lanesBound]),
      ReferenceMap.word_nat p.lanes (Nat.lt_trans h.lanesBound (by decide))]
  · intro active
    refine ⟨reduced.ready.of_state bp (keeps.regs .x20 (by decide)) keeps.mem keeps.rd keeps.wr,
      active, h.lanesBound, nextWord, ?_, ?_⟩
    · rw [keeps.rd, keeps.wr, bp]; exact read
    · rw [keeps.mem, bp]; exact word

end VG.Proof.Argon2.AArch64.ReduceLanes
end

/-! Merged from `Proof.Argon2.AArch64.ReductionInit`. -/
section
/-! Merged from `Proof.Argon2.AArch64.ReductionClear`. -/
section
/-! Clear only block zero, preserving the original last blocks in the matrix. -/

namespace VG.Proof.Argon2.AArch64.ReductionState

open VG VG.AArch64 VG.Spec.Argon2

structure Cleared (s t : State) (p : Params) (memory : Array Block) : Prop where
  ready : Ready p t
  represented : Represents p memory zeroBlock t
  base : matrix t = matrix s
  keeps : CopyKeeps s t
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem clear_ok (s : State) (p : Params) (h : Ready p s)
    (dest : s.gpr .x0 = matrix s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa Impl.Argon2.AArch64.ReductionInit.clear s (Cleared s · p memory) := by
  have write : Covers [⟨s.gpr .x0, 1024⟩] s.wr := by rw [dest]; exact h.accumulator_cover
  refine (ReductionClear.code_ok s write).mono ?_
  rintro t ⟨zero, frame, keeps, mx⟩
  rw [dest] at frame zero
  have bp := keeps.1 .x19 (by decide) (by decide)
  have nonempty := Proof.Argon2.lastIndex_bounds p h.positive h.minimum 0 h.positive
  have metadata (d : Nat) (bound : d + 8 ≤ 272) :
      t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
    rw [bp]
    exact frame.readW (r := ⟨s.gpr .x19, 272⟩) (Offset.contains_base _ bound (by omega_using [bound]))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact h.frame.symm.sub_right (Region.sub_prefix (by omega_using [nonempty]))) (by decide)
  have base : matrix t = matrix s := metadata 232 (by decide)
  refine ⟨?_, ?_, base, keeps, frame, mx⟩
  · refine ⟨h.positive, h.minimum, h.bound, ?_, ?_, ?_, (keeps.1 .x20 (by decide) (by decide)).trans h.length⟩
    · rw [keeps.2.1, keeps.2.2, bp]; exact h.read
    · rw [base, keeps.2.2]; exact h.write
    · rw [base, bp]; exact h.frame
  · constructor
    · rw [base]; exact zero
    · intro lane active
      rw [base]
      apply Eq.trans _ (represented.block _ (Proof.Argon2.lastIndex_bounds p h.positive h.minimum lane active).2)
      apply FillCompress.block_frame frame
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      have bounds := Proof.Argon2.lastIndex_bounds p h.positive h.minimum lane active
      simpa only [Proof.Argon2.matrixCell, Nat.zero_mul, BitVec.add_zero] using
        Proof.Argon2.matrixCell_disjoint (matrix s) p.blocks (Proof.Argon2.lastIndex p lane) 0 h.bound
          bounds.2 (by omega_using [nonempty]) (by omega_using [bounds])

theorem Cleared.frame_word {p : Params} {s t : State} {memory : Array Block}
    (ready : Ready p s) (done : Cleared s t p memory) (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.keeps.1 .x19 (by decide) (by decide)]
  exact done.frame.readW (r := ⟨s.gpr .x19, 272⟩) (Offset.contains_base _ bound (by omega_using [bound]))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ready.frame.symm.sub_right (Region.sub_prefix (by
          have nonempty := Proof.Argon2.lastIndex_bounds p ready.positive ready.minimum 0 ready.positive
          omega_using [nonempty]))) (by decide)

end VG.Proof.Argon2.AArch64.ReductionState
end

/-! Merged from `Proof.Argon2.AArch64.ReduceLanes`. -/
section
/-! Termination and correctness of the final lane reduction. -/

namespace VG.Proof.Argon2.AArch64.ReduceLanes

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Finished (s t : State) (p : Params) (memory : Array Block) (acc : Block) : Prop where
  represented : ReductionState.Represents p memory acc t
  base : matrix t = matrix s
  laneWord : t.gpr .x24 = BitVec.ofNat 64 p.lanes
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → t.gpr r = s.gpr r

theorem Done.finished {s t : State} {p : Params} {lane : Nat} {memory : Array Block} {acc : Block}
    (h : Done s t p lane memory acc) (last : lane + 1 = p.lanes) : Finished s t p memory acc :=
  ⟨h.represented, h.base, last ▸ h.laneWord, h.rd, h.wr, h.frame, h.sp, h.regs⟩

theorem Finished.prepend {s a t : State} {p : Params} {lane : Nat} {memory : Array Block} {acc result : Block}
    (first : Done s a p lane memory acc) (rest : Finished a t p memory result) : Finished s t p memory result := by
  refine ⟨rest.represented, rest.base.trans first.base, rest.laneWord,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.sp.trans first.sp, ?_⟩
  · have frame := rest.frame
    rw [first.base] at frame
    exact first.frame.trans frame
  · intro r hr bx; exact (rest.regs r hr bx).trans (first.regs r hr bx)

theorem loop_ok (count : Nat) (s : State) (p : Params) (lane : Nat) (h : Ready p lane s)
    (memory : Array Block) (acc : Block) (represented : ReductionState.Represents p memory acc s)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    WP isa Impl.Argon2.AArch64.ReduceLanes.loop s
      (Finished s · p memory (Proof.Argon2.reduction p memory lane count acc)) := by
  induction count generalizing s lane acc with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := body_ok s p lane h memory acc represented
    rw [Proof.Argon2.reduction_succ]
    cases n with
    | zero =>
      have last : lane + 1 = p.lanes := endLane
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : lane + 1 < p.lanes := by omega_using [endLane]
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (lane + 1) (done.next active) _
        done.represented (by omega_using []) (by omega_using [endLane])
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [done.cf, active, decide_true]

end VG.Proof.Argon2.AArch64.ReduceLanes
end

/-! Establish the invariant for reducing all lanes, retaining the input matrix's last blocks. -/

namespace VG.Proof.Argon2.AArch64.ReductionInit

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Ready (p : Params) (s : State) : Prop where
  allocation : ReductionState.Ready p s
  lanesBound : p.lanes < 2 ^ 32
  lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 184) 8
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

theorem setup_ok (s : State) (read : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 232) 8) :
    WP isa (.block Impl.Argon2.AArch64.ReductionInit.setup) s fun t =>
      t.gpr .x0 = matrix s ∧ t.gpr .x24 = 0 ∧ Divide.Keeps [.x0, .x24] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.ReductionInit.setup,
    Impl.Argon2.AArch64.Instructions.load, Impl.Argon2.AArch64.Instructions.imm,
    show 0 < 65536 from by decide, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.load, addr, Size.bytes, Size.bits,
    show 232 % 8 = 0 ∧ 232 < 4096 * 8 from by decide, and_self,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (0#16).setWidth 64 = 0#64 from rfl, read, RegUpd.gpr_write,
    reduceCtorEq, ite_false, ite_true, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

structure Prepared (s t : State) (p : Params) (memory : Array Block) : Prop where
  ready : ReduceLanes.Ready p 0 t
  represented : ReductionState.Represents p memory zeroBlock t
  base : matrix t = matrix s
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem code_ok (s : State) (p : Params) (h : Ready p s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa Impl.Argon2.AArch64.ReductionInit.code s (Prepared s · p memory) := by
  unfold Impl.Argon2.AArch64.ReductionInit.code
  refine WP.seq ((setup_ok s h.allocation.read).mono ?_)
  rintro a ⟨dest, lane, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have base : matrix a = matrix s := by unfold matrix; rw [keeps.mem, bp]
  have ha := h.allocation.of_state bp (keeps.regs .x20 (by decide)) keeps.mem keeps.rd keeps.wr
  have rep : Proof.Argon2.Represents a.mem (matrix a) p.blocks memory := by rw [keeps.mem, base]; exact represented
  refine (ReductionState.clear_ok a p ha (dest.trans base.symm) memory rep).mono ?_
  intro t cleared
  refine ⟨⟨cleared.ready, ha.positive, h.lanesBound,
    (cleared.keeps.1 .x24 (by decide) (by decide)).trans lane, ?_, ?_⟩,
    cleared.represented, cleared.base.trans base, ?_, cleared.keeps.2.1.trans keeps.rd,
    cleared.keeps.2.2.trans keeps.wr, ?_, cleared.sp.trans keeps.sp⟩
  · rw [cleared.keeps.2.1, cleared.keeps.2.2, cleared.keeps.1 .x19 (by decide) (by decide), keeps.rd, keeps.wr, bp]
    exact h.lanesRead
  · rw [cleared.frame_word ha 184 (by decide), keeps.mem, bp]; exact h.lanesWord
  · intro r hr bx
    have ne : r ≠ .x8 ∧ r ≠ .x9 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have notDest : r ≠ .x0 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (cleared.keeps.1 r ne.1 ne.2).trans (keeps.regs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨notDest, bx⟩))
  · have frame := cleared.frame
    rw [base, keeps.mem] at frame; exact frame

end VG.Proof.Argon2.AArch64.ReductionInit
end

/-! Merged from `Proof.Argon2.AArch64.ReductionInitCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.ReducePointersCT`. -/
section
/-! Pointer preparation reads one public frame location and performs fixed arithmetic. -/

namespace VG.Proof.Argon2.AArch64.ReducePointers

open VG VG.AArch64

theorem code_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    Impl.Argon2.AArch64.ReducePointers.code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

end VG.Proof.Argon2.AArch64.ReducePointers
end

/-! Merged from `Proof.Argon2.AArch64.ReduceLanesCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.ReduceLanesBodyCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.ReduceLaneCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.ReduceBlockCT`. -/
section
/-! Final block XOR has fixed accesses determined only by its public pointers. -/

namespace VG.Proof.Argon2.AArch64.ReduceBlock

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReduceBlock

theorem code_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x0, .x1], s.gpr r = t.gpr r)
    code (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x0, .x1])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Argon2.AArch64.ReduceBlock
end

/-! Final lane reduction depends only on public lane coordinates and matrix pointers. -/

namespace VG.Proof.Argon2.AArch64.ReduceLane

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (lane : Nat) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  active : lane < p.lanes
  leftLane : s.gpr .x24 = BitVec.ofNat 64 lane
  rightLane : t.gpr .x24 = BitVec.ofNat 64 lane
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : matrix s = matrix t

theorem pointers_rel (p : Params) (lane : Nat) :
    RelCT isa (Related p lane) Impl.Argon2.AArch64.ReducePointers.code
      (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x0, .x1], s.gpr r = t.gpr r) := by
  have trace := ReducePointers.code_rel.mono (P' := Related p lane) (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => by
    have q : 0 < p.laneLen := by
      have eq := Proof.Argon2.laneLen_segments p h.left.positive
      have minimum := h.left.minimum
      omega_using [eq, minimum]
    exact ⟨ReducePointers.code_ok s lane p.laneLen q h.left.read h.leftLane h.left.length,
      ReducePointers.code_ok t lane p.laneLen q h.right.read h.rightLane h.right.length⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨sp, s, t, hp, ⟨destA, srcA, _⟩, ⟨destB, srcB, _⟩⟩ := h
  refine ⟨sp, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact destA.trans (hp.matrices.trans destB.symm)
  · have bases : s.mem.readW (off (s.gpr .x19) 232) 64 = t.mem.readW (off (t.gpr .x19) 232) 64 := hp.matrices
    rw [srcA, srcB, bases]

theorem code_rel (p : Params) (lane : Nat) :
    RelCT isa (Related p lane) Impl.Argon2.AArch64.ReduceLane.code (fun _ _ => True) :=
  (pointers_rel p lane).seq ReduceBlock.code_rel

end VG.Proof.Argon2.AArch64.ReduceLane
end

/-! Reduction visits the same last blocks even when their contents differ. -/

namespace VG.Proof.Argon2.AArch64.ReduceLanes

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (lane : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block)
    (s t : State) : Prop where
  left : Ready p lane s
  right : Ready p lane t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : matrix s = matrix t
  leftRep : ReductionState.Represents p leftMemory leftAcc s
  rightRep : ReductionState.Represents p rightMemory rightAcc t

theorem advance_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block Impl.Argon2.AArch64.ReduceLanes.advance) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem body_rel (p : Params) (lane : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block) :
    RelCT isa (Related p lane leftMemory rightMemory leftAcc rightAcc) Impl.Argon2.AArch64.ReduceLanes.body
      (fun s t => eval (.nonzero .x .x14) s = eval (.nonzero .x .x14) t ∧ (lane + 1 < p.lanes → Related p (lane + 1) leftMemory rightMemory
        (xorBlock leftAcc (leftMemory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock))
        (xorBlock rightAcc (rightMemory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock)) s t)) := by
  intro s t ts tt a b hp ea eb
  have related : ReduceLane.Related p lane s t :=
    ⟨hp.left.allocation, hp.right.allocation, hp.left.active, hp.left.laneWord, hp.right.laneWord, hp.bases, hp.stacks, hp.matrices⟩
  cases ea with
  | seq reduceA advanceA =>
    cases eb with
    | seq reduceB advanceB =>
      obtain ⟨reduceTrace, _⟩ := ReduceLane.code_rel p lane _ _ _ _ _ _ related reduceA reduceB
      obtain ⟨_, sa, runA, reducedA⟩ := ReduceLane.code_ok s p lane hp.left.allocation hp.left.active
        hp.left.laneWord leftMemory leftAcc hp.leftRep
      obtain ⟨_, sb, runB, reducedB⟩ := ReduceLane.code_ok t p lane hp.right.allocation hp.right.active
        hp.right.laneWord rightMemory rightAcc hp.rightRep
      obtain ⟨_, rfl⟩ := Exec.det reduceA runA
      obtain ⟨_, rfl⟩ := Exec.det reduceB runB
      have bases := (reducedA.regs .x19 (by simp [FillCompress.loopRegs])).trans
        (hp.bases.trans (reducedB.regs .x19 (by simp [FillCompress.loopRegs])).symm)
      have stacks := reducedA.sp.trans (hp.stacks.trans reducedB.sp.symm)
      obtain ⟨advanceTrace, _⟩ := advance_rel _ _ _ _ _ _ ⟨bases, stacks⟩ advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := body_ok s p lane hp.left leftMemory leftAcc hp.leftRep
      obtain ⟨_, b', runB, doneB⟩ := body_ok t p lane hp.right rightMemory rightAcc hp.rightRep
      obtain ⟨_, rfl⟩ := Exec.det (.seq reduceA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq reduceB advanceB) runB
      refine ⟨by rw [reduceTrace, advanceTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨doneA.next active, doneB.next active, ?_, doneA.sp.trans (hp.stacks.trans doneB.sp.symm),
        doneA.base.trans (hp.matrices.trans doneB.base.symm), doneA.represented, doneB.represented⟩
      exact (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).trans
        (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).symm)

end VG.Proof.Argon2.AArch64.ReduceLanes
end

/-! The final reduction leaks only public matrix addresses and the public lane count. -/

namespace VG.Proof.Argon2.AArch64.ReduceLanes

open VG VG.AArch64 VG.Spec.Argon2

theorem loop_rel (p : Params) (lane count : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    RelCT isa (Related p lane leftMemory rightMemory leftAcc rightAcc) Impl.Argon2.AArch64.ReduceLanes.loop
      (fun _ _ => True) := by
  let I := fun n s t => ∃ (lane : Nat) (leftAcc rightAcc : Block), lane + n = p.lanes ∧ 0 < n ∧
    Related p lane leftMemory rightMemory leftAcc rightAcc s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.AArch64.ReduceLanes.body fun s t =>
      isa.eval (.nonzero .x .x14) s = isa.eval (.nonzero .x .x14) t ∧ (isa.eval (.nonzero .x .x14) s = some false → True) ∧
        (isa.eval (.nonzero .x .x14) s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, la, ra, endLane, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨trace, flags, next⟩ := body_rel p j leftMemory rightMemory la ra _ _ _ _ _ _ hp ea eb
      obtain ⟨_, a', runA, done⟩ := body_ok s p j hp.left leftMemory la hp.leftRep
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · exact flags
      · intro taken
        have active : j + 1 < p.lanes := by
          simp only [done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        exact ⟨n, by omega_using [], j + 1, _, _, by omega_using [endLane], by omega_using [endLane, active], next active⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨lane, leftAcc, rightAcc, endLane, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.ReduceLanes
end

/-! Clearing the accumulator follows public pointers and visits a fixed block. -/

namespace VG.Proof.Argon2.AArch64.ReductionInit

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (leftMemory rightMemory : Array Block) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : matrix s = matrix t
  leftMatrix : Proof.Argon2.Represents s.mem (matrix s) p.blocks leftMemory
  rightMatrix : Proof.Argon2.Represents t.mem (matrix t) p.blocks rightMemory

theorem setup_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block Impl.Argon2.AArch64.ReductionInit.setup) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem clear_rel : RelCT isa (fun s t => s.gpr .x0 = t.gpr .x0 ∧ s.sp = t.sp)
    Impl.Argon2.AArch64.ReductionInit.clear (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x0])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem code_rel (p : Params) (leftMemory rightMemory : Array Block) :
    RelCT isa (Related p leftMemory rightMemory) Impl.Argon2.AArch64.ReductionInit.code
      (ReduceLanes.Related p 0 leftMemory rightMemory zeroBlock zeroBlock) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq setupA clearA =>
    cases eb with
    | seq setupB clearB =>
      obtain ⟨setupTrace, setupSp⟩ := setup_rel _ _ _ _ _ _ ⟨hp.bases, hp.stacks⟩ setupA setupB
      obtain ⟨_, sa, runA, destA, _, _⟩ := setup_ok s hp.left.allocation.read
      obtain ⟨_, sb, runB, destB, _, _⟩ := setup_ok t hp.right.allocation.read
      obtain ⟨_, rfl⟩ := Exec.det setupA runA
      obtain ⟨_, rfl⟩ := Exec.det setupB runB
      obtain ⟨clearTrace, _⟩ := clear_rel _ _ _ _ _ _ ⟨destA.trans (hp.matrices.trans destB.symm), setupSp⟩ clearA clearB
      obtain ⟨_, a', runA, doneA⟩ := code_ok s p hp.left leftMemory hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := code_ok t p hp.right rightMemory hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq setupA clearA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq setupB clearB) runB
      refine ⟨by rw [setupTrace, clearTrace], doneA.ready, doneB.ready, ?_, doneA.sp.trans (hp.stacks.trans doneB.sp.symm),
        doneA.base.trans (hp.matrices.trans doneB.base.symm), doneA.represented, doneB.represented⟩
      exact (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).trans
        (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).symm)

end VG.Proof.Argon2.AArch64.ReductionInit
end

/-! Merged from `Proof.Argon2.AArch64.FinalReduction`. -/
section
/-! Complete final block reduction, including setup, termination and a public trace. -/

namespace VG.Proof.Argon2.AArch64.FinalReduction

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

theorem code_ok (s : State) (p : Params) (h : ReductionInit.Ready p s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa Impl.Argon2.AArch64.FinalReduction.code s
      (ReduceLanes.Finished s · p memory (Proof.Argon2.reduction p memory 0 p.lanes zeroBlock)) := by
  unfold Impl.Argon2.AArch64.FinalReduction.code
  refine WP.seq ((ReductionInit.code_ok s p h memory represented).mono ?_)
  intro a prepared
  refine (ReduceLanes.loop_ok p.lanes a p 0 prepared.ready memory zeroBlock prepared.represented
    h.allocation.positive (Nat.zero_add _)).mono ?_
  intro t finished
  refine ⟨finished.represented, finished.base.trans prepared.base, finished.laneWord,
    finished.rd.trans prepared.rd, finished.wr.trans prepared.wr, ?_, finished.sp.trans prepared.sp, ?_⟩
  · have frame := finished.frame
    rw [prepared.base] at frame
    exact prepared.frame.trans frame
  · intro r hr bx; exact (finished.regs r hr bx).trans (prepared.regs r hr bx)

theorem code_rel (p : Params) (positive : 0 < p.lanes) (leftMemory rightMemory : Array Block) :
    RelCT isa (ReductionInit.Related p leftMemory rightMemory) Impl.Argon2.AArch64.FinalReduction.code
      (fun _ _ => True) :=
  (ReductionInit.code_rel p leftMemory rightMemory).seq
    (ReduceLanes.loop_rel p 0 p.lanes leftMemory rightMemory zeroBlock zeroBlock positive (Nat.zero_add _))

end VG.Proof.Argon2.AArch64.FinalReduction
end

/-! Preserve the final-call allocations and metadata through the matrix reduction. -/

namespace VG.Proof.Argon2.AArch64.Finish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Ready (p : Params) (s : State) : Prop where
  reduction : ReductionInit.Ready p s
  output : FinalOutput.Ready p s

theorem frame_word {s t : State} {p : Params} {memory : Array Block} {acc : Block}
    (ready : ReductionInit.Ready p s) (done : ReduceLanes.Finished s t p memory acc)
    (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)]
  exact done.frame.readW (r := ⟨s.gpr .x19, 272⟩) (Offset.contains_base _ bound (by omega_using [bound]))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ready.allocation.frame.symm.sub_right (Region.sub_prefix (by
          have nonempty := Proof.Argon2.lastIndex_bounds p ready.allocation.positive ready.allocation.minimum 0 ready.allocation.positive
          omega_using [nonempty]))) (by decide)

theorem output_ready {s t : State} {p : Params} {memory : Array Block} {acc : Block}
    (ready : Ready p s) (done : ReduceLanes.Finished s t p memory acc) : FinalOutput.Ready p t := by
  have bp := done.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)
  have sp := done.sp
  have output : FinalOutput.output t = FinalOutput.output s := frame_word ready.reduction done 256 (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := frame_word ready.reduction done 248 (by decide)
  refine ⟨?_, ready.output.positive, ready.output.bound, ?_,
    (frame_word ready.reduction done 264 (by decide)).trans ready.output.tagWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sp]; exact ready.output.stackMinimum
  · rw [done.rd, done.wr, bp]; exact ready.output.reads
  · rw [done.base, done.rd, done.wr]; exact ready.output.input
  · rw [output, done.wr]; exact ready.output.outputWrite
  · rw [work, done.wr]; exact ready.output.workWrite
  · rw [done.base, work]; exact ready.output.inputWork
  · rw [output, work]; exact ready.output.outputWork
  · rw [sp, done.base]; exact ready.output.stackInput
  · rw [sp, output]; exact ready.output.stackOutput
  · rw [sp, work]; exact ready.output.stackWork

end VG.Proof.Argon2.AArch64.Finish

end

end

/-! ### `Argon2.AArch64.FillIterations`, which only this module used -/

section

/-! ### `Argon2.AArch64.FillIterationsBody`, which only this module used -/

section

/-! ### `Argon2.AArch64.FillIteration`, which only this module used -/

section

/-! ### `Argon2.AArch64.FillSlices`, which only this module used -/

section

/-! ### `Argon2.AArch64.FillSlicesBody`, which only this module used -/

section

/-! ### `Argon2.AArch64.FillSlice`, which only this module used -/

section

/-! ### `Argon2.AArch64.FillLanes`, which only this module used -/

section

/-! ### `Argon2.AArch64.FillLanesBody`, which only this module used -/

section

/-! One lane iteration fills its segment and advances the public lane. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.FillLanes

open VG VG.AArch64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass lane slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  laneWord : t.gpr .x24 = BitVec.ofNat 64 (lane + 1)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x23 → t.gpr r = s.gpr r
  header : ∃ a, SegmentSetup.Ready p pass lane slice a ∧ Divide.Keeps [.x24, .x12, .x13, .x14, .x15] a t
  cf : eval (.nonzero .x .x14) t = some (decide (lane + 1 < p.lanes))
  next : lane + 1 < p.lanes → SegmentSetup.Ready p pass (lane + 1) slice t

theorem body_ok (s : State) (p : Params) (pass lane slice : Nat)
    (h : SegmentSetup.Ready p pass lane slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillLanes.body s (Done s · p pass lane slice state) := by
  unfold Impl.Argon2.AArch64.FillLanes.body
  refine WP.seq ((SegmentSetup.code_ok s p pass lane slice h state represented).mono ?_)
  intro a filled
  have ready := finished_ready h.parameters filled
  obtain ⟨old, words⟩ := ready.words
  have added : a.gpr .x24 + 1 = BitVec.ofNat 64 (lane + 1) := by
    rw [words.laneWord, BitVec.ofNat_add]; rfl
  have laneBound := h.parameters.laneBound
  have lanesBound32 := h.parameters.lanesBound
  have left : (a.gpr .x24 + 1).toNat < 2 ^ 63 := by
    rw [added, ReferenceMap.word_nat (lane + 1) (by omega_using [laneBound, lanesBound32])]; omega_using [laneBound, lanesBound32]
  have right : (a.mem.readW (off (a.gpr .x19) 184) 64).toNat < 2 ^ 63 := by
    rw [ready.lanesWord, ReferenceMap.word_nat p.lanes (by omega_using [lanesBound32])]; omega_using [lanesBound32]
  refine (advance_ok a (ready.layout.frameRead 184 (by simp)) left right).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [keeps.mem, bp]
  have nextWord := value.trans added
  have lanesBound : p.lanes < 2 ^ 64 := Nat.lt_trans h.parameters.lanesBound (by decide)
  refine ⟨?_, base.trans filled.matrix, work.trans filled.work, nextWord, keeps.rd.trans filled.rd,
    keeps.wr.trans filled.wr, ?_, keeps.sp.trans filled.sp, ?_, ⟨a, ready, keeps⟩, ?_, ?_⟩
  · rw [keeps.mem, base]; exact filled.represented
  · rw [keeps.mem]; exact filled.frame
  · intro r hr bx ix
    have outside : r ∉ [Reg.x24, .x12, .x13, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    exact (keeps.regs r outside).trans (filled.regs r hr ix)
  · rw [flag, added, ready.lanesWord, ReferenceMap.word_nat (lane + 1) (by omega_using [laneBound, lanesBound32]),
      ReferenceMap.word_nat p.lanes lanesBound]
  · intro active; exact change_lane_ready ready keeps nextWord active

end VG.Proof.Argon2.AArch64.FillLanes

end

end


/-! Termination and correctness of all remaining lanes in one slice. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.FillLanes

open VG VG.AArch64 VG.Spec.Argon2

structure Finished (s t : State) (p : Params) (pass slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  laneWord : t.gpr .x24 = BitVec.ofNat 64 p.lanes
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x23 → t.gpr r = s.gpr r
  header : ∃ lane a, lane + 1 = p.lanes ∧ SegmentSetup.Ready p pass lane slice a ∧ Divide.Keeps [.x24, .x12, .x13, .x14, .x15] a t

theorem Done.finished {s t : State} {p : Params} {pass lane slice : Nat} {state : FillState}
    (h : Done s t p pass lane slice state) (last : lane + 1 = p.lanes) :
    Finished s t p pass slice (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state) := by
  obtain ⟨a, ready, keeps⟩ := h.header
  exact ⟨h.represented, h.matrix, h.work, last ▸ h.laneWord, h.rd, h.wr, h.frame, h.sp,
    h.regs, lane, a, last, ready, keeps⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass lane slice : Nat} {state finalState : FillState}
    (first : Done s a p pass lane slice state) (rest : Finished a t p pass slice finalState) :
    Finished s t p pass slice finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work, rest.laneWord,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.sp.trans first.sp, ?_, rest.header⟩
  · have frame := rest.frame
    rw [FillBlock.writes, first.matrix, first.work,
      first.sp,
      first.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide)] at frame
    exact first.frame.trans frame
  · intro r hr bx ix; exact (rest.regs r hr bx ix).trans (first.regs r hr bx ix)

theorem loop_ok (count : Nat) (s : State) (p : Params) (pass lane slice : Nat)
    (h : SegmentSetup.Ready p pass lane slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    WP isa Impl.Argon2.AArch64.FillLanes.loop s
      (Finished s · p pass slice (Proof.Argon2.lanes p pass slice lane count state)) := by
  induction count generalizing s lane state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := body_ok s p pass lane slice h state represented
    rw [Proof.Argon2.lanes_succ]
    cases n with
    | zero =>
      have last : lane + 1 = p.lanes := endLane
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : lane + 1 < p.lanes := by omega_using [endLane]
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (lane + 1) (done.next active)
        (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state) done.represented (by omega_using []) (by omega_using [endLane])
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [done.cf, active, decide_true]

end VG.Proof.Argon2.AArch64.FillLanes

end

end


/-! Merged from `Proof.Argon2.AArch64.FillSlicePrepare`. -/

@[expose] public section

section
/-! Merged from `Proof.Argon2.AArch64.FillHeader`. -/
section
/-! Allocation and normalized header across lane, slice and pass boundaries. -/

namespace VG.Proof.Argon2.AArch64.FillHeader

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (pass lane slice : Nat) (s : State) : Prop where
  layout : FillKernel.Layout p s
  addressLayout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  write : InRegions s.wr (off (s.gpr .x19) 8) 8
  words : ∃ old, AddressHeader.Words p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  laneLength : s.gpr .x20 = BitVec.ofNat 64 p.laneLen
  segmentLength : s.gpr .x21 = BitVec.ofNat 64 p.segmentLen
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

theorem of_segment_ready {p : Params} {pass lane slice : Nat} {s : State}
    (h : SegmentSetup.Ready p pass lane slice s) : Ready p pass lane slice s :=
  ⟨h.layout, h.addressLayout, h.reads, h.write, h.words, h.matrixWork, h.laneLength, h.segmentLength, h.lanesWord⟩

theorem Ready.segment {p : Params} {pass lane slice : Nat} {s : State}
    (h : Ready p pass lane slice s) (parameters : FillContext.Parameters p pass lane slice) :
    SegmentSetup.Ready p pass lane slice s :=
  ⟨parameters, h.layout, h.addressLayout, h.reads, h.write, h.words,
    h.matrixWork, h.laneLength, h.segmentLength, h.lanesWord⟩

theorem Ready.of_state {p : Params} {pass lane slice newLane newSlice : Nat} {s t : State}
    (h : Ready p pass lane slice s)
    (regs : ∀ r ∈ [Reg.x19, .x20, .x21], t.gpr r = s.gpr r)
    (sp : t.sp = s.sp) (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (laneWord : t.gpr .x24 = BitVec.ofNat 64 newLane) (sliceWord : t.gpr .x22 = BitVec.ofNat 64 newSlice) :
    Ready p pass newLane newSlice t := by
  have bp := regs .x19 (by simp)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [mem, bp]
  refine ⟨h.layout.of_preserved bp sp base work rd wr, ?_, ?_, ?_, ?_, ?_,
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
    refine ⟨old, ?_, laneWord, sliceWord, ?_, ?_, ?_, ?_⟩
    all_goals rw [mem, bp]
    · exact words.passWord
    · exact words.blocksWord
    · exact words.passesWord
    · exact words.variantWord
    · exact words.counterWord
  · rw [base, work]; exact h.matrixWork
  · rw [mem, bp]; exact h.lanesWord

theorem of_lanes_finished {p : Params} {pass slice : Nat} {s t : State} {state : FillState}
    (h : FillLanes.Finished s t p pass slice state) : Ready p pass p.lanes slice t := by
  obtain ⟨lane, a, _, ready, keeps⟩ := h.header
  obtain ⟨old, words⟩ := ready.words
  apply (of_segment_ready ready).of_state _ keeps.sp keeps.mem keeps.rd keeps.wr h.laneWord
    ((keeps.regs .x22 (by decide)).trans words.sliceWord)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact keeps.regs _ (by decide)

end VG.Proof.Argon2.AArch64.FillHeader
end

/-! Initialize lane zero without requiring a valid incoming lane coordinate. -/

namespace VG.Proof.Argon2.AArch64.FillSlice

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (pass slice : Nat) (s : State) : Prop where
  parameters : FillContext.Parameters p pass 0 slice
  header : ∃ lane, FillHeader.Ready p pass lane slice s

structure Prepared (s t : State) (p : Params) (pass slice : Nat) : Prop where
  ready : SegmentSetup.Ready p pass 0 slice t
  keeps : Divide.Keeps [.x24] s t

theorem setup_ok (s : State) (p : Params) (pass slice : Nat) (h : Ready p pass slice s) :
    WP isa (.block Impl.Argon2.AArch64.FillSlice.setup) s (Prepared s · p pass slice) := by
  refine (SegmentSetup.register_ok s .x24 0 (by decide)).mono ?_
  rintro t ⟨laneWord, keeps⟩
  obtain ⟨lane, header⟩ := h.header
  obtain ⟨old, words⟩ := header.words
  have next : FillHeader.Ready p pass 0 slice t := header.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact keeps.regs _ (by decide))
    keeps.sp keeps.mem keeps.rd keeps.wr laneWord ((keeps.regs .x22 (by decide)).trans words.sliceWord)
  exact ⟨next.segment h.parameters, keeps⟩

end VG.Proof.Argon2.AArch64.FillSlice
end

/-! Correctness of one complete slice, starting at lane zero. -/

namespace VG.Proof.Argon2.AArch64.FillSlice

open VG VG.AArch64 VG.Spec.Argon2

theorem code_ok (s : State) (p : Params) (pass slice : Nat) (h : Ready p pass slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillSlice.code s
      (FillLanes.Finished s · p pass slice (Proof.Argon2.lanes p pass slice 0 p.lanes state)) := by
  unfold Impl.Argon2.AArch64.FillSlice.code
  refine WP.seq ((setup_ok s p pass slice h).mono ?_)
  intro a prepared
  have bp := prepared.keeps.regs .x19 (by decide)
  have base : FillKernel.matrix a = FillKernel.matrix s := by unfold FillKernel.matrix; rw [prepared.keeps.mem, bp]
  have work : AddressCalls.work a = AddressCalls.work s := by unfold AddressCalls.work; rw [prepared.keeps.mem, bp]
  have representedA : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks state.memory := by
    rw [prepared.keeps.mem, base]; exact represented
  refine (FillLanes.loop_ok p.lanes a p pass 0 slice prepared.ready state representedA
    h.parameters.lanesPositive (by omega_using [])).mono ?_
  intro t finished
  refine ⟨finished.represented, finished.matrix.trans base, finished.work.trans work, finished.laneWord,
    finished.rd.trans prepared.keeps.rd, finished.wr.trans prepared.keeps.wr, ?_,
    finished.sp.trans prepared.keeps.sp, ?_, finished.header⟩
  · have frame := finished.frame
    rw [FillBlock.writes, base, work, prepared.keeps.sp, bp, prepared.keeps.mem] at frame
    exact frame
  · intro r hr bx ix
    have ne : r ∉ [Reg.x24] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact bx
    exact (finished.regs r hr bx ix).trans (prepared.keeps.regs r ne)

end VG.Proof.Argon2.AArch64.FillSlice

end

end


/-! Merged from `Proof.Argon2.AArch64.FillSliceAdvance`. -/

@[expose] public section

section
/-! Slice advancement retains the public header and matrix allocation. -/

namespace VG.Proof.Argon2.AArch64.FillSlices

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillSlices

theorem advance_ok (s : State) (ha : (s.gpr .x22 + 1).toNat < 2 ^ 63) :
    WP isa (.block advance) s fun t => t.gpr .x22 = s.gpr .x22 + 1 ∧
      eval (.nonzero .x .x14) t = some (decide ((s.gpr .x22 + 1).toNat < 4)) ∧
      Divide.Keeps [.x22, .x12, .x13, .x14, .x15] s t := by
  simp only [advance, List.flatten_cons, List.flatten_nil, List.append_nil,
    Impl.Argon2.AArch64.Instructions.comparei]
  apply WP.block_append
  refine (Instructions.addi_ok s .x22 1 (by decide) (by decide) (by decide)).mono ?_
  rintro a ⟨value, ka⟩
  apply WP.block_append
  refine (SegmentSetup.register_ok a .x13 4 (by decide)).mono ?_
  rintro b ⟨bound, kb⟩
  have left : (b.gpr .x22).toNat < 2 ^ 63 := by
    rw [kb.regs .x22 (by decide), value]; exact ha
  have right : (b.gpr .x13).toNat < 2 ^ 63 := by rw [bound]; decide
  refine (Instructions.compare_ok b .x22 .x13 left right).mono ?_
  rintro t ⟨flag, kt⟩
  have val := (kt.regs .x22 (by decide)).trans ((kb.regs .x22 (by decide)).trans value)
  refine ⟨val, ?_, (ka.mono (by decide)).trans
    ((kb.mono (by decide)).trans (kt.mono (by decide)))⟩
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag,
    kb.regs .x22 (by decide), value, bound, show (BitVec.ofNat 64 4).toNat = 4 from rfl]
  cases decide ((s.gpr .x22 + 1).toNat < 4) <;> rfl

theorem advanced_header {s t : State} {p : Params} {pass lane slice : Nat}
    (h : FillHeader.Ready p pass lane slice s) (k : Divide.Keeps [.x22, .x12, .x13, .x14, .x15] s t)
    (value : t.gpr .x22 = BitVec.ofNat 64 (slice + 1)) : FillHeader.Ready p pass lane (slice + 1) t := by
  obtain ⟨old, words⟩ := h.words
  exact h.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact k.regs _ (by decide))
    k.sp k.mem k.rd k.wr ((k.regs .x24 (by decide)).trans words.laneWord) value

end VG.Proof.Argon2.AArch64.FillSlices
end

/-! Fill one slice and advance its public coordinate. -/

namespace VG.Proof.Argon2.AArch64.FillSlices

open VG VG.AArch64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (Proof.Argon2.lanes p pass slice 0 p.lanes state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p pass p.lanes (slice + 1) t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  cf : eval (.nonzero .x .x14) t = some (decide (slice + 1 < 4))
  next : slice + 1 < 4 → FillSlice.Ready p pass (slice + 1) t

theorem body_ok (s : State) (p : Params) (pass slice : Nat) (h : FillSlice.Ready p pass slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillSlices.body s (Done s · p pass slice state) := by
  unfold Impl.Argon2.AArch64.FillSlices.body
  refine WP.seq ((FillSlice.code_ok s p pass slice h state represented).mono ?_)
  intro a filled
  have header := FillHeader.of_lanes_finished filled
  obtain ⟨old, words⟩ := header.words
  have sliceBound := h.parameters.sliceBound
  have added : a.gpr .x22 + 1 = BitVec.ofNat 64 (slice + 1) := by
    rw [words.sliceWord, BitVec.ofNat_add]; rfl
  have inputBound : (a.gpr .x22 + 1).toNat < 2 ^ 63 := by
    rw [added, ReferenceMap.word_nat (slice + 1) (by omega_using [sliceBound])]; omega_using [sliceBound]
  refine (advance_ok a inputBound).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have nextWord := value.trans added
  have nextHeader := advanced_header header keeps nextWord
  have bp := keeps.regs .x19 (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [keeps.mem, bp]
  refine ⟨?_, base.trans filled.matrix, work.trans filled.work, nextHeader, keeps.rd.trans filled.rd,
    keeps.wr.trans filled.wr, ?_, keeps.sp.trans filled.sp, ?_, ?_, ?_⟩
  · rw [keeps.mem, base]; exact filled.represented
  · rw [keeps.mem]; exact filled.frame
  · intro r hr bx sl ix
    have outside : r ∉ [Reg.x22, .x12, .x13, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    exact (keeps.regs r outside).trans (filled.regs r hr bx ix)
  · rw [flag, added, ReferenceMap.word_nat (slice + 1) (by omega_using [sliceBound])]
  · intro active
    exact ⟨{ h.parameters with sliceBound := active }, p.lanes, nextHeader⟩

end VG.Proof.Argon2.AArch64.FillSlices

end

end


/-! Termination and correctness of the four-slice filling pass. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.FillSlices

open VG VG.AArch64 VG.Spec.Argon2

structure Finished (s t : State) (p : Params) (pass : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p pass p.lanes 4 t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r

theorem Done.finished {s t : State} {p : Params} {pass slice : Nat} {state : FillState}
    (h : Done s t p pass slice state) (last : slice + 1 = 4) :
    Finished s t p pass (Proof.Argon2.lanes p pass slice 0 p.lanes state) :=
  ⟨h.represented, h.matrix, h.work, last ▸ h.header, h.rd, h.wr, h.frame, h.sp, h.regs⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass slice : Nat} {state finalState : FillState}
    (first : Done s a p pass slice state) (rest : Finished a t p pass finalState) : Finished s t p pass finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work, rest.header,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.sp.trans first.sp, ?_⟩
  · have frame := rest.frame
    rw [FillBlock.writes, first.matrix, first.work,
      first.sp,
      first.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)] at frame
    exact first.frame.trans frame
  · intro r hr bx sl ix; exact (rest.regs r hr bx sl ix).trans (first.regs r hr bx sl ix)

theorem loop_ok (count : Nat) (s : State) (p : Params) (pass slice : Nat)
    (h : FillSlice.Ready p pass slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endSlice : slice + count = 4) :
    WP isa Impl.Argon2.AArch64.FillSlices.loop s (Finished s · p pass (Proof.Argon2.slices p pass slice count state)) := by
  induction count generalizing s slice state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := body_ok s p pass slice h state represented
    rw [Proof.Argon2.slices_succ]
    cases n with
    | zero =>
      have last : slice + 1 = 4 := endSlice
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : slice + 1 < 4 := by omega_using [endSlice]
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (slice + 1) (done.next active)
        (Proof.Argon2.lanes p pass slice 0 p.lanes state) done.represented (by omega_using []) (by omega_using [endSlice])
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [done.cf, active, decide_true]

theorem pass_ok (s : State) (p : Params) (pass : Nat) (h : FillSlice.Ready p pass 0 s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillSlices.loop s (Finished s · p pass (fillPass p state pass)) := by
  rw [← Proof.Argon2.slices_pass p pass state]
  exact loop_ok 4 s p pass 0 h state represented (by decide) (by decide)

end VG.Proof.Argon2.AArch64.FillSlices

end

end


/-! Merged from `Proof.Argon2.AArch64.FillIterationPrepare`. -/

@[expose] public section

section
/-! Start a pass at slice zero regardless of its incoming lane and slice coordinates. -/

namespace VG.Proof.Argon2.AArch64.FillIteration

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (pass : Nat) (s : State) : Prop where
  parameters : FillContext.Parameters p pass 0 0
  header : ∃ lane slice, FillHeader.Ready p pass lane slice s

structure Prepared (s t : State) (p : Params) (pass : Nat) : Prop where
  ready : FillSlice.Ready p pass 0 t
  keeps : Divide.Keeps [.x22] s t

theorem setup_ok (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) :
    WP isa (.block Impl.Argon2.AArch64.FillIteration.setup) s (Prepared s · p pass) := by
  refine (SegmentSetup.register_ok s .x22 0 (by decide)).mono ?_
  rintro t ⟨sliceWord, keeps⟩
  obtain ⟨lane, slice, header⟩ := h.header
  obtain ⟨old, words⟩ := header.words
  have next : FillHeader.Ready p pass lane 0 t := header.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact keeps.regs _ (by decide))
    keeps.sp keeps.mem keeps.rd keeps.wr ((keeps.regs .x24 (by decide)).trans words.laneWord) sliceWord
  exact ⟨⟨h.parameters, lane, next⟩, keeps⟩

end VG.Proof.Argon2.AArch64.FillIteration
end

/-! One complete filling pass against the reviewed specification. -/

namespace VG.Proof.Argon2.AArch64.FillIteration

open VG VG.AArch64 VG.Spec.Argon2

theorem code_ok (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillIteration.code s (FillSlices.Finished s · p pass (fillPass p state pass)) := by
  unfold Impl.Argon2.AArch64.FillIteration.code
  refine WP.seq ((setup_ok s p pass h).mono ?_)
  intro a prepared
  have bp := prepared.keeps.regs .x19 (by decide)
  have base : FillKernel.matrix a = FillKernel.matrix s := by unfold FillKernel.matrix; rw [prepared.keeps.mem, bp]
  have work : AddressCalls.work a = AddressCalls.work s := by unfold AddressCalls.work; rw [prepared.keeps.mem, bp]
  have representedA : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks state.memory := by
    rw [prepared.keeps.mem, base]; exact represented
  refine (FillSlices.pass_ok a p pass prepared.ready state representedA).mono ?_
  intro t finished
  refine ⟨finished.represented, finished.matrix.trans base, finished.work.trans work, finished.header,
    finished.rd.trans prepared.keeps.rd, finished.wr.trans prepared.keeps.wr, ?_,
    finished.sp.trans prepared.keeps.sp, ?_⟩
  · have frame := finished.frame
    rw [FillBlock.writes, base, work, prepared.keeps.sp, bp, prepared.keeps.mem] at frame
    exact frame
  · intro r hr bx sl ix
    have ne : r ∉ [Reg.x22] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact sl
    exact (finished.regs r hr bx sl ix).trans (prepared.keeps.regs r ne)

end VG.Proof.Argon2.AArch64.FillIteration

end

end


/-! Merged from `Proof.Argon2.AArch64.FillPassSave`. -/

@[expose] public section

section
/-! Merged from `Proof.Argon2.AArch64.FillPassCounter`. -/
section
/-! Increment, save and compare the public pass counter. -/
namespace VG.Proof.Argon2.AArch64.FillIterations
open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillIterations

theorem increment_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8) :
    WP isa (.block increment) s fun t =>
      t.gpr .x8 = s.mem.readW (off (s.gpr .x19) 0) 64 + 1 ∧
      Divide.Keeps [.x8, .x12, .x15] s t := by
  simp only [increment, List.flatten_cons, List.flatten_nil, List.append_nil]
  apply WP.block_append
  refine (Instructions.load_ok s .x8 .x19 0 (by decide) (by decide) hr).mono ?_
  rintro a ⟨value, ka⟩
  refine (Instructions.addi_ok a .x8 1 (by decide) (by decide) (by decide)).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨?_, (ka.mono (by decide)).trans kt⟩
  rw [out, value]; rfl

theorem saveCheck_ok (s : State) (hw : InRegions s.wr (off (s.gpr .x19) 0) 8)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 72) 8)
    (ha : (s.gpr .x8).toNat < 2 ^ 63)
    (hb : (s.mem.readW (off (s.gpr .x19) 72) 64).toNat < 2 ^ 63) :
    WP isa (.block saveCheck) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x19) 0) (s.gpr .x8) ∧
      (∀ r, r ∉ [Reg.x13, .x14, .x15] → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      eval (.nonzero .x .x14) t = some (decide ((s.gpr .x8).toNat <
        (s.mem.readW (off (s.gpr .x19) 72) 64).toNat)) := by
  simp only [saveCheck, List.flatten_cons, List.flatten_nil, List.append_nil]
  apply WP.block_append
  refine (Instructions.store_ok s .x19 .x8 0 (by decide) (by decide) hw).mono ?_
  rintro a ⟨mem, regs, rd, wr, sp⟩
  have unchanged : a.mem.readW (off (a.gpr .x19) 72) 64 =
      s.mem.readW (off (s.gpr .x19) 72) 64 := by
    rw [regs, mem]
    exact Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) 72) 8 := by rw [regs, rd, wr]; exact hr
  have left : (a.gpr .x8).toNat < 2 ^ 63 := by rw [regs]; exact ha
  have right : (a.mem.readW (off (a.gpr .x19) 72) 64).toNat < 2 ^ 63 := by rw [unchanged]; exact hb
  refine (Instructions.comparem_ok a .x8 .x19 72 (by decide) (by decide) (by decide)
    read left right).mono ?_
  rintro t ⟨flag, keeps⟩
  refine ⟨keeps.mem.trans mem, ?_, keeps.rd.trans rd, keeps.wr.trans wr, keeps.sp.trans sp, ?_⟩
  · intro r hr; exact (keeps.regs r hr).trans (congrFun regs r)
  · change eval (.nonzero .x .x14) t = some (decide ((s.gpr .x8).toNat <
      (s.mem.readW (off (s.gpr .x19) 72) 64).toNat))
    change eval (.nonzero .x .x14) t = some (decide ((a.gpr .x8).toNat <
      (a.mem.readW (off (a.gpr .x19) 72) 64).toNat)) at flag
    rw [flag, regs, mem]
    rw [Mem.readW_writeW_sep (w := 64) (w' := 64)
      (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]

end VG.Proof.Argon2.AArch64.FillIterations
end

/-! A saved pass counter changes only its eight-byte header word. -/

namespace VG.Proof.Argon2.AArch64.FillIterations

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillIterations

structure Saved (s t : State) : Prop where
  mem : t.mem = s.mem.writeW (off (s.gpr .x19) 0) (s.mem.readW (off (s.gpr .x19) 0) 64 + 1)
  regs : ∀ r, r ∉ [Reg.x8, .x12, .x13, .x14, .x15] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  cf : eval (.nonzero .x .x14) t = some (decide ((s.mem.readW (off (s.gpr .x19) 0) 64 + 1).toNat <
    (s.mem.readW (off (s.gpr .x19) 72) 64).toNat))
  frame : Frame [⟨off (s.gpr .x19) 0, 8⟩] s.mem t.mem

theorem advance_ok (s : State) (read : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8)
    (write : InRegions s.wr (off (s.gpr .x19) 0) 8)
    (passesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 72) 8)
    (ha : (s.mem.readW (off (s.gpr .x19) 0) 64 + 1).toNat < 2 ^ 63)
    (hb : (s.mem.readW (off (s.gpr .x19) 72) 64).toNat < 2 ^ 63) : WP isa advance s (Saved s) := by
  unfold advance
  refine WP.seq ((increment_ok s read).mono ?_)
  rintro a ⟨value, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have readA : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) 72) 8 := by
    rw [keeps.rd, keeps.wr, bp]; exact passesRead
  have writeA : InRegions a.wr (off (a.gpr .x19) 0) 8 := by rw [keeps.wr, bp]; exact write
  have left : (a.gpr .x8).toNat < 2 ^ 63 := by rw [value]; exact ha
  have right : (a.mem.readW (off (a.gpr .x19) 72) 64).toNat < 2 ^ 63 := by
    rw [keeps.mem, bp]; exact hb
  refine (saveCheck_ok a writeA readA left right).mono ?_
  rintro t ⟨mem, regs, rd, wr, mx, cf⟩
  have finalMem : t.mem = s.mem.writeW (off (s.gpr .x19) 0) (s.mem.readW (off (s.gpr .x19) 0) 64 + 1) := by
    rw [mem, keeps.mem, bp, value]
  refine ⟨finalMem, ?_, rd.trans keeps.rd, wr.trans keeps.wr, mx.trans keeps.sp, ?_, ?_⟩
  · intro r ne
    have small : r ∉ [Reg.x8, .x12, .x15] := by
      intro hr; apply ne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp_all
    have compare : r ∉ [Reg.x13, .x14, .x15] := by
      intro hr; apply ne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp_all
    exact (regs r compare).trans (keeps.regs r small)
  · rw [cf, value, keeps.mem, bp]
  · rw [finalMem]
    exact (Frame.refl _ _).writeW (r := ⟨off (s.gpr .x19) 0, 8⟩) (by simp) _ (Region.contains_self _ _)

theorem Saved.read {s t : State} (h : Saved s t) (d : Nat) (separate : 8 ≤ d) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [h.regs .x19 (by decide), h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ (d := d) (n := 8) (e := 0) (k := 8)
    (by omega_using [separate]) (by omega_using [bound]) (by decide)) (by decide)

theorem Saved.words {s t : State} {p : Params} {pass lane slice old : Nat}
    (h : Saved s t) (words : AddressHeader.Words p pass lane slice old s) :
    AddressHeader.Words p (pass + 1) lane slice old t := by
  refine ⟨?_, (h.regs .x24 (by decide)).trans words.laneWord,
    (h.regs .x22 (by decide)).trans words.sliceWord,
    (h.read 240 (by decide) (by decide)).trans words.blocksWord,
    (h.read 72 (by decide) (by decide)).trans words.passesWord,
    (h.read 112 (by decide) (by decide)).trans words.variantWord,
    (h.read 8 (by decide) (by decide)).trans words.counterWord⟩
  rw [h.regs .x19 (by decide), h.mem, Mem.readW_writeW_self64, words.passWord, BitVec.ofNat_add]
  rfl

theorem Saved.header {s t : State} {p : Params} {pass lane slice : Nat}
    (h : Saved s t) (header : FillHeader.Ready p pass lane slice s) : FillHeader.Ready p (pass + 1) lane slice t := by
  have bp := h.regs .x19 (by decide)
  have sp := h.sp
  have base : FillKernel.matrix t = FillKernel.matrix s := h.read 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work s := h.read 248 (by decide) (by decide)
  refine ⟨header.layout.of_preserved bp sp base work h.rd h.wr, ?_, ?_, ?_, ?_, ?_,
    (h.regs .x20 (by decide)).trans header.laneLength, (h.regs .x21 (by decide)).trans header.segmentLength, ?_⟩
  · constructor
    · rw [h.rd, h.wr, bp]; exact header.addressLayout.frameRead
    · rw [h.wr, work]; exact header.addressLayout.workWrite
    · rw [bp, work]; exact header.addressLayout.frameWork
    · rw [bp, sp]; exact header.addressLayout.frameStack
    · rw [sp, work]; exact header.addressLayout.stackWork
  · rw [h.rd, h.wr, bp]; exact header.reads
  · rw [h.wr, bp]; exact header.write
  · obtain ⟨old, words⟩ := header.words; exact ⟨old, h.words words⟩
  · rw [base, work]; exact header.matrixWork
  · exact (h.read 184 (by decide) (by decide)).trans header.lanesWord

end VG.Proof.Argon2.AArch64.FillIterations
end

/-! Merged from `Proof.Argon2.AArch64.FillIterationsFrame`. -/
section
/-! The outer pass loop also writes the public pass word at frame offset zero. -/

namespace VG.Proof.Argon2.AArch64.FillIterations

open VG VG.AArch64 VG.Spec.Argon2

def writes (s : State) (p : Params) : List Region :=
  [⟨FillKernel.matrix s, p.blocks * 1024⟩, ⟨AddressCalls.work s, 8192⟩,
    below (s.sp) 8, ⟨s.gpr .x19, 24⟩]

theorem filling_frame {s t : State} {p : Params} (h : Frame (FillBlock.writes s p) s.mem t.mem) :
    Frame (writes s p) s.mem t.mem := by
  apply h.sub
  intro r hr
  simp only [FillBlock.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨⟨s.gpr .x19, 24⟩, by simp [writes], Offset.sub_base _ (by decide)⟩

theorem Saved.outer_frame {s t : State} {p : Params} (h : Saved s t) : Frame (writes s p) s.mem t.mem := by
  apply h.frame.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨s.gpr .x19, 24⟩, by simp [writes], Offset.sub_base _ (by decide)⟩

theorem Saved.represents {s t : State} {p : Params} {pass lane slice : Nat}
    (h : Saved s t) (header : FillHeader.Ready p pass lane slice s) (blocks : Array Block)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks blocks) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks blocks := by
  have base : FillKernel.matrix t = FillKernel.matrix s := h.read 232 (by decide) (by decide)
  rw [base]
  refine ⟨represented.size, ?_⟩
  intro k hk
  apply Eq.trans _ (represented.block k hk)
  apply FillCompress.block_frame h.frame
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact (header.layout.matrixFrame.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)).sub_right
    (Offset.sub_base _ (by decide))

end VG.Proof.Argon2.AArch64.FillIterations
end

/-! A complete pass retains the matrix and advances its public iteration counter. -/

namespace VG.Proof.Argon2.AArch64.FillIterations

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (pass : Nat) (s : State) : Prop where
  filling : FillIteration.Ready p pass s
  passesBound : p.passes < 2 ^ 32
  passWrite : InRegions s.wr (off (s.gpr .x19) 0) 8

structure Done (s t : State) (p : Params) (pass : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks (fillPass p state pass).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p (pass + 1) p.lanes 4 t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  cf : eval (.nonzero .x .x14) t = some (decide (pass + 1 < p.passes))
  next : pass + 1 < p.passes → Ready p (pass + 1) t

theorem body_ok (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillIterations.body s (Done s · p pass state) := by
  unfold Impl.Argon2.AArch64.FillIterations.body
  refine WP.seq ((FillIteration.code_ok s p pass h.filling state represented).mono ?_)
  intro a filled
  have write : InRegions a.wr (off (a.gpr .x19) 0) 8 := by
    rw [filled.wr, filled.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)]
    exact h.passWrite
  obtain ⟨old, words⟩ := filled.header.words
  have passBound := h.filling.parameters.passBound
  have added : (BitVec.ofNat 64 pass + 1 : Addr) = BitVec.ofNat 64 (pass + 1) := by
    rw [BitVec.ofNat_add]; rfl
  have left : (a.mem.readW (off (a.gpr .x19) 0) 64 + 1).toNat < 2 ^ 63 := by
    rw [words.passWord, added, ReferenceMap.word_nat (pass + 1) (by omega_using [passBound])]; omega_using [passBound]
  have right : (a.mem.readW (off (a.gpr .x19) 72) 64).toNat < 2 ^ 63 := by
    rw [words.passesWord, ReferenceMap.word_nat p.passes (Nat.lt_trans h.passesBound (by decide))]
    exact Nat.lt_trans h.passesBound (by decide)
  refine (advance_ok a (filled.header.reads 0 (by simp)) write
    (filled.header.reads 72 (by simp)) left right).mono ?_
  intro t saved
  have header := saved.header filled.header
  have base : FillKernel.matrix t = FillKernel.matrix a := saved.read 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work a := saved.read 248 (by decide) (by decide)
  refine ⟨saved.represents filled.header _ filled.represented, base.trans filled.matrix,
    work.trans filled.work, header, saved.rd.trans filled.rd, saved.wr.trans filled.wr,
    ?_, saved.sp.trans filled.sp, ?_, ?_, ?_⟩
  · have lastFrame := saved.outer_frame (p := p)
    rw [writes, filled.matrix, filled.work,
      filled.sp,
      filled.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)] at lastFrame
    exact (filling_frame filled.frame).trans lastFrame
  · intro r hr bx sl ix
    have ne : r ∉ [Reg.x8, .x12, .x13, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (saved.regs r ne).trans (filled.regs r hr bx sl ix)
  · rw [saved.cf, words.passWord, words.passesWord, added, ReferenceMap.word_nat (pass + 1) (by omega_using [passBound]),
      ReferenceMap.word_nat p.passes (Nat.lt_trans h.passesBound (by decide))]
  · intro active
    refine ⟨⟨{ h.filling.parameters with passBound := Nat.lt_trans active h.passesBound }, p.lanes, 4, header⟩,
      h.passesBound, ?_⟩
    rw [saved.wr, saved.regs .x19 (by decide)]; exact write

end VG.Proof.Argon2.AArch64.FillIterations

end

end


/-! Termination and correctness of every requested filling pass. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.FillIterations

open VG VG.AArch64 VG.Spec.Argon2

structure Finished (s t : State) (p : Params) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p p.passes p.lanes 4 t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r

theorem Done.finished {s t : State} {p : Params} {pass : Nat} {state : FillState}
    (h : Done s t p pass state) (last : pass + 1 = p.passes) : Finished s t p (fillPass p state pass) :=
  ⟨h.represented, h.matrix, h.work, last ▸ h.header, h.rd, h.wr, h.frame, h.sp, h.regs⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass : Nat} {state finalState : FillState}
    (first : Done s a p pass state) (rest : Finished a t p finalState) : Finished s t p finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work, rest.header,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.sp.trans first.sp, ?_⟩
  · have frame := rest.frame
    rw [writes, first.matrix, first.work,
      first.sp,
      first.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)] at frame
    exact first.frame.trans frame
  · intro r hr bx sl ix; exact (rest.regs r hr bx sl ix).trans (first.regs r hr bx sl ix)

theorem loop_ok (count : Nat) (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endPass : pass + count = p.passes) :
    WP isa Impl.Argon2.AArch64.FillIterations.loop s (Finished s · p (Proof.Argon2.iterations p pass count state)) := by
  induction count generalizing s pass state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := body_ok s p pass h state represented
    rw [Proof.Argon2.iterations_succ]
    cases n with
    | zero =>
      have last : pass + 1 = p.passes := endPass
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : pass + 1 < p.passes := by omega_using [endPass]
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (pass + 1) (done.next active)
        (fillPass p state pass) done.represented (by omega_using []) (by omega_using [endPass])
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [done.cf, active, decide_true]

theorem Finished.frame_word {s t : State} {p : Params} {pass : Nat} {state : FillState}
    (ready : Ready p pass s) (done : Finished s t p state)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : 24 ≤ d) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)]
  obtain ⟨lane, slice, header⟩ := ready.filling.header
  have sub : Region.Sub ⟨off (s.gpr .x19) d, 8⟩ ⟨s.gpr .x19, 272⟩ := Offset.sub_base _ bound
  exact done.frame.readW (r := ⟨off (s.gpr .x19) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact header.layout.matrixFrame.symm.sub_left sub
    · exact header.addressLayout.frameWork.sub_left sub
    · exact header.addressLayout.frameStack.sub_left sub
    · simpa only [off, BitVec.add_zero] using Offset.disjoint (d := d) (n := 8) (e := 0) (k := 24) (s.gpr .x19) (Or.inr (by omega_using [separate])) (by omega_using [bound]) (by decide)) (by decide)

end VG.Proof.Argon2.AArch64.FillIterations

end

end


/-! Merged from `Proof.Argon2.AArch64.FinishStage`. -/

@[expose] public section

section
/-! Merged from `Proof.Argon2.AArch64.FinalOutput`. -/
section
/-! The generic H′ call produces exactly the reviewed final Argon2 tag. -/

namespace VG.Proof.Argon2.AArch64.FinalOutput

open VG VG.AArch64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

structure Done (s t : State) (p : Params) (memory : Array Block) : Prop where
  digest : bytesAt t.mem (output s) p.tagLen = finish p memory
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨output s, p.tagLen⟩, ⟨work s, 16384⟩, below s.sp 16] s.mem t.mem

theorem code_ok (v : HPrime.Backend) (name : String) (s : State) (p : Params)
    (h : Ready p s) (memory : Array Block)
    (block : blockAt s.mem (ReductionState.matrix s) = Proof.Argon2.reduction p memory 0 p.lanes zeroBlock) :
    WP isa (Impl.Argon2.AArch64.FinalOutput.code name v.hash) s (Done s · p memory) := by
  unfold Impl.Argon2.AArch64.FinalOutput.code
  refine WP.seq ((args_ok s h.reads).mono ?_)
  intro a args
  have length := args.outputLength.trans h.tagWord
  refine (FinalCall.hPrime_call_ok v name p.tagLen a (args.ready h) args.inputLength length).mono ?_
  intro t called
  refine ⟨?_, fun r hr => (called.regs r hr).trans (args.regs r hr), called.sp.trans args.keeps.sp, called.rd.trans args.keeps.rd,
    called.wr.trans args.keeps.wr, ?_⟩
  · have input : bytesAt a.mem (a.gpr .x0) 1024 =
        serialize (Proof.Argon2.reduction p memory 0 p.lanes zeroBlock) := by
      rw [args.keeps.mem, args.input, ← Proof.Argon2.serialize_blockAt, block]
    rw [Proof.Argon2.finish_reduction]
    have digest := called.digest
    rw [args.output, input] at digest
    exact digest
  · have frame := called.frame
    rw [args.output, args.work, args.keeps.sp, args.keeps.mem] at frame
    exact frame

end VG.Proof.Argon2.AArch64.FinalOutput
end

/-! The complete reviewed finish computation, with its enclosing frame and ABI obligations. -/

namespace VG.Proof.Argon2.AArch64.Finish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState
open VG.Spec.Blake2 (bytesAt)

def writes (s : State) (p : Params) : List Region :=
  [⟨matrix s, 1024⟩, ⟨FinalOutput.output s, p.tagLen⟩,
    ⟨FinalOutput.work s, 16384⟩, below s.sp 16]

structure Done (s t : State) (p : Params) (memory : Array Block) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen = Spec.Argon2.finish p memory
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem

theorem code_ok (v : HPrime.Backend) (name : String) (s : State) (p : Params)
    (h : Ready p s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa (Impl.Argon2.AArch64.Finish.code name v.hash) s (Done s · p memory) := by
  unfold Impl.Argon2.AArch64.Finish.code
  refine WP.seq ((FinalReduction.code_ok s p h.reduction memory represented).mono ?_)
  intro a reduced
  refine (FinalOutput.code_ok v name a p (output_ready h reduced) memory reduced.represented.accumulator).mono ?_
  intro t written
  have output : FinalOutput.output a = FinalOutput.output s := frame_word h.reduction reduced 256 (by decide)
  have work : FinalOutput.work a = FinalOutput.work s := frame_word h.reduction reduced 248 (by decide)
  refine ⟨?_, fun r hr bx => (written.regs r hr).trans (reduced.regs r hr bx),
    written.sp.trans reduced.sp, written.rd.trans reduced.rd, written.wr.trans reduced.wr, ?_⟩
  · have digest := written.digest
    rw [output] at digest; exact digest
  · have firstFrame : Frame (writes s p) s.mem a.mem := reduced.frame.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨_, by simp [writes], fun _ h => h⟩)
    have lastFrame := written.frame
    rw [output, work, reduced.sp] at lastFrame
    apply firstFrame.trans
    apply lastFrame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp [writes], fun _ h => h⟩

end VG.Proof.Argon2.AArch64.Finish
end

/-! Merged from `Proof.Argon2.AArch64.FillFinishReady`. -/
section
/-! The complete filling loop retains the original final-call allocations and public metadata. -/

namespace VG.Proof.Argon2.AArch64.FillFinish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

theorem finish_ready {s t : State} {p : Params} {state : FillState}
    (filling : FillIterations.Ready p 0 s) (ready : Finish.Ready p s)
    (done : FillIterations.Finished s t p state) : Finish.Ready p t := by
  have bp := done.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)
  have sp := done.sp
  have base : matrix t = matrix s := done.matrix
  have output : FinalOutput.output t = FinalOutput.output s := done.frame_word filling 256 (by decide) (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := done.frame_word filling 248 (by decide) (by decide)
  constructor
  · have a := ready.reduction.allocation
    refine ⟨⟨a.positive, a.minimum, a.bound, ?_, ?_, ?_, ?_⟩, ready.reduction.lanesBound, ?_, ?_⟩
    · rw [done.rd, done.wr, bp]; exact a.read
    · rw [base, done.wr]; exact a.write
    · rw [base, bp]; exact a.frame
    · exact (done.regs .x20 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).trans a.length
    · rw [done.rd, done.wr, bp]; exact ready.reduction.lanesRead
    · exact (done.frame_word filling 184 (by decide) (by decide)).trans ready.reduction.lanesWord
  · refine ⟨?_, ready.output.positive, ready.output.bound, ?_,
      (done.frame_word filling 264 (by decide) (by decide)).trans ready.output.tagWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [sp]; exact ready.output.stackMinimum
    · rw [done.rd, done.wr, bp]; exact ready.output.reads
    · rw [base, done.rd, done.wr]; exact ready.output.input
    · rw [output, done.wr]; exact ready.output.outputWrite
    · rw [work, done.wr]; exact ready.output.workWrite
    · rw [base, work]; exact ready.output.inputWork
    · rw [output, work]; exact ready.output.outputWork
    · rw [sp, base]; exact ready.output.stackInput
    · rw [sp, output]; exact ready.output.stackOutput
    · rw [sp, work]; exact ready.output.stackWork

end VG.Proof.Argon2.AArch64.FillFinish
end

/-! The complete filling and finalization stages produce the reviewed final tag. -/

namespace VG.Proof.Argon2.AArch64.FillFinish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState
open VG.Spec.Blake2 (bytesAt)

structure Ready (p : Params) (s : State) : Prop where
  filling : FillIterations.Ready p 0 s
  finish : Finish.Ready p s
  positive : 0 < p.passes

def writes (s : State) (p : Params) : List Region := FillIterations.writes s p ++ Finish.writes s p

structure Done (s t : State) (p : Params) (state : FillState) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen =
    Spec.Argon2.finish p (Proof.Argon2.iterations p 0 p.passes state).memory
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem

theorem code_ok (v : HPrime.Backend) (name : String) (s : State) (p : Params)
    (h : Ready p s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks state.memory) :
    WP isa (Impl.Argon2.AArch64.FillFinish.code name v.hash) s (Done s · p state) := by
  unfold Impl.Argon2.AArch64.FillFinish.code
  refine WP.seq ((FillIterations.loop_ok p.passes s p 0 h.filling state represented h.positive (Nat.zero_add _)).mono ?_)
  intro a filled
  refine (Finish.code_ok v name a p (finish_ready h.filling h.finish filled) _ filled.represented).mono ?_
  intro t finished
  have output : FinalOutput.output a = FinalOutput.output s := filled.frame_word h.filling 256 (by decide) (by decide)
  have work : FinalOutput.work a = FinalOutput.work s := filled.frame_word h.filling 248 (by decide) (by decide)
  have base : matrix a = matrix s := filled.matrix
  refine ⟨?_, fun r hr bx sl ix => (finished.regs r hr bx).trans (filled.regs r hr bx sl ix),
    finished.sp.trans filled.sp, finished.rd.trans filled.rd, finished.wr.trans filled.wr, ?_⟩
  · have digest := finished.digest
    rw [output] at digest; exact digest
  · have firstFrame : Frame (writes s p) s.mem a.mem := filled.frame.sub (by
      intro r hr
      exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩)
    have lastFrame := finished.frame
    rw [Finish.writes, base, output, work,
      filled.sp] at lastFrame
    apply firstFrame.trans
    apply lastFrame.sub
    intro r hr
    exact ⟨r, List.mem_append_right _ hr, fun _ h => h⟩

end VG.Proof.Argon2.AArch64.FillFinish
