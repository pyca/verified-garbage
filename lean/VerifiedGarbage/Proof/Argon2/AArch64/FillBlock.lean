import VerifiedGarbage.Impl.Argon2.AArch64.ReferenceStart
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Proof.Argon2.AArch64.Compress
import VerifiedGarbage.Impl.Argon2.AArch64.AddressCache
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Impl.Argon2.AArch64.FillWrite
import VerifiedGarbage.Impl.Argon2.AArch64.FillCompress
import VerifiedGarbage.Impl.Argon2.AArch64.AddressCalls
import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Proof.Argon2.AddressInput
import VerifiedGarbage.Impl.Argon2.AArch64.BlockAddress
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Argon2.References
import VerifiedGarbage.Impl.Argon2.AArch64.ReferenceMap
import VerifiedGarbage.Impl.Argon2.AArch64.FirstLane
import VerifiedGarbage.Impl.Argon2.AArch64.ReferenceLane
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Verified
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Argon2.AArch64.Divide
import VerifiedGarbage.Impl.Argon2.AArch64.FillKernel
import VerifiedGarbage.Impl.Argon2.AArch64.FillColumn
import VerifiedGarbage.Impl.Argon2.AArch64.FillPointers
import VerifiedGarbage.Impl.Argon2.AArch64.DependentWord
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.Argon2.AArch64.Derive
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.Argon2.AArch64.Parameters
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Impl.Argon2.AArch64.Initial
import VerifiedGarbage.Impl.Argon2.AArch64.FillBlock
import VerifiedGarbage.Impl.Argon2.AArch64.RandomSource
import VerifiedGarbage.Impl.Argon2.AArch64.AddressMode

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.ReferenceStart`. -/
section

/-! The reference window starts at the next slice on later passes. -/

namespace VG.Proof.Argon2.AArch64.ReferenceStart

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceStart
open VG.Impl.Argon2.AArch64

theorem sub_zero_iff (x y : Addr) : x - y = 0 ↔ x = y := by
  constructor
  · intro h
    calc
      x = (x - y) + y := (BitVec.sub_add_cancel x y).symm
      _ = y := by rw [h]; exact BitVec.zero_add y
  · intro h; rw [h, BitVec.sub_self]; rfl

theorem zero_ok (s : State) : WP isa (.block VG.Impl.Argon2.AArch64.ReferenceStart.zero) s fun t =>
    t.gpr .x6 = 0 ∧ Divide.Keeps [.x6] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.AArch64.ReferenceStart.zero, Instructions.imm, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, Size.bits, Nat.reduceMul, Nat.reduceLT, ite_true,
    BitVec.shiftLeft_zero, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem advance_ok (s : State) : WP isa (.block VG.Impl.Argon2.AArch64.ReferenceStart.advance) s fun t =>
    t.gpr .x6 = (s.gpr .x22 + 1) * s.gpr .x21 ∧
    t.gpr .x15 = s.gpr .x22 - 3 ∧ Divide.Keeps [.x8, .x2, .x6, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.AArch64.ReferenceStart.advance, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.addi, Instructions.mul, Instructions.mark,
    Instructions.comparei, Instructions.compare, Instructions.imm,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    BitVec.add_zero, Option.some.injEq, exists_eq_left', Bool.toNat_true,
    show 1 < 4096 from by decide, show 0 < 4096 from by decide,
    show 3 < 65536 from by decide,
    show (BitVec.ofNat 16 3).setWidth 64 = 3#64 from rfl,
    show (3#64) = (3 : Addr) from rfl,
    show (BitVec.ofNat 64 1) = (1 : Addr) from rfl]
  refine ⟨trivial, sub_value _ _, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
  all_goals rfl

def changed : List Reg := [.x8, .x2, .x6, .x13, .x14, .x15]

def value (s : State) : Addr :=
  if s.gpr .x5 = 0 then 0 else
    if s.gpr .x22 = 3 then 0 else (s.gpr .x22 + 1) * s.gpr .x21

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.AArch64.ReferenceStart.code s fun t =>
    t.gpr .x6 = VG.Proof.Argon2.AArch64.ReferenceStart.value s ∧ Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceStart.changed s t := by
  unfold VG.Impl.Argon2.AArch64.ReferenceStart.code
  refine WP.seq ((CountCandidates.compare_ok s).mono ?_)
  rintro a ⟨flag, keeps⟩
  refine WP.ite (decide (s.gpr .x5 = 0)) (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag, Bool.beq_eq_decide_eq]) ?_ ?_
  · intro h
    have firstPass : s.gpr .x5 = 0 := of_decide_eq_true h
    refine (VG.Proof.Argon2.AArch64.ReferenceStart.zero_ok a).mono ?_
    rintro t ⟨out, tail⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (tail.mono (by decide))⟩
    simpa only [VG.Proof.Argon2.AArch64.ReferenceStart.value, firstPass, ite_true] using out
  · intro h
    have laterPass : s.gpr .x5 ≠ 0 := of_decide_eq_false h
    refine WP.seq ((VG.Proof.Argon2.AArch64.ReferenceStart.advance_ok a).mono ?_)
    rintro b ⟨out, flag, advanceKeeps⟩
    have sliceReg := keeps.regs .x22 (by simp)
    have segmentReg := keeps.regs .x21 (by simp)
    refine WP.ite (decide (s.gpr .x22 = 3))
      (by
        simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag, sliceReg]
        apply congrArg some
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq, decide_eq_true_eq]
        exact VG.Proof.Argon2.AArch64.ReferenceStart.sub_zero_iff _ _) ?_ ?_
    · intro h
      have lastSlice : s.gpr .x22 = 3 := of_decide_eq_true h
      refine (VG.Proof.Argon2.AArch64.ReferenceStart.zero_ok b).mono ?_
      rintro t ⟨out, tail⟩
      refine ⟨?_, ((keeps.mono (by decide)).trans advanceKeeps).trans (tail.mono (by decide))⟩
      simpa only [VG.Proof.Argon2.AArch64.ReferenceStart.value, laterPass, lastSlice, ite_false, ite_true] using out
    · intro h
      have earlierSlice : s.gpr .x22 ≠ 3 := of_decide_eq_false h
      apply WP.of_runBlock
      simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
      refine ⟨?_, (keeps.mono (by decide)).trans advanceKeeps⟩
      simpa only [VG.Proof.Argon2.AArch64.ReferenceStart.value, laterPass, earlierSlice, ite_false, sliceReg, segmentReg] using out

theorem start_nat (p : Spec.Argon2.Params) (hl : 0 < p.lanes)
    (hg : 0 < p.segmentLen) (slice : Nat) (hs : slice < 4) :
    (slice + 1) * p.segmentLen % p.laneLen =
      if slice = 3 then 0 else (slice + 1) * p.segmentLen := by
  rw [Proof.Argon2.laneLen_segments p hl]
  by_cases lastSlice : slice = 3
  · simp only [lastSlice, ite_true, show (3 : Nat) + 1 = 4 from rfl, Nat.mod_self]
  · have smaller : (slice + 1) * p.segmentLen < 4 * p.segmentLen :=
      Nat.mul_lt_mul_of_pos_right (by omega) hg
    rw [Nat.mod_eq_of_lt smaller]
    simp only [lastSlice, ite_false]

theorem value_nat (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (hl : 0 < p.lanes) (hg : 0 < p.segmentLen) (hs : slice < 4)
    (passReg : (s.gpr .x5).toNat = pass)
    (sliceReg : s.gpr .x22 = BitVec.ofNat 64 slice)
    (segmentReg : s.gpr .x21 = BitVec.ofNat 64 p.segmentLen) :
    VG.Proof.Argon2.AArch64.ReferenceStart.value s = BitVec.ofNat 64
      (if pass = 0 then 0 else (slice + 1) * p.segmentLen % p.laneLen) := by
  have isZero : s.gpr .x5 = 0 ↔ pass = 0 := by
    rw [← passReg]
    constructor
    · intro h; rw [h]; rfl
    · intro h
      apply BitVec.eq_of_toNat_eq
      exact h
  have isLast : s.gpr .x22 = 3 ↔ slice = 3 := by
    rw [sliceReg]
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hn
      exact hn
    · intro h; rw [h]; rfl
  unfold VG.Proof.Argon2.AArch64.ReferenceStart.value
  simp only [isZero, isLast]
  by_cases firstPass : pass = 0
  · simp only [firstPass, ite_true]; rfl
  · simp only [firstPass, ite_false, VG.Proof.Argon2.AArch64.ReferenceStart.start_nat p hl hg slice hs]
    by_cases lastSlice : slice = 3
    · simp only [lastSlice, ite_true]; rfl
    · simp only [lastSlice, ite_false]
      rw [sliceReg, segmentReg]
      change (BitVec.ofNat 64 slice + BitVec.ofNat 64 1) *
        BitVec.ofNat 64 p.segmentLen = _
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_mul]

theorem code_nat_ok (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (hl : 0 < p.lanes) (hg : 0 < p.segmentLen) (hs : slice < 4)
    (passReg : (s.gpr .x5).toNat = pass)
    (sliceReg : s.gpr .x22 = BitVec.ofNat 64 slice)
    (segmentReg : s.gpr .x21 = BitVec.ofNat 64 p.segmentLen) :
    WP isa VG.Impl.Argon2.AArch64.ReferenceStart.code s fun t =>
      t.gpr .x6 = BitVec.ofNat 64
        (if pass = 0 then 0 else (slice + 1) * p.segmentLen % p.laneLen) ∧
      Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceStart.changed s t :=
  (VG.Proof.Argon2.AArch64.ReferenceStart.code_ok s).mono (fun _ h =>
    ⟨h.1.trans (VG.Proof.Argon2.AArch64.ReferenceStart.value_nat s p pass slice hl hg hs passReg sliceReg segmentReg), h.2⟩)

end VG.Proof.Argon2.AArch64.ReferenceStart

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillCompressCall`. -/
section

/-! Invoke the verified compression primitive with narrowed permissions,
retaining the surrounding matrix and derivation frame. -/

namespace VG.Proof.Argon2.AArch64.FillCompress

open VG VG.AArch64

/-- Persistent registers available to the enclosing derivation loop. -/
def loopRegs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

structure CallReady (s : State) : Prop where
  left : Covers [⟨s.gpr .x0, 1024⟩] (s.rd ++ s.wr)
  right : Covers [⟨s.gpr .x1, 1024⟩] (s.rd ++ s.wr)
  output : Covers [⟨s.gpr .x2, 1024⟩] s.wr
  scratch : Covers [⟨s.gpr .x3, 4096⟩] s.wr
  leftScratch : (⟨s.gpr .x0, 1024⟩ : Region).Disjoint ⟨s.gpr .x3, 4096⟩
  rightScratch : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨s.gpr .x3, 4096⟩
  outputScratch : (⟨s.gpr .x2, 1024⟩ : Region).Disjoint ⟨s.gpr .x3, 4096⟩
  stackLeft : (below s.sp 8).Disjoint ⟨s.gpr .x0, 1024⟩
  stackRight : (below s.sp 8).Disjoint ⟨s.gpr .x1, 1024⟩
  stackOutput : (below s.sp 8).Disjoint ⟨s.gpr .x2, 1024⟩
  stackScratch : (below s.sp 8).Disjoint ⟨s.gpr .x3, 4096⟩

structure Called (s t : State) : Prop where
  result : Spec.Argon2.blockAt t.mem (s.gpr .x2) = Spec.Argon2.compress
    (Spec.Argon2.blockAt s.mem (s.gpr .x0)) (Spec.Argon2.blockAt s.mem (s.gpr .x1))
  regs : ∀ r ∈ VG.Proof.Argon2.AArch64.FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .x2, 1024⟩, ⟨s.gpr .x3, 4096⟩, below s.sp 8] s.mem t.mem

theorem call_hyps (s : State) (h : VG.Proof.Argon2.AArch64.FillCompress.CallReady s) :
    compressLocal.pre (s.callEntry.withRegions [⟨s.gpr .x0, 1024⟩, ⟨s.gpr .x1, 1024⟩]
      [⟨s.gpr .x2, 1024⟩, ⟨s.gpr .x3, 4096⟩]) ∧
    Covers [⟨s.gpr .x0, 1024⟩, ⟨s.gpr .x1, 1024⟩,
      ⟨s.gpr .x2, 1024⟩, ⟨s.gpr .x3, 4096⟩] (s.rd ++ s.wr) ∧
    Covers [⟨s.gpr .x2, 1024⟩, ⟨s.gpr .x3, 4096⟩] s.wr := by
  have g : ∀ r, r ∉ linkRegs → s.callEntry.gpr r = s.gpr r := fun _ hr => State.callEntry_gpr s hr
  refine ⟨?_, ?_, ?_⟩
  · simp only [compressLocal, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g _ (by decide : Reg.x0 ∉ linkRegs),
      g _ (by decide : Reg.x1 ∉ linkRegs), g _ (by decide : Reg.x2 ∉ linkRegs),
      g _ (by decide : Reg.x3 ∉ linkRegs)]
    exact ⟨trivial, trivial, h.outputScratch, h.leftScratch, h.rightScratch⟩
  · intro p n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.left p n ⟨_, List.mem_singleton_self _, hc⟩
    · exact h.right p n ⟨_, List.mem_singleton_self _, hc⟩
    · obtain ⟨r, hr, hc⟩ := h.output p n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · obtain ⟨r, hr, hc⟩ := h.scratch p n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro p n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.output p n ⟨_, List.mem_singleton_self _, hc⟩
    · exact h.scratch p n ⟨_, List.mem_singleton_self _, hc⟩

theorem call_ok (name : String) (s : State) (h : VG.Proof.Argon2.AArch64.FillCompress.CallReady s) :
    WP isa (.call name Impl.Argon2.AArch64.compress) s (VG.Proof.Argon2.AArch64.FillCompress.Called s) := by
  obtain ⟨pre, cover, writes⟩ := VG.Proof.Argon2.AArch64.FillCompress.call_hyps s h
  refine WP.call (k := compressLocal) VG.Proof.Argon2.AArch64.compress_correct pre cover writes ?_ (by lit_decide)
  intro t rd wr sp frame regs _ result
  change Spec.Argon2.blockAt t.mem (s.callEntry.gpr .x2) = Spec.Argon2.compress
    (Spec.Argon2.blockAt s.mem (s.callEntry.gpr .x0))
    (Spec.Argon2.blockAt s.mem (s.callEntry.gpr .x1)) at result
  rw [State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs)] at result
  refine ⟨result, ?_, rd, wr, sp, frame.mono ?_⟩
  · intro r hr
    have hp : r ∈ preserved ∧ r ≠ .x30 := by
      simp only [VG.Proof.Argon2.AArch64.FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact regs r hp.1 hp.2
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    exact hr.elim Or.inl (fun h => Or.inr (Or.inl h))

end VG.Proof.Argon2.AArch64.FillCompress

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillWritePrefix`. -/
section

/-! Merged from `Proof.Argon2.AArch64.FillWriteWord`. -/
section
/-! One output word, keeping register writes folded during execution. -/

namespace VG.Proof.Argon2.AArch64.FillWrite

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillWrite
open VG.Impl.Argon2.AArch64

/-- Registers preserved while copying/XORing matrix words and testing the pass. -/
def CopyKeeps (s t : State) : Prop :=
  (∀ r, r ≠ .x8 → r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → t.gpr r = s.gpr r) ∧
    t.rd = s.rd ∧ t.wr = s.wr

theorem CopyKeeps.refl (s : State) : VG.Proof.Argon2.AArch64.FillWrite.CopyKeeps s s := ⟨fun _ _ _ _ _ => rfl, rfl, rfl⟩
theorem CopyKeeps.trans {s t u : State} (h : VG.Proof.Argon2.AArch64.FillWrite.CopyKeeps s t) (k : VG.Proof.Argon2.AArch64.FillWrite.CopyKeeps t u) : VG.Proof.Argon2.AArch64.FillWrite.CopyKeeps s u :=
  ⟨fun r h8 h13 h14 h15 => (k.1 r h8 h13 h14 h15).trans (h.1 r h8 h13 h14 h15),
    k.2.1.trans h.2.1, k.2.2.trans h.2.2⟩

def value (xorOld : Bool) (m : Mem) (src dest : Addr) (i : Nat) : Addr :=
  let next := m.readW (off src (8 * i)) 64
  if xorOld then next ^^^ m.readW (off dest (8 * i)) 64 else next

/-- The source is readable and the destination writable; its old contents
are read only on later passes. -/
theorem word_ok (xorOld : Bool) (s : State) (i : Nat) (hi : i < 128)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x1) (8 * i)) 8)
    (hw : InRegions s.wr (off (s.gpr .x0) (8 * i)) 8)
    (ho : InRegions (s.rd ++ s.wr) (off (s.gpr .x0) (8 * i)) 8) :
    WP isa (.block (Impl.Argon2.AArch64.FillWrite.word xorOld i)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x0) (8 * i))
        (VG.Proof.Argon2.AArch64.FillWrite.value xorOld s.mem (s.gpr .x1) (s.gpr .x0) i) ∧
      (∀ r, r ≠ .x8 → r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hoff : (8 * i) % 8 = 0 ∧ 8 * i < 4096 * 8 := by omega
  cases xorOld <;> apply WP.of_runBlock <;>
    simp only [Impl.Argon2.AArch64.FillWrite.word, VG.Proof.Argon2.AArch64.FillWrite.value, Bool.false_eq_true, ite_false, ite_true,
      Instructions.load, Instructions.store, Instructions.xorm, Instructions.logic,
      Instructions.mark, Instructions.mov,
      List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, hoff,
      State.load, State.store, State.read, Size.bits, Size.bytes,
      off, hr, hw, ho, and_self, show 0 < 4096 from by decide,
      RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
      BitVec.setWidth_eq, BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
      Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  all_goals
    refine ⟨?_, ?_, trivial, trivial, rfl⟩
    · rfl
    · intro r h8 h13 _h14 h15
      simp only [h8, h13, h15, ite_false]

end VG.Proof.Argon2.AArch64.FillWrite
end

/-! Compose the word writes without re-executing a long load/store block. -/

namespace VG.Proof.Argon2.AArch64.FillWrite

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillWrite

def result (xorOld : Bool) (m : Mem) (src dest : Addr) : VG.Spec.Argon2.Block :=
  if xorOld then xorBlock (VG.Spec.Argon2.blockAt m src) (VG.Spec.Argon2.blockAt m dest) else VG.Spec.Argon2.blockAt m src

theorem result_get (xorOld : Bool) (m : Mem) (src dest : Addr) (i : Fin 128) :
    (VG.Proof.Argon2.AArch64.FillWrite.result xorOld m src dest)[i] = VG.Proof.Argon2.AArch64.FillWrite.value xorOld m src dest i.val := by
  cases xorOld <;> simp only [VG.Proof.Argon2.AArch64.FillWrite.result, VG.Proof.Argon2.AArch64.FillWrite.value, Bool.false_eq_true, ite_false, ite_true,
    xorBlock_get, blockAt_get]

theorem frame_extend {m m' : Mem} {dest : Addr} {n k : Nat}
    (hf : Frame [⟨dest, 8 * n⟩] m m') (h : n ≤ k) : Frame [⟨dest, 8 * k⟩] m m' := by
  apply hf.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨_, by simp, Region.sub_prefix (Nat.mul_le_mul_left 8 h)⟩

theorem source_read {m m' : Mem} {src dest : Addr} {n : Nat}
    (hf : Frame [⟨dest, 8 * n⟩] m m') (hn : n ≤ 128)
    (hd : (⟨src, 1024⟩ : Region).Disjoint ⟨dest, 1024⟩) (i : Fin 128) :
    m'.readW (off src (8 * i.val)) 64 = m.readW (off src (8 * i.val)) 64 := by
  have full := VG.Proof.Argon2.AArch64.FillWrite.frame_extend hf hn
  exact full.readW (r := ⟨src, 1024⟩)
    (Offset.contains_base src (by omega) (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

theorem old_read {m m' : Mem} {dest : Addr} {n : Nat}
    (hf : Frame [⟨dest, 8 * n⟩] m m') (hn : n < 128) :
    m'.readW (off dest (8 * n)) 64 = m.readW (off dest (8 * n)) 64 :=
  hf.readW (r := ⟨off dest (8 * n), 8⟩) (Region.contains_self _ _)
    (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact Offset.disjoint_base dest (Nat.le_refl _) (by omega)) (by decide)

theorem prefix_ok (xorOld : Bool) (n : Nat) (hn : n ≤ 128) (s : State)
    (hs : (⟨s.gpr .x1, 1024⟩ : Region) ∈ s.rd ++ s.wr)
    (hw : (⟨s.gpr .x0, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩) :
    WP isa (.block (VG.Impl.Argon2.AArch64.FillWrite.words xorOld n)) s fun t =>
      VG.Proof.Argon2.AArch64.Written t.mem (s.gpr .x0) (VG.Proof.Argon2.AArch64.FillWrite.result xorOld s.mem (s.gpr .x1) (s.gpr .x0)) n ∧
      Frame [⟨s.gpr .x0, 8 * n⟩] s.mem t.mem ∧ VG.Proof.Argon2.AArch64.FillWrite.CopyKeeps s t ∧ t.sp = s.sp := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by omega, Frame.refl _ _, CopyKeeps.refl s, rfl⟩
  | succ n ih =>
    simp only [VG.Impl.Argon2.AArch64.FillWrite.words, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨written, frame, keeps, mx⟩
    have hn' : n < 128 := by omega
    have src : t.gpr .x1 = s.gpr .x1 := keeps.1 .x1 (by decide) (by decide) (by decide) (by decide)
    have dest : t.gpr .x0 = s.gpr .x0 := keeps.1 .x0 (by decide) (by decide) (by decide) (by decide)
    have write : InRegions t.wr (off (t.gpr .x0) (8 * n)) 8 := by
      rw [dest, keeps.2.2]
      exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩
    have read : InRegions (t.rd ++ t.wr) (off (t.gpr .x1) (8 * n)) 8 := by
      rw [src, keeps.2.1, keeps.2.2]
      exact ⟨_, hs, Offset.contains_base _ (by omega) (by omega)⟩
    have old : InRegions (t.rd ++ t.wr) (off (t.gpr .x0) (8 * n)) 8 := by
      obtain ⟨r, hr, hc⟩ := write
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    refine (VG.Proof.Argon2.AArch64.FillWrite.word_ok xorOld t n hn' read write old).mono ?_
    rintro u ⟨mem, regs, rd, wr, mx'⟩
    have v : VG.Proof.Argon2.AArch64.FillWrite.value xorOld t.mem (t.gpr .x1) (t.gpr .x0) n =
        (VG.Proof.Argon2.AArch64.FillWrite.result xorOld s.mem (s.gpr .x1) (s.gpr .x0))[(⟨n, hn'⟩ : Fin 128)] := by
      rw [VG.Proof.Argon2.AArch64.FillWrite.result_get, src, dest]
      unfold VG.Proof.Argon2.AArch64.FillWrite.value
      rw [VG.Proof.Argon2.AArch64.FillWrite.source_read frame (by omega) hd ⟨n, hn'⟩]
      cases xorOld
      · rfl
      · rw [VG.Proof.Argon2.AArch64.FillWrite.old_read frame hn']
    refine ⟨?_, ?_, keeps.trans ⟨regs, rd, wr⟩, mx'.trans mx⟩
    · rw [mem, v, dest]
      exact written_step hn' written
    · rw [mem, dest]
      exact (VG.Proof.Argon2.AArch64.FillWrite.frame_extend frame (Nat.le_succ n)).writeW
        (r := ⟨s.gpr .x0, 8 * (n + 1)⟩) (by simp) _
        (Offset.contains_base _ (by omega) (by omega))

end VG.Proof.Argon2.AArch64.FillWrite

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillWriteCover`. -/
section

/-! Merged from `Proof.Argon2.AArch64.FillWrite`. -/
section
/-! Whole-block first-pass copying and later-pass XOR, with a frame proof. -/

namespace VG.Proof.Argon2.AArch64.FillWrite

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillWrite

theorem code_ok (s : State)
    (hs : (⟨s.gpr .x1, 1024⟩ : Region) ∈ s.rd ++ s.wr)
    (hw : (⟨s.gpr .x0, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩) :
    WP isa VG.Impl.Argon2.AArch64.FillWrite.code s fun t =>
      VG.Spec.Argon2.blockAt t.mem (s.gpr .x0) =
        (if s.gpr .x5 = 0 then VG.Spec.Argon2.blockAt s.mem (s.gpr .x1)
          else xorBlock (VG.Spec.Argon2.blockAt s.mem (s.gpr .x1)) (VG.Spec.Argon2.blockAt s.mem (s.gpr .x0))) ∧
      Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.AArch64.FillWrite.CopyKeeps s t ∧ t.sp = s.sp := by
  unfold VG.Impl.Argon2.AArch64.FillWrite.code
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
    refine (VG.Proof.Argon2.AArch64.FillWrite.prefix_ok false 128 (by decide) a hs' hw' hd').mono ?_
    rintro t ⟨written, frame, keeps, mx⟩
    refine ⟨?_, ?_, ?_, mx.trans ka.sp⟩
    · rw [dest] at written
      rw [ite_eq_left zero, written_block written]
      simp only [VG.Proof.Argon2.AArch64.FillWrite.result, Bool.false_eq_true, ite_false, ka.mem, src]
    · rw [dest, ka.mem] at frame; exact frame
    · exact (show VG.Proof.Argon2.AArch64.FillWrite.CopyKeeps s a from ⟨fun r _ h13 h14 h15 => ka.regs r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨h13, h14, h15⟩), ka.rd, ka.wr⟩).trans keeps
  · intro h
    have nonzero := of_decide_eq_false h
    refine (VG.Proof.Argon2.AArch64.FillWrite.prefix_ok true 128 (by decide) a hs' hw' hd').mono ?_
    rintro t ⟨written, frame, keeps, mx⟩
    refine ⟨?_, ?_, ?_, mx.trans ka.sp⟩
    · rw [dest] at written
      rw [ite_eq_right nonzero, written_block written]
      simp only [VG.Proof.Argon2.AArch64.FillWrite.result, ite_true, ka.mem, src]
    · rw [dest, ka.mem] at frame; exact frame
    · exact (show VG.Proof.Argon2.AArch64.FillWrite.CopyKeeps s a from ⟨fun r _ h13 h14 h15 => ka.regs r (by
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
    WP isa VG.Impl.Argon2.AArch64.FillWrite.code s fun t =>
      VG.Spec.Argon2.blockAt t.mem (s.gpr .x0) =
        (if s.gpr .x5 = 0 then VG.Spec.Argon2.blockAt s.mem (s.gpr .x1)
          else xorBlock (VG.Spec.Argon2.blockAt s.mem (s.gpr .x1)) (VG.Spec.Argon2.blockAt s.mem (s.gpr .x0))) ∧
      Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.AArch64.FillWrite.CopyKeeps s t ∧ t.sp = s.sp := by
  let a := s.withRegions [⟨s.gpr .x1, 1024⟩] [⟨s.gpr .x0, 1024⟩]
  obtain ⟨tr, t, he, value, frame, keeps, mx⟩ := VG.Proof.Argon2.AArch64.FillWrite.code_ok a (by simp [a]) (by simp [a]) hd
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

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillCompressOperation`. -/
section

/-! Merged from `Proof.Argon2.AArch64.FillCompressArgs`. -/
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
  call : VG.Proof.Argon2.AArch64.FillCompress.CallReady s
  frameRead : ∀ d ∈ [0, 16, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  workWord : s.mem.readW (off (s.gpr .x19) 248) 64 = s.gpr .x3
  outputPointer : s.gpr .x3 + 4096 = s.gpr .x2
  destinationWrite : Covers [⟨VG.Proof.Argon2.AArch64.FillCompress.destination s, 1024⟩] s.wr
  frameSafe : ∀ r ∈ VG.Proof.Argon2.AArch64.FillCompress.callWrites s, (⟨s.gpr .x19, 272⟩ : Region).Disjoint r
  destinationSafe : ∀ r ∈ VG.Proof.Argon2.AArch64.FillCompress.callWrites s, (⟨VG.Proof.Argon2.AArch64.FillCompress.destination s, 1024⟩ : Region).Disjoint r

structure OperationDone (s t : State) : Prop where
  block : VG.Spec.Argon2.blockAt t.mem (VG.Proof.Argon2.AArch64.FillCompress.destination s) =
    let next := Spec.Argon2.compress (VG.Spec.Argon2.blockAt s.mem (s.gpr .x0)) (VG.Spec.Argon2.blockAt s.mem (s.gpr .x1))
    if VG.Proof.Argon2.AArch64.FillCompress.pass s = 0 then next else xorBlock next (VG.Spec.Argon2.blockAt s.mem (VG.Proof.Argon2.AArch64.FillCompress.destination s))
  regs : ∀ r ∈ VG.Proof.Argon2.AArch64.FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (⟨VG.Proof.Argon2.AArch64.FillCompress.destination s, 1024⟩ :: VG.Proof.Argon2.AArch64.FillCompress.callWrites s) s.mem t.mem

theorem frame_word {s t : State} (h : VG.Proof.Argon2.AArch64.FillCompress.OperationReady s) (called : VG.Proof.Argon2.AArch64.FillCompress.Called s t)
    (d : Nat) (hd : d + 8 ≤ 272) :
    t.mem.readW (off (s.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 :=
  called.frame.readW (r := ⟨s.gpr .x19, 272⟩)
    (Offset.contains_base _ hd (by omega)) h.frameSafe (by decide)

theorem destination_unchanged {s t : State} (h : VG.Proof.Argon2.AArch64.FillCompress.OperationReady s) (called : VG.Proof.Argon2.AArch64.FillCompress.Called s t) :
    VG.Spec.Argon2.blockAt t.mem (VG.Proof.Argon2.AArch64.FillCompress.destination s) = VG.Spec.Argon2.blockAt s.mem (VG.Proof.Argon2.AArch64.FillCompress.destination s) := by
  apply Vector.ext
  intro i hi
  have read : t.mem.readW (off (VG.Proof.Argon2.AArch64.FillCompress.destination s) (8 * i)) 64 =
      s.mem.readW (off (VG.Proof.Argon2.AArch64.FillCompress.destination s) (8 * i)) 64 :=
    called.frame.readW (r := ⟨VG.Proof.Argon2.AArch64.FillCompress.destination s, 1024⟩)
      (Offset.contains_base _ (by omega) (by omega)) h.destinationSafe (by decide)
  rw [← blockAt_get t.mem (VG.Proof.Argon2.AArch64.FillCompress.destination s) ⟨i, hi⟩,
    ← blockAt_get s.mem (VG.Proof.Argon2.AArch64.FillCompress.destination s) ⟨i, hi⟩] at read
  exact read

theorem operation_ok (s : State) (h : VG.Proof.Argon2.AArch64.FillCompress.OperationReady s) :
    WP isa operation s (VG.Proof.Argon2.AArch64.FillCompress.OperationDone s) := by
  unfold operation
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillCompress.call_ok _ s h.call).mono ?_)
  intro a called
  have bp : a.gpr .x19 = s.gpr .x19 := called.regs .x19 (by simp [VG.Proof.Argon2.AArch64.FillCompress.loopRegs])
  have reads (d : Nat) (hd : d ∈ [0, 16, 248]) :
      InRegions (a.rd ++ a.wr) (off (a.gpr .x19) d) 8 := by
    rw [called.rd, called.wr, bp]; exact h.frameRead d hd
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillCompress.writeArgs_ok a (reads 16 (by simp)) (reads 248 (by simp))
    (reads 0 (by simp))).mono ?_)
  rintro b ⟨dest, src, counter, keeps⟩
  have dest' : b.gpr .x0 = VG.Proof.Argon2.AArch64.FillCompress.destination s := by
    rw [dest, bp, VG.Proof.Argon2.AArch64.FillCompress.frame_word h called 16 (by decide), VG.Proof.Argon2.AArch64.FillCompress.destination]
  have src' : b.gpr .x1 = s.gpr .x2 := by
    rw [src, bp, VG.Proof.Argon2.AArch64.FillCompress.frame_word h called 248 (by decide), h.workWord, h.outputPointer]
  have counter' : b.gpr .x5 = VG.Proof.Argon2.AArch64.FillCompress.pass s := by
    rw [counter, bp, VG.Proof.Argon2.AArch64.FillCompress.frame_word h called 0 (by decide), VG.Proof.Argon2.AArch64.FillCompress.pass]
  have readable : Covers [⟨b.gpr .x1, 1024⟩] (b.rd ++ b.wr) := by
    rw [src', keeps.rd, keeps.wr, called.rd, called.wr]
    intro p n hp
    obtain ⟨r, hr, hc⟩ := h.call.output p n hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have writable : Covers [⟨b.gpr .x0, 1024⟩] b.wr := by
    rw [dest', keeps.wr, called.wr]; exact h.destinationWrite
  have sep : (⟨b.gpr .x1, 1024⟩ : Region).Disjoint ⟨b.gpr .x0, 1024⟩ := by
    rw [src', dest']; exact (h.destinationSafe _ (by simp [VG.Proof.Argon2.AArch64.FillCompress.callWrites])).symm
  refine (FillWrite.code_cover_ok b readable writable sep).mono ?_
  rintro t ⟨value, frame, tk, tsp⟩
  refine ⟨?_, ?_, tk.2.1.trans (keeps.rd.trans called.rd),
    tk.2.2.trans (keeps.wr.trans called.wr), tsp.trans (keeps.sp.trans called.sp), ?_⟩
  · rw [dest', src', counter', keeps.mem, called.result, VG.Proof.Argon2.AArch64.FillCompress.destination_unchanged h called] at value
    exact value
  · intro r hr
    have safe : r ≠ .x8 ∧ r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x15 ∧
        r ∉ [Reg.x0, .x1, .x5, .x12, .x15] := by
      simp only [VG.Proof.Argon2.AArch64.FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (tk.1 r safe.1 safe.2.1 safe.2.2.1 safe.2.2.2.1).trans
      ((keeps.regs r safe.2.2.2.2).trans (called.regs r hr))
  · rw [dest'] at frame
    rw [keeps.mem] at frame
    exact (called.frame.mono (by intro r hr; exact List.mem_cons_of_mem _ hr)).trans
      (frame.mono (by simp))

end VG.Proof.Argon2.AArch64.FillCompress

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillCompressSetup`. -/
section

/-! Establish compression-and-write invariants from the frame and allocations. -/

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
  workWrite : Covers [⟨VG.Proof.Argon2.AArch64.FillCompress.work s, 5120⟩] s.wr
  leftWork : (⟨s.gpr .x0, 1024⟩ : Region).Disjoint ⟨VG.Proof.Argon2.AArch64.FillCompress.work s, 5120⟩
  rightWork : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨VG.Proof.Argon2.AArch64.FillCompress.work s, 5120⟩
  destinationWork : (⟨s.gpr .x6, 1024⟩ : Region).Disjoint ⟨VG.Proof.Argon2.AArch64.FillCompress.work s, 5120⟩
  frameWork : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨VG.Proof.Argon2.AArch64.FillCompress.work s, 5120⟩
  leftFrame : (⟨s.gpr .x0, 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩
  rightFrame : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩
  destinationFrame : (⟨s.gpr .x6, 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩
  stackLeft : (below s.sp 8).Disjoint ⟨s.gpr .x0, 1024⟩
  stackRight : (below s.sp 8).Disjoint ⟨s.gpr .x1, 1024⟩
  stackWork : (below s.sp 8).Disjoint ⟨VG.Proof.Argon2.AArch64.FillCompress.work s, 5120⟩
  destinationStack : (⟨s.gpr .x6, 1024⟩ : Region).Disjoint (below s.sp 8)
  frameStack : (⟨s.gpr .x19, 272⟩ : Region).Disjoint (below s.sp 8)

structure Prepared (s t : State) : Prop where
  ready : VG.Proof.Argon2.AArch64.FillCompress.OperationReady t
  dest : VG.Proof.Argon2.AArch64.FillCompress.destination t = s.gpr .x6
  counter : VG.Proof.Argon2.AArch64.FillCompress.pass t = VG.Proof.Argon2.AArch64.FillCompress.pass s
  scratch : t.gpr .x3 = VG.Proof.Argon2.AArch64.FillCompress.work s
  output : t.gpr .x2 = VG.Proof.Argon2.AArch64.FillCompress.work s + 4096
  left : t.gpr .x0 = s.gpr .x0
  right : t.gpr .x1 = s.gpr .x1
  regs : ∀ r ∈ VG.Proof.Argon2.AArch64.FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (VG.Proof.Argon2.AArch64.FillCompress.prefixWrites s) s.mem t.mem
  leftBlock : VG.Spec.Argon2.blockAt t.mem (t.gpr .x0) = VG.Spec.Argon2.blockAt s.mem (s.gpr .x0)
  rightBlock : VG.Spec.Argon2.blockAt t.mem (t.gpr .x1) = VG.Spec.Argon2.blockAt s.mem (s.gpr .x1)
  oldBlock : VG.Spec.Argon2.blockAt t.mem (VG.Proof.Argon2.AArch64.FillCompress.destination t) = VG.Spec.Argon2.blockAt s.mem (s.gpr .x6)

theorem block_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (p : Addr) (sep : ∀ r ∈ rs, (⟨p, 1024⟩ : Region).Disjoint r) :
    VG.Spec.Argon2.blockAt m' p = VG.Spec.Argon2.blockAt m p := by
  apply Vector.ext
  intro i hi
  have read : m'.readW (off p (8 * i)) 64 = m.readW (off p (8 * i)) 64 :=
    hf.readW (r := ⟨p, 1024⟩) (Offset.contains_base p (by omega) (by omega)) sep (by decide)
  rw [← blockAt_get m' p ⟨i, hi⟩, ← blockAt_get m p ⟨i, hi⟩] at read
  exact read

theorem work_cover (s : State) (h : VG.Proof.Argon2.AArch64.FillCompress.Ready s) (d n : Nat) (hd : d + n ≤ 5120) :
    Covers [⟨off (VG.Proof.Argon2.AArch64.FillCompress.work s) d, n⟩] s.wr := by
  have sub : Covers [⟨off (VG.Proof.Argon2.AArch64.FillCompress.work s) d, n⟩] [⟨VG.Proof.Argon2.AArch64.FillCompress.work s, 5120⟩] := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨VG.Proof.Argon2.AArch64.FillCompress.work s, 5120⟩, by simp, d, rfl, hd⟩
  exact fun p n hp => h.workWrite p n (sub p n hp)

theorem prepared_of_setup (s a b : State) (h : VG.Proof.Argon2.AArch64.FillCompress.Ready s)
    (mem : a.mem = s.mem.writeW (off (s.gpr .x19) 16) (s.gpr .x6))
    (regs : a.gpr = s.gpr) (rd : a.rd = s.rd) (wr : a.wr = s.wr) (sp : a.sp = s.sp)
    (scratch : b.gpr .x3 = a.mem.readW (off (a.gpr .x19) 248) 64)
    (output : b.gpr .x2 = a.mem.readW (off (a.gpr .x19) 248) 64 + 4096)
    (keeps : Divide.Keeps [.x3, .x2, .x12, .x15] a b) : VG.Proof.Argon2.AArch64.FillCompress.Prepared s b := by
  have g (r : Reg) (hr : r ∉ [Reg.x3, .x2, .x12, .x15]) : b.gpr r = s.gpr r :=
    (keeps.regs r hr).trans (congrFun regs r)
  have brd : b.rd = s.rd := keeps.rd.trans rd
  have bwr : b.wr = s.wr := keeps.wr.trans wr
  have bsp : b.sp = s.sp := keeps.sp.trans sp
  have bm : b.mem = s.mem.writeW (off (s.gpr .x19) 16) (s.gpr .x6) := keeps.mem.trans mem
  have unchanged (d : Nat) (sep : d + 8 ≤ 16 ∨ 24 ≤ d) (bound : d + 8 ≤ 272) :
      b.mem.readW (off (b.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
    rw [bm, g .x19 (by decide)]
    exact Mem.readW_writeW_sep (Offset.sep _ sep (by omega) (by decide)) (by decide)
  have work' : b.gpr .x3 = VG.Proof.Argon2.AArch64.FillCompress.work s := by
    rw [scratch, regs, mem]
    exact Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)
  have out' : b.gpr .x2 = VG.Proof.Argon2.AArch64.FillCompress.work s + 4096 := by
    rw [output, regs, mem,
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), VG.Proof.Argon2.AArch64.FillCompress.work]
  have dest : VG.Proof.Argon2.AArch64.FillCompress.destination b = s.gpr .x6 := by
    unfold VG.Proof.Argon2.AArch64.FillCompress.destination
    rw [bm, g .x19 (by decide), Mem.readW_writeW_self64]
  have counter : VG.Proof.Argon2.AArch64.FillCompress.pass b = VG.Proof.Argon2.AArch64.FillCompress.pass s := unchanged 0 (by decide) (by decide)
  have frame : Frame (VG.Proof.Argon2.AArch64.FillCompress.prefixWrites s) s.mem b.mem := by
    rw [bm]
    exact (Frame.refl _ _).writeW (r := ⟨off (s.gpr .x19) 16, 8⟩) (by simp [VG.Proof.Argon2.AArch64.FillCompress.prefixWrites]) _
      (Region.contains_self _ _)
  have cellFrame (p : Addr) (sep : (⟨p, 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩) :
      VG.Spec.Argon2.blockAt b.mem p = VG.Spec.Argon2.blockAt s.mem p :=
    VG.Proof.Argon2.AArch64.FillCompress.block_frame frame p (by
      intro r hr
      simp only [VG.Proof.Argon2.AArch64.FillCompress.prefixWrites, List.mem_singleton] at hr
      subst r
      exact sep.sub_right (Offset.sub_base _ (by decide)))
  have tempSub : Region.Sub ⟨VG.Proof.Argon2.AArch64.FillCompress.work s + 4096, 1024⟩ ⟨VG.Proof.Argon2.AArch64.FillCompress.work s, 5120⟩ :=
    Offset.sub_base _ (by decide)
  have scratchSub : Region.Sub ⟨VG.Proof.Argon2.AArch64.FillCompress.work s, 4096⟩ ⟨VG.Proof.Argon2.AArch64.FillCompress.work s, 5120⟩ := Region.sub_prefix (by decide)
  refine ⟨?_, dest, counter, work', out', g .x0 (by decide), g .x1 (by decide), ?_, brd, bwr, bsp,
    frame, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [g .x0 (by decide), brd, bwr]; exact h.leftRead
      · rw [g .x1 (by decide), brd, bwr]; exact h.rightRead
      · rw [out', bwr]; exact VG.Proof.Argon2.AArch64.FillCompress.work_cover s h 4096 1024 (by decide)
      · rw [work', bwr]
        simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
          using VG.Proof.Argon2.AArch64.FillCompress.work_cover s h 0 4096 (by decide)
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
      simp only [VG.Proof.Argon2.AArch64.FillCompress.callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [g .x19 (by decide), out']; exact h.frameWork.sub_right tempSub
      · rw [g .x19 (by decide), work']; exact h.frameWork.sub_right scratchSub
      · rw [g .x19 (by decide), bsp]; exact h.frameStack
    · intro r hr
      rw [dest]
      simp only [VG.Proof.Argon2.AArch64.FillCompress.callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [out']; exact h.destinationWork.sub_right tempSub
      · rw [work']; exact h.destinationWork.sub_right scratchSub
      · rw [bsp]; exact h.destinationStack
  · intro r hr
    apply g r
    simp only [VG.Proof.Argon2.AArch64.FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [g .x0 (by decide)]; exact cellFrame _ h.leftFrame
  · rw [g .x1 (by decide)]; exact cellFrame _ h.rightFrame
  · rw [dest]; exact cellFrame _ h.destinationFrame

theorem setup_ok (s : State) (h : VG.Proof.Argon2.AArch64.FillCompress.Ready s) :
    WP isa VG.Impl.Argon2.AArch64.FillCompress.setup s (VG.Proof.Argon2.AArch64.FillCompress.Prepared s) := by
  unfold VG.Impl.Argon2.AArch64.FillCompress.setup
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillCompress.saveCurrent_ok s h.frameWrite).mono ?_)
  rintro a ⟨mem, regs, rd, wr, sp⟩
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) 248) 8 := by
    rw [rd, wr, regs]; exact h.frameRead 248 (by simp)
  refine (VG.Proof.Argon2.AArch64.FillCompress.compressArgs_ok a read).mono ?_
  rintro b ⟨scratch, output, keeps⟩
  exact VG.Proof.Argon2.AArch64.FillCompress.prepared_of_setup s a b h mem regs rd wr sp scratch output keeps

end VG.Proof.Argon2.AArch64.FillCompress

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.Instructions`. -/
section

/-! Short register operations used by the allocation and loop drivers. -/
namespace VG.Proof.Argon2.AArch64.Instructions
open VG VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

theorem addi_ok (s : State) (d : Reg) (n : Nat) (hn : n < 65536)
    (hd : d ≠ .x12) (h15 : d ≠ .x15) :
    WP isa (.block (addi d n)) s fun t =>
      t.gpr d = s.gpr d + BitVec.ofNat 64 n ∧ Divide.Keeps [d, .x12, .x15] s t := by
  have width : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
    exact BitVec.setWidth_ofNat_of_le_of_lt (by decide) hn
  by_cases small : n < 4096
  · apply WP.of_runBlock
    simp only [addi, small, ite_true, mark, VG.Impl.Argon2.AArch64.Instructions.mov, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
      show 0 < 4096 from by decide, RegUpd.gpr_write, Size.bits,
      BitVec.setWidth_eq, BitVec.add_zero, h15,
      ite_false, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, ?_⟩
    constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2.2, ite_false]
    all_goals rfl
  · apply WP.of_runBlock
    simp only [addi, small, ite_false, imm, hn, ite_true, mark, VG.Impl.Argon2.AArch64.Instructions.mov,
      List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
      show 0 < 4096 from by decide, Size.bits, Nat.reduceMul, Nat.reduceLT,
      BitVec.shiftLeft_zero, width, RegUpd.gpr_write, BitVec.setWidth_eq,
      hd, h15, BitVec.add_zero,
      Option.some.injEq, exists_eq_left']
    refine ⟨trivial, ?_⟩
    constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
    all_goals rfl

theorem mov_ok (s : State) (d n : Reg) :
    WP isa (.block (VG.Impl.Argon2.AArch64.Instructions.mov d n)) s fun t =>
      t.gpr d = s.gpr n ∧ Divide.Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.AArch64.Instructions.mov, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    show 0 < 4096 from by decide, Size.bits, BitVec.setWidth_eq,
    BitVec.add_zero, RegUpd.gpr_write, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem load_ok (s : State) (d n : Reg) (offset : Nat)
    (ha : offset % 8 = 0) (hb : offset < 32768)
    (read : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 offset) 8) :
    WP isa (.block (load d n offset)) s fun t =>
      t.gpr d = s.mem.readW (s.gpr n + BitVec.ofNat 64 offset) 64 ∧
      Divide.Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [load, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    Size.bytes, ha, hb, and_self, ite_true, State.load, read,
    Option.map_some, Option.bind_some, RegUpd.gpr_write, BitVec.setWidth_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem pointer_ok (s : State) (d base : Reg) (n : Nat) (hn : n < 65536)
    (hd : d ≠ .x12) (h15 : d ≠ .x15) :
    WP isa (.block (VG.Impl.Argon2.AArch64.Instructions.mov d base ++ addi d n)) s fun t =>
      t.gpr d = s.gpr base + BitVec.ofNat 64 n ∧ Divide.Keeps [d, .x12, .x15] s t := by
  apply WP.block_append
  refine (VG.Proof.Argon2.AArch64.Instructions.mov_ok s d base).mono ?_
  rintro a ⟨value, keeps⟩
  refine (VG.Proof.Argon2.AArch64.Instructions.addi_ok a d n hn hd h15).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨out.trans (congrArg (· + BitVec.ofNat 64 n) value), ?_⟩
  exact (keeps.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)).trans kt

theorem compare_ok (s : State) (a b : Reg)
    (ha : (s.gpr a).toNat < 2 ^ 63) (hb : (s.gpr b).toNat < 2 ^ 63) :
    WP isa (.block (VG.Impl.Argon2.AArch64.Instructions.compare a b)) s fun t =>
      t.gpr .x14 = (BitVec.ofBool (decide ((s.gpr a).toNat < (s.gpr b).toNat))).setWidth 64 ∧
      Divide.Keeps [.x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.AArch64.Instructions.compare, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, BitVec.setWidth_eq, show (63 : Nat) < 64 from by decide,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, Bool.toNat_true, sub_value,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · rw [Divide.difference_high _ _ ha hb]
    by_cases h : (s.gpr a).toNat < (s.gpr b).toNat <;>
      simp only [h, decide_true, decide_false, ite_true, ite_false] <;> rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2, ite_false]
    all_goals rfl
theorem store_ok (s : State) (base source : Reg) (offset : Nat)
    (ha : offset % 8 = 0) (hb : offset < 32768)
    (write : InRegions s.wr (s.gpr base + BitVec.ofNat 64 offset) 8) :
    WP isa (.block (store base offset source)) s fun t =>
      t.mem = s.mem.writeW (s.gpr base + BitVec.ofNat 64 offset) (s.gpr source) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [store, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    Size.bytes, ha, hb, and_self, ite_true, State.store, write, State.read,
    BitVec.setWidth_eq, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial⟩

theorem comparem_ok (s : State) (a base : Reg) (offset : Nat)
    (ha : offset % 8 = 0) (hb : offset < 32768) (ar : a ≠ .x13)
    (read : InRegions (s.rd ++ s.wr) (s.gpr base + BitVec.ofNat 64 offset) 8)
    (left : (s.gpr a).toNat < 2 ^ 63)
    (right : (s.mem.readW (s.gpr base + BitVec.ofNat 64 offset) 64).toNat < 2 ^ 63) :
    WP isa (.block (comparem a base offset)) s fun t =>
      eval (.nonzero .x .x14) t = some (decide ((s.gpr a).toNat <
        (s.mem.readW (s.gpr base + BitVec.ofNat 64 offset) 64).toNat)) ∧
      Divide.Keeps [.x13, .x14, .x15] s t := by
  unfold comparem
  apply WP.block_append
  refine (VG.Proof.Argon2.AArch64.Instructions.load_ok s .x13 base offset ha hb read).mono ?_
  rintro u ⟨loaded, keeps⟩
  have preserved := keeps.regs a (by simpa only [List.mem_singleton] using ar)
  have leftU : (u.gpr a).toNat < 2 ^ 63 := by rw [preserved]; exact left
  have rightU : (u.gpr .x13).toNat < 2 ^ 63 := by rw [loaded]; exact right
  refine (VG.Proof.Argon2.AArch64.Instructions.compare_ok u a .x13 leftU rightU).mono ?_
  rintro t ⟨value, changed⟩
  refine ⟨?_, (keeps.mono (by decide)).trans (changed.mono (by decide))⟩
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, value, preserved, loaded]
  cases decide ((s.gpr a).toNat < (s.mem.readW (s.gpr base + BitVec.ofNat 64 offset) 64).toNat) <;> rfl

theorem add_ok (s : State) (d n : Reg) (h15 : d ≠ .x15) :
    WP isa (.block (add d n)) s fun t =>
      t.gpr d = s.gpr d + s.gpr n ∧ Divide.Keeps [d, .x15] s t := by
  apply WP.of_runBlock
  simp only [add, mark, VG.Impl.Argon2.AArch64.Instructions.mov, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 0 < 4096 from by decide, BitVec.setWidth_eq, BitVec.add_zero,
    RegUpd.gpr_write, h15, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

theorem subi_ok (s : State) (d : Reg) (n : Nat) (hn : n < 65536)
    (hd : d ≠ .x12) (h15 : d ≠ .x15) :
    WP isa (.block (subi d n)) s fun t =>
      t.gpr d = s.gpr d - BitVec.ofNat 64 n ∧
      t.gpr .x15 = s.gpr d - BitVec.ofNat 64 n ∧ Divide.Keeps [d, .x12, .x15] s t := by
  have width : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n :=
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) hn
  apply WP.of_runBlock
  simp only [subi, VG.Impl.Argon2.AArch64.Instructions.sub, imm, hn, ite_true, mark, VG.Impl.Argon2.AArch64.Instructions.mov, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 0 < 4096 from by decide, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hd, h15, width,
    sub_value, Bool.toNat_true, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.AArch64.Instructions

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.AddressCallsStage`. -/
section

/-! Merged from `Proof.Argon2.AArch64.AddressCallsLayout`. -/
section
/-! Merged from `Proof.Argon2.AArch64.AddressCallsArgs`. -/
section
/-! Independent-address compression arguments from one fixed frame read. -/
namespace VG.Proof.Argon2.AArch64.AddressCalls
open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressCalls
open VG.Impl.Argon2.AArch64

def work (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 248) 64

theorem pointer_ok (s : State) (offset : Nat) (bound : offset ≤ 8192)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8) :
    WP isa (.block (VG.Impl.Argon2.AArch64.AddressCalls.pointer offset)) s fun t =>
      t.gpr .x0 = VG.Proof.Argon2.AArch64.AddressCalls.work s + BitVec.ofNat 64 offset ∧ Divide.Keeps [.x0, .x12, .x15] s t := by
  simp only [VG.Impl.Argon2.AArch64.AddressCalls.pointer, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  apply WP.block_append
  refine (Instructions.load_ok s .x0 .x19 248 (by decide) (by decide) hr).mono ?_
  rintro a ⟨value, keeps⟩
  refine (Instructions.addi_ok a .x0 offset (by omega) (by decide) (by decide)).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨out.trans (congrArg (· + BitVec.ofNat 64 offset) value), ?_⟩
  exact (keeps.mono (by simp)).trans kt

theorem args_ok (s : State) (x y out : Nat) (hx : x ≤ 8192) (hy : y ≤ 8192) (ho : out ≤ 8192)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8) :
    WP isa (.block (VG.Impl.Argon2.AArch64.AddressCalls.args x y out)) s fun t =>
      t.gpr .x3 = VG.Proof.Argon2.AArch64.AddressCalls.work s ∧ t.gpr .x0 = VG.Proof.Argon2.AArch64.AddressCalls.work s + BitVec.ofNat 64 x ∧
      t.gpr .x1 = VG.Proof.Argon2.AArch64.AddressCalls.work s + BitVec.ofNat 64 y ∧ t.gpr .x2 = VG.Proof.Argon2.AArch64.AddressCalls.work s + BitVec.ofNat 64 out ∧
      Divide.Keeps [.x3, .x0, .x1, .x2, .x12, .x15] s t := by
  simp only [VG.Impl.Argon2.AArch64.AddressCalls.args, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  apply WP.block_append
  refine (Instructions.load_ok s .x3 .x19 248 (by decide) (by decide) hr).mono ?_
  rintro a ⟨scratch, ka⟩
  rw [← List.append_assoc (Instructions.mov .x0 .x3) (Instructions.addi .x0 x)]
  apply WP.block_append
  refine (Instructions.pointer_ok a .x0 .x3 x (by omega) (by decide) (by decide)).mono ?_
  rintro b ⟨left, kb⟩
  rw [← List.append_assoc (Instructions.mov .x1 .x3) (Instructions.addi .x1 y)]
  apply WP.block_append
  refine (Instructions.pointer_ok b .x1 .x3 y (by omega) (by decide) (by decide)).mono ?_
  rintro c ⟨right, kc⟩
  refine (Instructions.pointer_ok c .x2 .x3 out (by omega) (by decide) (by decide)).mono ?_
  rintro t ⟨output, kt⟩
  have scrB := kb.regs .x3 (by decide)
  have scrC := kc.regs .x3 (by decide)
  refine ⟨(kt.regs .x3 (by decide)).trans (scrC.trans (scrB.trans scratch)),
    (kt.regs .x0 (by decide)).trans ((kc.regs .x0 (by decide)).trans
      (left.trans (congrArg (· + BitVec.ofNat 64 x) scratch))),
    (kt.regs .x1 (by decide)).trans (right.trans (congrArg (· + BitVec.ofNat 64 y) (scrB.trans scratch))),
    output.trans (congrArg (· + BitVec.ofNat 64 out) (scrC.trans (scrB.trans scratch))), ?_⟩
  exact (ka.mono (by decide)).trans ((kb.mono (by decide)).trans
    ((kc.mono (by decide)).trans (kt.mono (by decide))))
end VG.Proof.Argon2.AArch64.AddressCalls
end

/-! Permissions and separation for either address-generation compression call. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64

structure Ready (s : State) : Prop where
  frameRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8
  workWrite : Covers [⟨VG.Proof.Argon2.AArch64.AddressCalls.work s, 8192⟩] s.wr
  frameWork : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨VG.Proof.Argon2.AArch64.AddressCalls.work s, 8192⟩
  frameStack : (⟨s.gpr .x19, 272⟩ : Region).Disjoint (below s.sp 8)
  stackWork : (below s.sp 8).Disjoint ⟨VG.Proof.Argon2.AArch64.AddressCalls.work s, 8192⟩

theorem work_cover (s : State) (h : VG.Proof.Argon2.AArch64.AddressCalls.Ready s) (d n : Nat) (hd : d + n ≤ 8192) :
    Covers [⟨off (VG.Proof.Argon2.AArch64.AddressCalls.work s) d, n⟩] s.wr := by
  have sub : Covers [⟨off (VG.Proof.Argon2.AArch64.AddressCalls.work s) d, n⟩] [⟨VG.Proof.Argon2.AArch64.AddressCalls.work s, 8192⟩] := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨VG.Proof.Argon2.AArch64.AddressCalls.work s, 8192⟩, by simp, d, rfl, hd⟩
  exact fun p n hp => h.workWrite p n (sub p n hp)

structure Args (s a : State) (x y out : Nat) : Prop where
  scratch : a.gpr .x3 = VG.Proof.Argon2.AArch64.AddressCalls.work s
  left : a.gpr .x0 = off (VG.Proof.Argon2.AArch64.AddressCalls.work s) x
  right : a.gpr .x1 = off (VG.Proof.Argon2.AArch64.AddressCalls.work s) y
  output : a.gpr .x2 = off (VG.Proof.Argon2.AArch64.AddressCalls.work s) out
  keeps : Divide.Keeps [.x3, .x0, .x1, .x2, .x12, .x15] s a

theorem args_nat_ok (s : State) (h : VG.Proof.Argon2.AArch64.AddressCalls.Ready s) (x y out : Nat)
    (hx : x ≤ 8192) (hy : y ≤ 8192) (ho : out ≤ 8192) :
    WP isa (.block (Impl.Argon2.AArch64.AddressCalls.args x y out)) s (VG.Proof.Argon2.AArch64.AddressCalls.Args s · x y out) := by
  refine (VG.Proof.Argon2.AArch64.AddressCalls.args_ok s x y out hx hy ho h.frameRead).mono ?_
  rintro a ⟨scratch, left, right, output, keeps⟩
  exact ⟨scratch, left, right, output, keeps⟩

theorem args_call_ready (s a : State) (h : VG.Proof.Argon2.AArch64.AddressCalls.Ready s) (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192)
    (args : VG.Proof.Argon2.AArch64.AddressCalls.Args s a x y out) : FillCompress.CallReady a := by
  have read (d : Nat) (hd : d + 1024 ≤ 8192) :
      Covers [⟨off (VG.Proof.Argon2.AArch64.AddressCalls.work s) d, 1024⟩] (a.rd ++ a.wr) := by
    rw [args.keeps.rd, args.keeps.wr]
    intro p n hp
    obtain ⟨r, hr, hc⟩ := VG.Proof.Argon2.AArch64.AddressCalls.work_cover s h d 1024 hd p n hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have sp : a.sp = s.sp := args.keeps.sp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [args.left]; exact read x bx
  · rw [args.right]; exact read y by_
  · rw [args.output, args.keeps.wr]; exact VG.Proof.Argon2.AArch64.AddressCalls.work_cover s h out 1024 bo
  · rw [args.scratch, args.keeps.wr]
    simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
      using VG.Proof.Argon2.AArch64.AddressCalls.work_cover s h 0 4096 (by decide)
  · rw [args.left, args.scratch]; exact Offset.disjoint_base _ hx (by omega)
  · rw [args.right, args.scratch]; exact Offset.disjoint_base _ hy (by omega)
  · rw [args.output, args.scratch]; exact Offset.disjoint_base _ ho (by omega)
  · rw [sp, args.left]; exact h.stackWork.sub_right (Offset.sub_base _ bx)
  · rw [sp, args.right]; exact h.stackWork.sub_right (Offset.sub_base _ by_)
  · rw [sp, args.output]; exact h.stackWork.sub_right (Offset.sub_base _ bo)
  · rw [sp, args.scratch]; exact h.stackWork.sub_right (Region.sub_prefix (by decide))

end VG.Proof.Argon2.AArch64.AddressCalls
end

/-! One verified G call within the independent-address scratch layout. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCalls

def stageWrites (s : State) (out : Nat) : List Region :=
  [⟨off (VG.Proof.Argon2.AArch64.AddressCalls.work s) out, 1024⟩, ⟨VG.Proof.Argon2.AArch64.AddressCalls.work s, 4096⟩, below s.sp 8]

structure StageDone (s t : State) (x y out : Nat) : Prop where
  result : VG.Spec.Argon2.blockAt t.mem (off (VG.Proof.Argon2.AArch64.AddressCalls.work s) out) = Spec.Argon2.compress
    (VG.Spec.Argon2.blockAt s.mem (off (VG.Proof.Argon2.AArch64.AddressCalls.work s) x)) (VG.Spec.Argon2.blockAt s.mem (off (VG.Proof.Argon2.AArch64.AddressCalls.work s) y))
  ready : VG.Proof.Argon2.AArch64.AddressCalls.Ready t
  work : VG.Proof.Argon2.AArch64.AddressCalls.work t = VG.Proof.Argon2.AArch64.AddressCalls.work s
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (VG.Proof.Argon2.AArch64.AddressCalls.stageWrites s out) s.mem t.mem

theorem Args.callee {s a : State} {x y out : Nat} (h : VG.Proof.Argon2.AArch64.AddressCalls.Args s a x y out)
    (r : Reg) (hr : r ∈ FillCompress.loopRegs) : a.gpr r = s.gpr r := by
  apply h.keeps.regs
  simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem ready_of_frame {s t : State} (h : VG.Proof.Argon2.AArch64.AddressCalls.Ready s) (out : Nat) (ho : out + 1024 ≤ 8192)
    (regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r) (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp)
    (frame : Frame (VG.Proof.Argon2.AArch64.AddressCalls.stageWrites s out) s.mem t.mem) : VG.Proof.Argon2.AArch64.AddressCalls.Ready t ∧ VG.Proof.Argon2.AArch64.AddressCalls.work t = VG.Proof.Argon2.AArch64.AddressCalls.work s := by
  have bp := regs .x19 (by simp [FillCompress.loopRegs])
  have safe : ∀ r ∈ VG.Proof.Argon2.AArch64.AddressCalls.stageWrites s out, (⟨s.gpr .x19, 272⟩ : Region).Disjoint r := by
    intro r hr
    simp only [VG.Proof.Argon2.AArch64.AddressCalls.stageWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.frameWork.sub_right (Offset.sub_base _ ho)
    · exact h.frameWork.sub_right (Region.sub_prefix (by decide))
    · exact h.frameStack
  have read : t.mem.readW (off (s.gpr .x19) 248) 64 = s.mem.readW (off (s.gpr .x19) 248) 64 :=
    frame.readW (r := ⟨s.gpr .x19, 272⟩)
      (Offset.contains_base _ (by decide) (by decide)) safe (by decide)
  have work' : VG.Proof.Argon2.AArch64.AddressCalls.work t = VG.Proof.Argon2.AArch64.AddressCalls.work s := by unfold VG.Proof.Argon2.AArch64.AddressCalls.work; rw [bp, read]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, work'⟩
  · rw [rd, wr, bp]; exact h.frameRead
  · rw [work', wr]; exact h.workWrite
  · rw [bp, work']; exact h.frameWork
  · rw [bp, sp]; exact h.frameStack
  · rw [sp, work']; exact h.stackWork

theorem stage_ok (s : State) (h : VG.Proof.Argon2.AArch64.AddressCalls.Ready s) (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192) :
    WP isa (stage x y out) s (VG.Proof.Argon2.AArch64.AddressCalls.StageDone s · x y out) := by
  unfold stage
  refine WP.seq ((VG.Proof.Argon2.AArch64.AddressCalls.args_nat_ok s h x y out (by omega) (by omega) (by omega)).mono ?_)
  intro a args
  have callReady := VG.Proof.Argon2.AArch64.AddressCalls.args_call_ready s a h x y out hx hy ho bx by_ bo args
  refine (FillCompress.call_ok _ a callReady).mono ?_
  intro t called
  have regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r :=
    fun r hr => (called.regs r hr).trans (args.callee r hr)
  have rd := called.rd.trans args.keeps.rd
  have wr := called.wr.trans args.keeps.wr
  have sp := called.sp.trans args.keeps.sp
  have frame : Frame (VG.Proof.Argon2.AArch64.AddressCalls.stageWrites s out) s.mem t.mem := by
    have hf := called.frame
    rw [args.output, args.scratch, args.keeps.sp, args.keeps.mem] at hf
    exact hf
  obtain ⟨ready, work'⟩ := VG.Proof.Argon2.AArch64.AddressCalls.ready_of_frame h out bo regs rd wr sp frame
  refine ⟨?_, ready, work', regs, rd, wr, sp, frame⟩
  have result := called.result
  rw [args.output, args.left, args.right, args.keeps.mem] at result
  exact result

end VG.Proof.Argon2.AArch64.AddressCalls

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.AddressCallsPrepare`. -/
section

/-! Merged from `Proof.Argon2.AArch64.AddressHeaderCorrect`. -/
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
  | n + 1 => (VG.Proof.Argon2.AArch64.AddressHeader.headerMem s p n).writeW (off p (8 * n)) (VG.Proof.Argon2.AArch64.AddressHeader.value s n)

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
      t.mem = s.mem.writeW (off (s.gpr .x0) (8 * i)) (VG.Proof.Argon2.AArch64.AddressHeader.value s i) ∧
      VG.Proof.Argon2.AArch64.CopyKeeps s t ∧ t.sp = s.sp := by
  unfold field VG.Proof.Argon2.AArch64.AddressHeader.value
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
      refine (frameWord_ok s i (frameOffset i) (by omega) (VG.Proof.Argon2.AArch64.AddressHeader.offset_aligned i) (VG.Proof.Argon2.AArch64.AddressHeader.offset_bound i hi) hr hw).mono ?_
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

theorem value_kept {s t : State} (keeps : VG.Proof.Argon2.AArch64.CopyKeeps s t)
    (hf : Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem)
    (sep : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩)
    (i : Nat) (hi : i < 7) : VG.Proof.Argon2.AArch64.AddressHeader.value t i = VG.Proof.Argon2.AArch64.AddressHeader.value s i := by
  unfold VG.Proof.Argon2.AArch64.AddressHeader.value
  rw [keeps.1 .x24 (by decide) (by decide), keeps.1 .x22 (by decide) (by decide), keeps.1 .x19 (by decide) (by decide)]
  have read : t.mem.readW (off (s.gpr .x19) (frameOffset i)) 64 =
      s.mem.readW (off (s.gpr .x19) (frameOffset i)) 64 :=
    hf.readW (r := ⟨s.gpr .x19, 272⟩)
      (Offset.contains_base _ (VG.Proof.Argon2.AArch64.AddressHeader.offset_bound i hi)
        (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) (VG.Proof.Argon2.AArch64.AddressHeader.offset_bound i hi)) (by decide)))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sep) (by decide)
  rw [read]

theorem prefix_ok (n : Nat) (hn : n ≤ 7) (s : State)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8)
    (write : Covers [⟨s.gpr .x0, 1024⟩] s.wr)
    (sep : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩) :
    WP isa (.block (fields n)) s fun t =>
      t.mem = VG.Proof.Argon2.AArch64.AddressHeader.headerMem s (s.gpr .x0) n ∧
      Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.AArch64.CopyKeeps s t ∧ t.sp = s.sp := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, Frame.refl _ _, CopyKeeps.refl s, rfl⟩
  | succ n ih =>
    simp only [fields, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro a ⟨mem, frame, keeps, mx⟩
    have dest : a.gpr .x0 = s.gpr .x0 := keeps.1 .x0 (by decide) (by decide)
    have read : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) (frameOffset n)) 8 := by
      rw [keeps.2.1, keeps.2.2, keeps.1 .x19 (by decide) (by decide)]
      exact VG.Proof.Argon2.AArch64.AddressHeader.offset_read s n reads
    have writable : InRegions a.wr (off (a.gpr .x0) (8 * n)) 8 := by
      rw [dest, keeps.2.2]
      exact write _ _ ⟨⟨s.gpr .x0, 1024⟩, by simp,
        Offset.contains_base _ (d := 8 * n) (n := 8) (k := 1024) (by omega) (by omega)⟩
    refine (VG.Proof.Argon2.AArch64.AddressHeader.field_ok a n (by omega) read writable).mono ?_
    rintro t ⟨mem', keeps', mx'⟩
    have value' := VG.Proof.Argon2.AArch64.AddressHeader.value_kept keeps frame sep n (by omega)
    refine ⟨?_, ?_, keeps.trans keeps', mx'.trans mx⟩
    · rw [mem', dest, value', mem]
      rfl
    · rw [mem', dest]
      exact frame.writeW (r := ⟨s.gpr .x0, 1024⟩) (by simp) _
        (Offset.contains_base _ (by omega) (by omega))

end VG.Proof.Argon2.AArch64.AddressHeader
end

/-! The prepared input agrees with RFC 9106's seven public address words. -/

namespace VG.Proof.Argon2.AArch64.AddressHeader

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressHeader

def input (s : State) : Block :=
  zeroBlock |>.set 0 (VG.Proof.Argon2.AArch64.AddressHeader.value s 0) |>.set 1 (VG.Proof.Argon2.AArch64.AddressHeader.value s 1) |>.set 2 (VG.Proof.Argon2.AArch64.AddressHeader.value s 2)
    |>.set 3 (VG.Proof.Argon2.AArch64.AddressHeader.value s 3) |>.set 4 (VG.Proof.Argon2.AArch64.AddressHeader.value s 4) |>.set 5 (VG.Proof.Argon2.AArch64.AddressHeader.value s 5) |>.set 6 (VG.Proof.Argon2.AArch64.AddressHeader.value s 6)

theorem headerMem_block (s : State) (p : Addr) (zero : blockAt s.mem p = zeroBlock) :
    blockAt (VG.Proof.Argon2.AArch64.AddressHeader.headerMem s p 7) p = VG.Proof.Argon2.AArch64.AddressHeader.input s := by
  rw [VG.Proof.Argon2.AArch64.AddressHeader.headerMem, blockAt_write_nat _ p 6 (by decide),
    VG.Proof.Argon2.AArch64.AddressHeader.headerMem, blockAt_write_nat _ p 5 (by decide),
    VG.Proof.Argon2.AArch64.AddressHeader.headerMem, blockAt_write_nat _ p 4 (by decide),
    VG.Proof.Argon2.AArch64.AddressHeader.headerMem, blockAt_write_nat _ p 3 (by decide),
    VG.Proof.Argon2.AArch64.AddressHeader.headerMem, blockAt_write_nat _ p 2 (by decide),
    VG.Proof.Argon2.AArch64.AddressHeader.headerMem, blockAt_write_nat _ p 1 (by decide),
    VG.Proof.Argon2.AArch64.AddressHeader.headerMem, blockAt_write_nat _ p 0 (by decide), VG.Proof.Argon2.AArch64.AddressHeader.headerMem, zero]
  rfl

theorem code_ok (s : State)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8)
    (write : Covers [⟨s.gpr .x0, 1024⟩] s.wr)
    (sep : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩)
    (zero : blockAt s.mem (s.gpr .x0) = zeroBlock) :
    WP isa VG.Impl.Argon2.AArch64.AddressHeader.code s fun t => blockAt t.mem (s.gpr .x0) = VG.Proof.Argon2.AArch64.AddressHeader.input s ∧
      Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.AArch64.CopyKeeps s t ∧ t.sp = s.sp := by
  refine (VG.Proof.Argon2.AArch64.AddressHeader.prefix_ok 7 (by decide) s reads write sep).mono ?_
  rintro t ⟨mem, frame, keeps, mx⟩
  exact ⟨by rw [mem]; exact VG.Proof.Argon2.AArch64.AddressHeader.headerMem_block s _ zero, frame, keeps, mx⟩

structure Words (p : Params) (pass lane slice counter : Nat) (s : State) : Prop where
  passWord : s.mem.readW (off (s.gpr .x19) 0) 64 = BitVec.ofNat 64 pass
  laneWord : s.gpr .x24 = BitVec.ofNat 64 lane
  sliceWord : s.gpr .x22 = BitVec.ofNat 64 slice
  blocksWord : s.mem.readW (off (s.gpr .x19) 240) 64 = BitVec.ofNat 64 p.blocks
  passesWord : s.mem.readW (off (s.gpr .x19) 72) 64 = BitVec.ofNat 64 p.passes
  variantWord : s.mem.readW (off (s.gpr .x19) 112) 64 = BitVec.ofNat 64 p.variant.code
  counterWord : s.mem.readW (off (s.gpr .x19) 8) 64 = BitVec.ofNat 64 counter

theorem input_spec (p : Params) (pass lane slice counter : Nat) (s : State)
    (h : VG.Proof.Argon2.AArch64.AddressHeader.Words p pass lane slice counter s) :
    VG.Proof.Argon2.AArch64.AddressHeader.input s = Proof.Argon2.addressInput p pass lane slice counter := by
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceEqDiff, VG.Proof.Argon2.AArch64.AddressHeader.input, VG.Proof.Argon2.AArch64.AddressHeader.value, frameOffset,
    h.passWord, h.laneWord, h.sliceWord, h.blocksWord,
    h.passesWord, h.variantWord, h.counterWord, Proof.Argon2.addressInput]

theorem code_spec_ok (p : Params) (pass lane slice counter : Nat) (s : State)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8)
    (write : Covers [⟨s.gpr .x0, 1024⟩] s.wr)
    (sep : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩)
    (zero : blockAt s.mem (s.gpr .x0) = zeroBlock)
    (words : VG.Proof.Argon2.AArch64.AddressHeader.Words p pass lane slice counter s) :
    WP isa VG.Impl.Argon2.AArch64.AddressHeader.code s fun t =>
      blockAt t.mem (s.gpr .x0) = Proof.Argon2.addressInput p pass lane slice counter ∧
      Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.AArch64.CopyKeeps s t ∧ t.sp = s.sp :=
  (VG.Proof.Argon2.AArch64.AddressHeader.code_ok s reads write sep zero).mono (fun _ h =>
    ⟨h.1.trans (VG.Proof.Argon2.AArch64.AddressHeader.input_spec p pass lane slice counter s words), h.2⟩)

end VG.Proof.Argon2.AArch64.AddressHeader
end

/-! Merged from `Proof.Argon2.AArch64.AddressCallsClear`. -/
section
/-! Clear an address-generation block, retaining the allocation invariants. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCalls

structure Cleared (s t : State) (offset : Nat) : Prop where
  block : blockAt t.mem (off (VG.Proof.Argon2.AArch64.AddressCalls.work s) offset) = zeroBlock
  ready : VG.Proof.Argon2.AArch64.AddressCalls.Ready t
  work_eq : VG.Proof.Argon2.AArch64.AddressCalls.work t = VG.Proof.Argon2.AArch64.AddressCalls.work s
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨off (VG.Proof.Argon2.AArch64.AddressCalls.work s) offset, 1024⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem clearAt_ok (s : State) (h : VG.Proof.Argon2.AArch64.AddressCalls.Ready s) (offset : Nat) (bound : offset + 1024 ≤ 8192) :
    WP isa (clearAt offset) s (VG.Proof.Argon2.AArch64.AddressCalls.Cleared s · offset) := by
  unfold clearAt
  refine WP.seq ((VG.Proof.Argon2.AArch64.AddressCalls.pointer_ok s offset (by omega) h.frameRead).mono ?_)
  rintro a ⟨dest, keeps⟩
  have write : Covers [⟨a.gpr .x0, 1024⟩] a.wr := by
    rw [dest, keeps.wr]; exact VG.Proof.Argon2.AArch64.AddressCalls.work_cover s h offset 1024 bound
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
  have hf : Frame [⟨off (VG.Proof.Argon2.AArch64.AddressCalls.work s) offset, 1024⟩] s.mem t.mem := by
    rw [dest, keeps.mem] at frame; exact frame
  have bigger : Frame (VG.Proof.Argon2.AArch64.AddressCalls.stageWrites s offset) s.mem t.mem :=
    hf.mono (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      simp [VG.Proof.Argon2.AArch64.AddressCalls.stageWrites])
  obtain ⟨ready, work'⟩ := VG.Proof.Argon2.AArch64.AddressCalls.ready_of_frame h offset bound regs rd wr (mx.trans keeps.sp) bigger
  rw [dest] at zero
  exact ⟨zero, ready, work', regs, rd, wr, hf, mx.trans keeps.sp⟩

theorem Cleared.full_frame {s t : State} {offset : Nat} (h : VG.Proof.Argon2.AArch64.AddressCalls.Cleared s t offset)
    (bound : offset + 1024 ≤ 8192) : Frame [⟨VG.Proof.Argon2.AArch64.AddressCalls.work s, 8192⟩] s.mem t.mem := by
  apply h.frame.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨VG.Proof.Argon2.AArch64.AddressCalls.work s, 8192⟩, by simp, Offset.sub_base _ bound⟩

theorem frame_word {s t : State} (h : VG.Proof.Argon2.AArch64.AddressCalls.Ready s) (frame : Frame [⟨VG.Proof.Argon2.AArch64.AddressCalls.work s, 8192⟩] s.mem t.mem)
    (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (s.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 :=
  frame.readW (r := ⟨s.gpr .x19, 272⟩) (Offset.contains_base _ bound (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.frameWork) (by decide)

end VG.Proof.Argon2.AArch64.AddressCalls
end

/-! Prepare the independent-address input and zero block from arbitrary scratch. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCalls

structure Stable (s t : State) : Prop where
  ready : VG.Proof.Argon2.AArch64.AddressCalls.Ready t
  work_eq : VG.Proof.Argon2.AArch64.AddressCalls.work t = VG.Proof.Argon2.AArch64.AddressCalls.work s
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨VG.Proof.Argon2.AArch64.AddressCalls.work s, 8192⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem Stable.trans {s a t : State} (h : VG.Proof.Argon2.AArch64.AddressCalls.Stable s a) (k : VG.Proof.Argon2.AArch64.AddressCalls.Stable a t) : VG.Proof.Argon2.AArch64.AddressCalls.Stable s t := by
  have hf := k.frame
  rw [h.work_eq] at hf
  exact ⟨k.ready, k.work_eq.trans h.work_eq, fun r hr => (k.regs r hr).trans (h.regs r hr),
    k.rd.trans h.rd, k.wr.trans h.wr, h.frame.trans hf, k.sp.trans h.sp⟩

theorem Cleared.stable {s t : State} {offset : Nat} (h : VG.Proof.Argon2.AArch64.AddressCalls.Cleared s t offset)
    (bound : offset + 1024 ≤ 8192) : VG.Proof.Argon2.AArch64.AddressCalls.Stable s t :=
  ⟨h.ready, h.work_eq, h.regs, h.rd, h.wr, h.full_frame bound, h.sp⟩

theorem stable_of_frame {s t : State} (h : VG.Proof.Argon2.AArch64.AddressCalls.Ready s)
    (regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (frame : Frame [⟨VG.Proof.Argon2.AArch64.AddressCalls.work s, 8192⟩] s.mem t.mem) (mx : t.sp = s.sp) : VG.Proof.Argon2.AArch64.AddressCalls.Stable s t := by
  have bp := regs .x19 (by simp [FillCompress.loopRegs])
  have sp := mx
  have work' : VG.Proof.Argon2.AArch64.AddressCalls.work t = VG.Proof.Argon2.AArch64.AddressCalls.work s := by
    unfold VG.Proof.Argon2.AArch64.AddressCalls.work
    rw [bp, VG.Proof.Argon2.AArch64.AddressCalls.frame_word h frame 248 (by decide)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, work', regs, rd, wr, frame, mx⟩
  · rw [rd, wr, bp]; exact h.frameRead
  · rw [work', wr]; exact h.workWrite
  · rw [bp, work']; exact h.frameWork
  · rw [bp, sp]; exact h.frameStack
  · rw [sp, work']; exact h.stackWork

theorem Stable.reads {s t : State} (h : VG.Proof.Argon2.AArch64.AddressCalls.Stable s t)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8) :
    ∀ d ∈ [0, 8, 72, 112, 240], InRegions (t.rd ++ t.wr) (off (t.gpr .x19) d) 8 := by
  rw [h.rd, h.wr, h.regs .x19 (by simp [FillCompress.loopRegs])]
  exact reads

theorem Stable.words {s t : State} {p : Params} {pass lane slice counter : Nat} (ready : VG.Proof.Argon2.AArch64.AddressCalls.Ready s) (h : VG.Proof.Argon2.AArch64.AddressCalls.Stable s t)
    (words : AddressHeader.Words p pass lane slice counter s) :
    AddressHeader.Words p pass lane slice counter t := by
  have bp := h.regs .x19 (by simp [FillCompress.loopRegs])
  have read (d : Nat) (hd : d + 8 ≤ 272) :
      t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
    rw [bp]; exact VG.Proof.Argon2.AArch64.AddressCalls.frame_word ready h.frame d hd
  exact ⟨(read 0 (by decide)).trans words.passWord,
    (h.regs .x24 (by simp [FillCompress.loopRegs])).trans words.laneWord,
    (h.regs .x22 (by simp [FillCompress.loopRegs])).trans words.sliceWord,
    (read 240 (by decide)).trans words.blocksWord,
    (read 72 (by decide)).trans words.passesWord,
    (read 112 (by decide)).trans words.variantWord,
    (read 8 (by decide)).trans words.counterWord⟩

theorem pointer_stable {s a : State} (h : VG.Proof.Argon2.AArch64.AddressCalls.Ready s)
    (k : Divide.Keeps [.x0, .x12, .x15] s a) : VG.Proof.Argon2.AArch64.AddressCalls.Stable s a := by
  apply VG.Proof.Argon2.AArch64.AddressCalls.stable_of_frame h _ k.rd k.wr _ k.sp
  · intro r hr
    apply k.regs
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [k.mem]; exact Frame.refl _ _

theorem Stable.input {s t : State} (ready : VG.Proof.Argon2.AArch64.AddressCalls.Ready s) (h : VG.Proof.Argon2.AArch64.AddressCalls.Stable s t) :
    AddressHeader.input t = AddressHeader.input s := by
  have value (i : Nat) (hi : i < 7) : AddressHeader.value t i = AddressHeader.value s i := by
    unfold AddressHeader.value
    rw [h.regs .x24 (by simp [FillCompress.loopRegs]), h.regs .x22 (by simp [FillCompress.loopRegs]),
      h.regs .x19 (by simp [FillCompress.loopRegs]),
      VG.Proof.Argon2.AArch64.AddressCalls.frame_word ready h.frame (Impl.Argon2.AArch64.AddressHeader.frameOffset i)
        (AddressHeader.offset_bound i hi)]
  unfold AddressHeader.input
  rw [value 0 (by decide), value 1 (by decide), value 2 (by decide), value 3 (by decide),
    value 4 (by decide), value 5 (by decide), value 6 (by decide)]

structure PreparedInput (s t : State) : Prop where
  stable : VG.Proof.Argon2.AArch64.AddressCalls.Stable s t
  zero : blockAt t.mem (off (VG.Proof.Argon2.AArch64.AddressCalls.work s) 7168) = zeroBlock
  input : blockAt t.mem (off (VG.Proof.Argon2.AArch64.AddressCalls.work s) 5120) = AddressHeader.input s

structure Prepared (s t : State) (p : Params) (pass lane slice counter : Nat) : Prop where
  stable : VG.Proof.Argon2.AArch64.AddressCalls.Stable s t
  zero : blockAt t.mem (off (VG.Proof.Argon2.AArch64.AddressCalls.work s) 7168) = zeroBlock
  input : blockAt t.mem (off (VG.Proof.Argon2.AArch64.AddressCalls.work s) 5120) = Proof.Argon2.addressInput p pass lane slice counter

theorem prepare_layout_ok (s : State) (h : VG.Proof.Argon2.AArch64.AddressCalls.Ready s)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8)
    : WP isa VG.Impl.Argon2.AArch64.AddressCalls.prepare s (VG.Proof.Argon2.AArch64.AddressCalls.PreparedInput s) := by
  unfold VG.Impl.Argon2.AArch64.AddressCalls.prepare
  refine WP.seq ((VG.Proof.Argon2.AArch64.AddressCalls.clearAt_ok s h 5120 (by decide)).mono ?_)
  intro a inputClear
  refine WP.seq ((VG.Proof.Argon2.AArch64.AddressCalls.clearAt_ok a inputClear.ready 7168 (by decide)).mono ?_)
  intro b zeroClear
  have stableB := (inputClear.stable (by decide)).trans (zeroClear.stable (by decide))
  have inputZero : blockAt b.mem (off (VG.Proof.Argon2.AArch64.AddressCalls.work s) 5120) = zeroBlock := by
    have kept := FillCompress.block_frame zeroClear.frame (p := off (VG.Proof.Argon2.AArch64.AddressCalls.work s) 5120) (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      rw [inputClear.work_eq]
      exact Offset.disjoint _ (by decide) (by decide) (by decide))
    exact kept.trans inputClear.block
  refine WP.seq ((VG.Proof.Argon2.AArch64.AddressCalls.pointer_ok b 5120 (by decide) zeroClear.ready.frameRead).mono ?_)
  rintro c ⟨dest, keeps⟩
  have stableC := stableB.trans (VG.Proof.Argon2.AArch64.AddressCalls.pointer_stable zeroClear.ready keeps)
  have dest' : c.gpr .x0 = off (VG.Proof.Argon2.AArch64.AddressCalls.work s) 5120 := by rw [dest, stableB.work_eq]
  have write : Covers [⟨c.gpr .x0, 1024⟩] c.wr := by
    rw [dest, keeps.wr]; exact VG.Proof.Argon2.AArch64.AddressCalls.work_cover b zeroClear.ready 5120 1024 (by decide)
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
  have frame' : Frame [⟨VG.Proof.Argon2.AArch64.AddressCalls.work c, 8192⟩] c.mem t.mem := by
    apply frame.sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    refine ⟨⟨VG.Proof.Argon2.AArch64.AddressCalls.work c, 8192⟩, by simp, ?_⟩
    rw [dest', stableC.work_eq]
    exact Offset.sub_base _ (by decide)
  have stableT := stableC.trans (VG.Proof.Argon2.AArch64.AddressCalls.stable_of_frame stableC.ready regs tk.2.1 tk.2.2 frame' mx)
  refine ⟨stableT, ?_, ?_⟩
  · have kept := FillCompress.block_frame frame (p := off (VG.Proof.Argon2.AArch64.AddressCalls.work s) 7168) (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      rw [dest']
      exact Offset.disjoint _ (by decide) (by decide) (by decide))
    rw [kept, keeps.mem, ← inputClear.work_eq]
    exact zeroClear.block
  · rw [dest'] at input
    exact input.trans (stableC.input h)

theorem prepare_ok (p : Params) (pass lane slice counter : Nat) (s : State) (h : VG.Proof.Argon2.AArch64.AddressCalls.Ready s)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8)
    (words : AddressHeader.Words p pass lane slice counter s) :
    WP isa VG.Impl.Argon2.AArch64.AddressCalls.prepare s (VG.Proof.Argon2.AArch64.AddressCalls.Prepared s · p pass lane slice counter) :=
  (VG.Proof.Argon2.AArch64.AddressCalls.prepare_layout_ok s h reads).mono (fun _ k =>
    ⟨k.stable, k.zero, k.input.trans (AddressHeader.input_spec p pass lane slice counter s words)⟩)

end VG.Proof.Argon2.AArch64.AddressCalls

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.AddressCacheMeta`. -/
section

/-! Public cache counters and indexed-word arguments. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressCache
open VG.Impl.Argon2.AArch64

def counter (index : Addr) : Addr := (index >>> 7) + 1

theorem check_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 8) 8) :
    WP isa (.block VG.Impl.Argon2.AArch64.AddressCache.check) s fun t => t.gpr .x8 = VG.Proof.Argon2.AArch64.AddressCache.counter (s.gpr .x23) ∧
      t.gpr .x15 = VG.Proof.Argon2.AArch64.AddressCache.counter (s.gpr .x23) - s.mem.readW (off (s.gpr .x19) 8) 64 ∧
      Divide.Keeps [.x8, .x13, .x14, .x15] s t := by
  simp only [off] at hr
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.AArch64.AddressCache.check, VG.Proof.Argon2.AArch64.AddressCache.counter, Instructions.mov, Instructions.shr, Instructions.mark,
    Instructions.addi, Instructions.comparem, Instructions.compare, Instructions.load,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, addr, State.load, Size.bytes, Size.bits,
    show 8 % 8 = 0 ∧ 8 < 4096 * 8 from by decide,
    show (7 : Nat) < 64 from by decide, show (63 : Nat) < 64 from by decide,
    show 0 < 4096 from by decide, show 1 < 4096 from by decide,
    hr, and_self, ite_true, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.gpr_addWithCarry,
    sub_value, Bool.toNat_true, BitVec.setWidth_eq,
    reduceCtorEq, ite_false, BitVec.add_zero,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem counter_nat (index : Addr) : VG.Proof.Argon2.AArch64.AddressCache.counter index = BitVec.ofNat 64 (index.toNat / 128 + 1) := by
  have shifted : index >>> 7 = BitVec.ofNat 64 (index.toNat / 128) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := index.isLt; omega)]
  unfold VG.Proof.Argon2.AArch64.AddressCache.counter
  rw [shifted]
  exact (BitVec.ofNat_add _ _).symm

theorem counter_ne_zero (index : Addr) : VG.Proof.Argon2.AArch64.AddressCache.counter index ≠ 0 := by
  have bound : index.toNat / 128 + 1 < 2 ^ 64 := by have := index.isLt; omega
  intro h
  have nat := congrArg BitVec.toNat h
  rw [VG.Proof.Argon2.AArch64.AddressCache.counter_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at nat
  change index.toNat / 128 + 1 = 0 at nat
  omega

theorem wordArgs_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8) :
    WP isa (.block wordArgs) s fun t => t.gpr .x3 = AddressCalls.work s ∧
      t.gpr .x8 = s.gpr .x23 &&& 127 ∧ Divide.Keeps [.x3, .x8, .x12, .x15] s t := by
  simp only [off] at hr
  apply WP.of_runBlock
  simp only [wordArgs, AddressCalls.work, off, Instructions.mov, Instructions.load,
    Instructions.logici, Instructions.logic, Instructions.imm, Instructions.mark,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, addr, State.load, Size.bytes, Size.bits,
    show 248 % 8 = 0 ∧ 248 < 4096 * 8 from by decide,
    show 0 < 4096 from by decide, show 127 < 65536 from by decide,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero, hr, and_self, ite_true,
    RegUpd.gpr_write,
    BitVec.setWidth_eq, reduceCtorEq, ite_false, BitVec.add_zero,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem index_nat (index : Addr) : index &&& 127 = BitVec.ofNat 64 (index.toNat % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Nat.and_two_pow_sub_one_eq_mod index.toNat 7

end VG.Proof.Argon2.AArch64.AddressCache

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.AddressCalls`. -/
section

/-! Both compression calls produce exactly the reviewed independent-address block. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCalls

def writes (s : State) : List Region := [⟨VG.Proof.Argon2.AArch64.AddressCalls.work s, 8192⟩, below s.sp 8]

structure Generated (s t : State) (p : VG.Spec.Argon2.Params) (pass lane slice counter : Nat) : Prop where
  block : VG.Spec.Argon2.blockAt t.mem (off (VG.Proof.Argon2.AArch64.AddressCalls.work s) 6144) = addressBlock p pass lane slice counter
  ready : VG.Proof.Argon2.AArch64.AddressCalls.Ready t
  work : VG.Proof.Argon2.AArch64.AddressCalls.work t = VG.Proof.Argon2.AArch64.AddressCalls.work s
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (VG.Proof.Argon2.AArch64.AddressCalls.writes s) s.mem t.mem

theorem stage_frame_full {s t : State} {out : Nat} (bound : out + 1024 ≤ 8192)
    (hf : Frame (VG.Proof.Argon2.AArch64.AddressCalls.stageWrites s out) s.mem t.mem) : Frame (VG.Proof.Argon2.AArch64.AddressCalls.writes s) s.mem t.mem := by
  apply hf.sub
  intro r hr
  simp only [VG.Proof.Argon2.AArch64.AddressCalls.stageWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨VG.Proof.Argon2.AArch64.AddressCalls.work s, 8192⟩, by simp [VG.Proof.Argon2.AArch64.AddressCalls.writes], Offset.sub_base _ bound⟩
  · exact ⟨⟨VG.Proof.Argon2.AArch64.AddressCalls.work s, 8192⟩, by simp [VG.Proof.Argon2.AArch64.AddressCalls.writes], Region.sub_prefix (by decide)⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.AArch64.AddressCalls.writes], fun _ h => h⟩

theorem zero_preserved {s t : State} (h : VG.Proof.Argon2.AArch64.AddressCalls.Ready s)
    (hf : Frame (VG.Proof.Argon2.AArch64.AddressCalls.stageWrites s 4096) s.mem t.mem) :
    VG.Spec.Argon2.blockAt t.mem (off (VG.Proof.Argon2.AArch64.AddressCalls.work s) 7168) = VG.Spec.Argon2.blockAt s.mem (off (VG.Proof.Argon2.AArch64.AddressCalls.work s) 7168) := by
  apply FillCompress.block_frame hf
  intro r hr
  simp only [VG.Proof.Argon2.AArch64.AddressCalls.stageWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ (by decide) (by decide) (by decide)
  · exact Offset.disjoint_base _ (by decide) (by decide)
  · exact (h.stackWork.sub_right (Offset.sub_base _ (by decide))).symm

theorem calls_ok (p : VG.Spec.Argon2.Params) (pass lane slice counter : Nat) (s : State) (h : VG.Proof.Argon2.AArch64.AddressCalls.Ready s)
    (zero : VG.Spec.Argon2.blockAt s.mem (off (VG.Proof.Argon2.AArch64.AddressCalls.work s) 7168) = zeroBlock)
    (input : VG.Spec.Argon2.blockAt s.mem (off (VG.Proof.Argon2.AArch64.AddressCalls.work s) 5120) = Proof.Argon2.addressInput p pass lane slice counter) :
    WP isa calls s (VG.Proof.Argon2.AArch64.AddressCalls.Generated s · p pass lane slice counter) := by
  unfold calls
  refine WP.seq ((VG.Proof.Argon2.AArch64.AddressCalls.stage_ok s h 7168 5120 4096 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).mono ?_)
  intro a first
  refine (VG.Proof.Argon2.AArch64.AddressCalls.stage_ok a first.ready 7168 4096 6144 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).mono ?_
  intro t second
  refine ⟨?_, second.ready, second.work.trans first.work,
    fun r hr => (second.regs r hr).trans (first.regs r hr),
    second.rd.trans first.rd, second.wr.trans first.wr, second.sp.trans first.sp, ?_⟩
  · have result := second.result
    rw [first.work, VG.Proof.Argon2.AArch64.AddressCalls.zero_preserved h first.frame, zero, first.result, zero, input] at result
    rw [Proof.Argon2.addressBlock_eq]
    exact result
  · have next := VG.Proof.Argon2.AArch64.AddressCalls.stage_frame_full (by decide) second.frame
    simp only [VG.Proof.Argon2.AArch64.AddressCalls.writes, first.work, first.sp] at next
    exact (VG.Proof.Argon2.AArch64.AddressCalls.stage_frame_full (by decide) first.frame).trans next

end VG.Proof.Argon2.AArch64.AddressCalls

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.AddressCacheSelect`. -/
section

/-! Merged from `Proof.Argon2.AArch64.AddressGeneration`. -/
section
/-! Complete independent-address generation against the reviewed algorithm. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCalls

theorem calls_sp_ok (p : Params) (pass lane slice counter : Nat) (s : State) (h : VG.Proof.Argon2.AArch64.AddressCalls.Ready s)
    (zero : blockAt s.mem (off (VG.Proof.Argon2.AArch64.AddressCalls.work s) 7168) = zeroBlock)
    (input : blockAt s.mem (off (VG.Proof.Argon2.AArch64.AddressCalls.work s) 5120) = Proof.Argon2.addressInput p pass lane slice counter) :
    WP isa calls s fun t => VG.Proof.Argon2.AArch64.AddressCalls.Generated s t p pass lane slice counter ∧ t.sp = s.sp :=
  (VG.Proof.Argon2.AArch64.AddressCalls.calls_ok p pass lane slice counter s h zero input).mono (fun _ h => ⟨h, h.sp⟩)

theorem code_ok (p : Params) (pass lane slice counter : Nat) (s : State) (h : VG.Proof.Argon2.AArch64.AddressCalls.Ready s)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8)
    (words : AddressHeader.Words p pass lane slice counter s) :
    WP isa VG.Impl.Argon2.AArch64.AddressCalls.code s fun t => VG.Proof.Argon2.AArch64.AddressCalls.Generated s t p pass lane slice counter ∧ t.sp = s.sp := by
  unfold VG.Impl.Argon2.AArch64.AddressCalls.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.AddressCalls.prepare_ok p pass lane slice counter s h reads words).mono ?_)
  intro a prepared
  have zero : blockAt a.mem (off (VG.Proof.Argon2.AArch64.AddressCalls.work a) 7168) = zeroBlock := by
    rw [prepared.stable.work_eq]; exact prepared.zero
  have input : blockAt a.mem (off (VG.Proof.Argon2.AArch64.AddressCalls.work a) 5120) = Proof.Argon2.addressInput p pass lane slice counter := by
    rw [prepared.stable.work_eq]; exact prepared.input
  refine (VG.Proof.Argon2.AArch64.AddressCalls.calls_sp_ok p pass lane slice counter a prepared.stable.ready zero input).mono ?_
  rintro t ⟨generated, mx⟩
  have frame := generated.frame
  rw [VG.Proof.Argon2.AArch64.AddressCalls.writes, prepared.stable.work_eq, prepared.stable.sp] at frame
  have firstFrame : Frame (VG.Proof.Argon2.AArch64.AddressCalls.writes s) s.mem a.mem :=
    prepared.stable.frame.mono (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      simp [VG.Proof.Argon2.AArch64.AddressCalls.writes])
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
    WP isa (.block VG.Impl.Argon2.AArch64.AddressCache.save) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x19) 8) (s.gpr .x8) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [off] at hw
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.AArch64.AddressCache.save, VG.Impl.Argon2.AArch64.Instructions.store,
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
    (hw : InRegions s.wr (off (s.gpr .x19) 8) 8) : WP isa (.block VG.Impl.Argon2.AArch64.AddressCache.save) s (VG.Proof.Argon2.AArch64.AddressCache.Saved s) := by
  refine (VG.Proof.Argon2.AArch64.AddressCache.save_ok s hw).mono ?_
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

theorem Saved.read {s t : State} (h : VG.Proof.Argon2.AArch64.AddressCache.Saved s t) (d : Nat)
    (hd : d + 8 ≤ 8 ∨ 16 ≤ d) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [h.regs, h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ hd (by omega) (by decide)) (by decide)

theorem Saved.words {s t : State} {p : Params} {pass lane slice old counter : Nat}
    (h : VG.Proof.Argon2.AArch64.AddressCache.Saved s t) (words : AddressHeader.Words p pass lane slice old s)
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
  cached : VG.Proof.Argon2.AArch64.AddressCache.counter (s.gpr .x23) = s.mem.readW (off (s.gpr .x19) 8) 64 →
    blockAt s.mem (off (AddressCalls.work s) 6144) = addressBlock p pass lane slice (VG.Proof.Argon2.AArch64.AddressCache.wanted s)

theorem ready_zero (p : Params) (pass lane slice : Nat) (s : State)
    (layout : AddressCalls.Ready s)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8)
    (write : InRegions s.wr (off (s.gpr .x19) 8) 8)
    (words : AddressHeader.Words p pass lane slice 0 s) : VG.Proof.Argon2.AArch64.AddressCache.Ready p pass lane slice 0 s :=
  ⟨layout, reads, write, words, fun same => False.elim
    (VG.Proof.Argon2.AArch64.AddressCache.counter_ne_zero _ (same.trans words.counterWord))⟩

structure Selected (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  block : blockAt t.mem (off (AddressCalls.work s) 6144) = addressBlock p pass lane slice (VG.Proof.Argon2.AArch64.AddressCache.wanted s)
  layout : AddressCalls.Ready t
  work_eq : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.AArch64.AddressCache.writes s) s.mem t.mem
  sp : t.sp = s.sp
  counterWord : t.mem.readW (off (t.gpr .x19) 8) 64 = VG.Proof.Argon2.AArch64.AddressCache.counter (s.gpr .x23)

theorem check_stable {s a : State} (h : AddressCalls.Ready s) (k : Divide.Keeps [.x8, .x13, .x14, .x15] s a) :
    AddressCalls.Stable s a := by
  apply AddressCalls.stable_of_frame h _ k.rd k.wr _ k.sp
  · intro r hr
    apply k.regs
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [k.mem]; exact Frame.refl _ _

theorem selected_ok (p : Params) (pass lane slice old : Nat) (s : State)
    (h : VG.Proof.Argon2.AArch64.AddressCache.Ready p pass lane slice old s) :
    WP isa VG.Impl.Argon2.AArch64.AddressCache.select s (VG.Proof.Argon2.AArch64.AddressCache.Selected s · p pass lane slice) := by
  unfold VG.Impl.Argon2.AArch64.AddressCache.select
  refine WP.seq ((VG.Proof.Argon2.AArch64.AddressCache.check_ok s (h.reads 8 (by simp))).mono ?_)
  rintro a ⟨value, flag, keeps⟩
  have stableA := VG.Proof.Argon2.AArch64.AddressCache.check_stable h.layout keeps
  refine WP.ite (decide (VG.Proof.Argon2.AArch64.AddressCache.counter (s.gpr .x23) = s.mem.readW (off (s.gpr .x19) 8) 64))
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
    refine WP.seq ((VG.Proof.Argon2.AArch64.AddressCache.save_ready a stableA.ready write).mono ?_)
    intro b saved
    have words : AddressHeader.Words p pass lane slice (VG.Proof.Argon2.AArch64.AddressCache.wanted s) b := by
      apply saved.words (stableA.words h.layout h.words)
      rw [value, VG.Proof.Argon2.AArch64.AddressCache.counter_nat]; rfl
    have reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (b.rd ++ b.wr) (off (b.gpr .x19) d) 8 := by
      rw [saved.rd, saved.wr, saved.regs]; exact stableA.reads h.reads
    refine (AddressCalls.code_ok p pass lane slice (VG.Proof.Argon2.AArch64.AddressCache.wanted s) b saved.ready reads words).mono ?_
    rintro t ⟨generated, mx⟩
    have workB : AddressCalls.work b = AddressCalls.work s := saved.work_eq.trans stableA.work_eq
    have regsB (r : Reg) (hr : r ∈ FillCompress.loopRegs) : b.gpr r = s.gpr r :=
      (congrFun saved.regs r).trans (stableA.regs r hr)
    have regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r :=
      fun r hr => (generated.regs r hr).trans (regsB r hr)
    have firstFrame : Frame (VG.Proof.Argon2.AArch64.AddressCache.writes s) s.mem b.mem := by
      have frame := saved.frame
      rw [stableA.regs .x19 (by simp [FillCompress.loopRegs]), keeps.mem] at frame
      exact frame.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp [VG.Proof.Argon2.AArch64.AddressCache.writes])
    have finalFrame : Frame (VG.Proof.Argon2.AArch64.AddressCache.writes s) b.mem t.mem := by
      have frame := generated.frame
      rw [AddressCalls.writes, workB, saved.sp.trans keeps.sp] at frame
      exact frame.mono (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp [VG.Proof.Argon2.AArch64.AddressCache.writes])
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

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.AddressCacheWord`. -/
section

/-! Read exactly the public indexed word of the cached address block. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCache
open VG.Impl.Argon2.AArch64

def wordAddress (s : State) : Addr :=
  s.gpr .x8 * BitVec.ofNat 64 8 + s.gpr .x3 + BitVec.ofInt 64 6144

theorem wordRead_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.AArch64.AddressCache.wordAddress s) 8) :
    WP isa (.block wordRead) s fun t => t.gpr .x0 = s.mem.readW (VG.Proof.Argon2.AArch64.AddressCache.wordAddress s) 64 ∧
      Divide.Keeps [.x0, .x12, .x13, .x15] s t := by
  change InRegions (s.rd ++ s.wr) (s.gpr .x8 * 8#64 + s.gpr .x3 + 6144#64) 8 at hr
  apply WP.of_runBlock
  simp only [wordRead, VG.Proof.Argon2.AArch64.AddressCache.wordAddress, Instructions.mov, Instructions.add, Instructions.addi,
    Instructions.mark, Instructions.imm, Instructions.load,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, addr, State.load,
    Size.bytes, Size.bits, show 0 % 8 = 0 ∧ 0 < 4096 * 8 from by decide,
    show 0 < 4096 from by decide, show ¬6144 < 4096 from by decide,
    show 6144 < 65536 from by decide, Nat.reduceMul, Nat.reduceLT,
    BitVec.shiftLeft_zero, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, and_self, Option.map_some, Option.bind_some,
    ← BitVec.mul_two, BitVec.mul_assoc,
    show (2#64) * (2#64 * 2#64) = 8#64 from rfl,
    show (6144#16).setWidth 64 = 6144#64 from rfl,
    show BitVec.ofInt 64 6144 = 6144#64 from rfl,
    hr, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem wordAddress_args {s a : State}
    (scratch : a.gpr .x3 = AddressCalls.work s)
    (index : a.gpr .x8 = s.gpr .x23 &&& 127) :
    VG.Proof.Argon2.AArch64.AddressCache.wordAddress a = off (off (AddressCalls.work s) 6144) (8 * ((s.gpr .x23).toNat % 128)) := by
  unfold VG.Proof.Argon2.AArch64.AddressCache.wordAddress off
  rw [scratch, index, VG.Proof.Argon2.AArch64.AddressCache.index_nat, ← BitVec.ofNat_mul, Nat.mul_comm]
  change BitVec.ofNat 64 (8 * ((s.gpr .x23).toNat % 128)) + AddressCalls.work s +
    BitVec.ofNat 64 6144 = _
  rw [BitVec.add_comm (BitVec.ofNat 64 (8 * ((s.gpr .x23).toNat % 128))) (AddressCalls.work s),
    BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (8 * ((s.gpr .x23).toNat % 128)))
      (BitVec.ofNat 64 6144), ← BitVec.add_assoc]

theorem word_ok (s : State) (h : AddressCalls.Ready s) :
    WP isa Impl.Argon2.AArch64.AddressCache.word s fun t => t.gpr .x0 =
      (blockAt s.mem (off (AddressCalls.work s) 6144))[(s.gpr .x23).toNat % 128]'(Nat.mod_lt _ (by decide)) ∧
      Divide.Keeps [.x3, .x8, .x0, .x12, .x13, .x15] s t := by
  unfold Impl.Argon2.AArch64.AddressCache.word
  refine WP.seq ((VG.Proof.Argon2.AArch64.AddressCache.wordArgs_ok s h.frameRead).mono ?_)
  rintro a ⟨scratch, index, keeps⟩
  have address := VG.Proof.Argon2.AArch64.AddressCache.wordAddress_args scratch index
  have read : InRegions (a.rd ++ a.wr) (VG.Proof.Argon2.AArch64.AddressCache.wordAddress a) 8 := by
    rw [address, keeps.rd, keeps.wr]
    have cover := AddressCalls.work_cover s h 6144 1024 (by decide)
    have writable := cover _ _ ⟨⟨off (AddressCalls.work s) 6144, 1024⟩, by simp,
      Offset.contains_base _ (d := 8 * ((s.gpr .x23).toNat % 128)) (n := 8) (k := 1024)
        (by have := Nat.mod_lt (s.gpr .x23).toNat (by decide : 0 < 128); omega) (by omega)⟩
    obtain ⟨r, hr, hc⟩ := writable
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine (VG.Proof.Argon2.AArch64.AddressCache.wordRead_ok a read).mono ?_
  rintro t ⟨value, tail⟩
  refine ⟨?_, (keeps.mono (by decide)).trans (tail.mono (by decide))⟩
  rw [value, address, keeps.mem]
  change s.mem.readW _ 64 = (blockAt _ _)[(⟨_, Nat.mod_lt _ (by decide)⟩ : Fin 128)]
  rw [blockAt_get]

end VG.Proof.Argon2.AArch64.AddressCache

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitScale`. -/
section

/-! # Fixed scaling by public powers of two on ARM64 -/
namespace VG.Proof.Argon2.AArch64.MemoryInit
open VG VG.AArch64 VG.Impl.Argon2.AArch64

structure Scaled (s t : State) (r : Reg) (n : Nat) : Prop where
  value : t.gpr r = s.gpr r * BitVec.ofNat 64 (2 ^ n)
  other : ∀ q, q ≠ r → q ≠ .x15 → t.gpr q = s.gpr q
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem double_ok (s : State) (r : Reg) :
    WP isa (.block (Instructions.add r r)) s fun t =>
      t.gpr r = s.gpr r + s.gpr r ∧
      (∀ q, q ≠ r → q ≠ .x15 → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [Instructions.add, Instructions.mark, Instructions.mov,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun q hq hq' => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_write, ite_true, BitVec.setWidth_eq, BitVec.add_zero, ite_self]
  · simp only [RegUpd.gpr_write, hq, hq', ite_false]

theorem scale_ok (s : State) (r : Reg) (n : Nat) :
    WP isa (.block (List.replicate n (Instructions.add r r)).flatten) s
      fun t => VG.Proof.Argon2.AArch64.MemoryInit.Scaled s t r n := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨by rw [Nat.pow_zero]; exact (BitVec.mul_one _).symm,
      fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons]
    rw [WP.block_append_iff]
    refine (VG.Proof.Argon2.AArch64.MemoryInit.double_ok s r).mono ?_
    rintro a ⟨value, other, mem, rd, wr, sp⟩
    refine (ih a).mono ?_
    intro t ht
    refine ⟨?_, fun q hq hq' => (ht.other q hq hq').trans (other q hq hq'),
      ht.mem.trans mem, ht.rd.trans rd, ht.wr.trans wr, ht.sp.trans sp⟩
    rw [ht.value, value, ← BitVec.mul_two, Nat.pow_succ, BitVec.ofNat_mul,
      BitVec.mul_assoc]
    exact congrArg (fun v => s.gpr r * v) (BitVec.mul_comm _ _)
end VG.Proof.Argon2.AArch64.MemoryInit

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.BlockAddress`. -/
section

/-! Fault-free matrix pointer calculation, with no memory accesses. -/

namespace VG.Proof.Argon2.AArch64.BlockAddress

open VG VG.AArch64 VG.Impl.Argon2.AArch64.BlockAddress
open VG.Impl.Argon2.AArch64

theorem flatten_ok (s : State) : WP isa (.block flatten) s fun t =>
    t.gpr .x8 = s.gpr .x8 * s.gpr .x20 + s.gpr .x3 ∧
    Divide.Keeps [.x8, .x2, .x15] s t := by
  apply WP.of_runBlock
  simp only [flatten, Instructions.mul, Instructions.add, Instructions.mark, Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem scale_ok (s : State) : WP isa (.block scale) s fun t =>
    t.gpr .x8 = s.gpr .x8 * 1024 ∧ Divide.Keeps [.x8, .x15] s t := by
  refine (MemoryInit.scale_ok s .x8 10).mono ?_
  intro t h
  refine ⟨h.value, ?_, h.mem, h.rd, h.wr, h.sp⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact h.other r hr.1 hr.2

theorem base_ok (s : State) : WP isa (.block ([Instructions.add .x8 .x4].flatten)) s fun t =>
    t.gpr .x8 = s.gpr .x8 + s.gpr .x4 ∧ Divide.Keeps [.x8, .x15] s t := by
  apply WP.of_runBlock
  simp only [Instructions.add, Instructions.mark, Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.AArch64.BlockAddress.code s fun t =>
    t.gpr .x8 = (s.gpr .x8 * s.gpr .x20 + s.gpr .x3) * 1024 + s.gpr .x4 ∧
    Divide.Keeps [.x8, .x2, .x15] s t := by
  unfold VG.Impl.Argon2.AArch64.BlockAddress.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.BlockAddress.flatten_ok s).mono ?_)
  rintro a ⟨flat, ka⟩
  refine WP.seq ((VG.Proof.Argon2.AArch64.BlockAddress.scale_ok a).mono ?_)
  rintro b ⟨scaled, kb⟩
  refine (VG.Proof.Argon2.AArch64.BlockAddress.base_ok b).mono ?_
  rintro t ⟨result, kt⟩
  refine ⟨?_, ka.trans ((kb.mono (by decide)).trans (kt.mono (by decide)))⟩
  rw [result, scaled, flat, kb.regs .x4 (by decide), ka.regs .x4 (by decide)]

theorem code_nat_ok (s : State) (lane column q : Nat)
    (hl : s.gpr .x8 = BitVec.ofNat 64 lane)
    (hc : s.gpr .x3 = BitVec.ofNat 64 column)
    (hq : s.gpr .x20 = BitVec.ofNat 64 q) :
    WP isa VG.Impl.Argon2.AArch64.BlockAddress.code s fun t =>
      t.gpr .x8 = s.gpr .x4 + BitVec.ofNat 64 ((lane * q + column) * 1024) ∧
      Divide.Keeps [.x8, .x2, .x15] s t := by
  refine (VG.Proof.Argon2.AArch64.BlockAddress.code_ok s).mono ?_
  rintro t ⟨h, k⟩
  refine ⟨?_, k⟩
  rw [h, hl, hc, hq, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  change BitVec.ofNat 64 (lane * q + column) * BitVec.ofNat 64 1024 + s.gpr .x4 = _
  rw [← BitVec.ofNat_mul, BitVec.add_comm]

theorem code_secret_rel : RelCT isa (fun s t => s.sp = t.sp) VG.Impl.Argon2.AArch64.BlockAddress.code (fun _ _ => True) :=
  RelCT.taint (A := VG.AArch64.taint) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) (by taint_decide)

end VG.Proof.Argon2.AArch64.BlockAddress

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMapState`. -/
section

/-! Merged from `Proof.Argon2.AArch64.ReferenceMapArgs`. -/
section
/-! Register preparation for the reference-index stages. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap
open VG.Impl.Argon2.AArch64

theorem loadPass_ok (s : State) (read : InRegions (s.rd ++ s.wr) (s.gpr .x19) 8) :
    WP isa (.block loadPass) s fun t =>
      t.gpr .x5 = s.mem.readW (s.gpr .x19) 64 ∧ Divide.Keeps [.x5] s t := by
  apply WP.of_runBlock
  simp only [loadPass, Instructions.load, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, Size.bits, show 0 % 8 = 0 ∧ 0 < 4096 * 8 from by decide,
    BitVec.add_zero, State.load, read, and_self, ite_true, Option.map_some, Option.bind_some,
    RegUpd.gpr_write, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem laneArgs_ok (s : State) : WP isa (.block laneArgs) s fun t =>
    t.gpr .x0 = s.gpr .x4 ∧ t.gpr .x1 = s.gpr .x24 ∧
    Divide.Keeps [.x0, .x1] s t := by
  apply WP.of_runBlock
  simp only [laneArgs, Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

theorem relativeArgs_ok (s : State) : WP isa (.block relativeArgs) s fun t =>
    t.gpr .x5 = s.gpr .x0 ∧ t.gpr .x0 = s.gpr .x7 ∧ t.gpr .x1 = s.gpr .x4 ∧
    Divide.Keeps [.x5, .x0, .x1] s t := by
  apply WP.of_runBlock
  simp only [relativeArgs, Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem wrapArgs_ok (s : State) : WP isa (.block wrapArgs) s fun t =>
    t.gpr .x0 = s.gpr .x8 + s.gpr .x6 ∧ t.gpr .x1 = s.gpr .x20 ∧
    Divide.Keeps [.x0, .x1, .x15] s t := by
  apply WP.of_runBlock
  simp only [wrapArgs, Instructions.mov, Instructions.add, Instructions.mark,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.AArch64.ReferenceMap
end

/-! Parameters and register invariants for the complete reference mapping. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64

/-- Every stage preserves the enclosing loop's callee-saved registers. -/
def changed : List Reg := [.x8, .x2, .x3, .x4, .x5, .x6, .x7, .x0, .x1, .x9, .x12, .x13, .x14, .x15]

structure Bounds (p : Spec.Argon2.Params) (pass lane slice index : Nat) : Prop where
  lanesPositive : 0 < p.lanes
  lanesBound : p.lanes < 2 ^ 32
  memoryMinimum : 8 * p.lanes ≤ p.memory
  memoryBound : p.memory < 2 ^ 32
  passBound : pass < 2 ^ 32
  laneBound : lane < p.lanes
  sliceBound : slice < 4
  indexBound : index < p.segmentLen
  active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index

structure Position (p : Spec.Argon2.Params) (lane slice index : Nat) (s : State) : Prop where
  current : s.gpr .x24 = BitVec.ofNat 64 lane
  laneLength : s.gpr .x20 = BitVec.ofNat 64 p.laneLen
  segmentLength : s.gpr .x21 = BitVec.ofNat 64 p.segmentLen
  slice : s.gpr .x22 = BitVec.ofNat 64 slice
  index : s.gpr .x23 = BitVec.ofNat 64 index

theorem Position.of_keeps {s t : State} {p : Spec.Argon2.Params} {lane slice index : Nat}
    (h : VG.Proof.Argon2.AArch64.ReferenceMap.Position p lane slice index s) (k : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed s t) :
    VG.Proof.Argon2.AArch64.ReferenceMap.Position p lane slice index t :=
  ⟨(k.regs .x24 (by decide)).trans h.current,
    (k.regs .x20 (by decide)).trans h.laneLength,
    (k.regs .x21 (by decide)).trans h.segmentLength,
    (k.regs .x22 (by decide)).trans h.slice,
    (k.regs .x23 (by decide)).trans h.index⟩

structure Ready (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s : State) : Prop where
  bounds : VG.Proof.Argon2.AArch64.ReferenceMap.Bounds p pass lane slice index
  position : VG.Proof.Argon2.AArch64.ReferenceMap.Position p lane slice index s
  lanes : s.gpr .x1 = BitVec.ofNat 64 p.lanes
  passRead : InRegions (s.rd ++ s.wr) (s.gpr .x19) 8
  passWord : s.mem.readW (s.gpr .x19) 64 = BitVec.ofNat 64 pass

theorem Ready.lanes_nat {p : Spec.Argon2.Params} {pass lane slice index : Nat} {s : State}
    (h : VG.Proof.Argon2.AArch64.ReferenceMap.Ready p pass lane slice index s) : (s.gpr .x1).toNat = p.lanes := by
  rw [h.lanes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.bounds.lanesBound (by decide))]

theorem Ready.of_keeps {p : Spec.Argon2.Params} {pass lane slice index : Nat} {s t : State}
    (h : VG.Proof.Argon2.AArch64.ReferenceMap.Ready p pass lane slice index s) (k : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed s t)
    (lanes : t.gpr .x1 = s.gpr .x1) : VG.Proof.Argon2.AArch64.ReferenceMap.Ready p pass lane slice index t := by
  refine ⟨h.bounds, h.position.of_keeps k, lanes.trans h.lanes, ?_, ?_⟩
  · rw [k.rd, k.wr, k.regs .x19 (by decide)]
    exact h.passRead
  · rw [k.mem, k.regs .x19 (by decide)]
    exact h.passWord

def chosenLane (p : Spec.Argon2.Params) (pass lane slice : Nat) (random : Addr) : Nat :=
  if pass = 0 ∧ slice = 0 then lane else (random >>> 32).toNat % p.lanes

theorem chosenLane_bound (p : Spec.Argon2.Params) (pass lane slice : Nat) (random : Addr)
    (positive : 0 < p.lanes) (bound : lane < p.lanes) :
    VG.Proof.Argon2.AArch64.ReferenceMap.chosenLane p pass lane slice random < p.lanes := by
  unfold VG.Proof.Argon2.AArch64.ReferenceMap.chosenLane
  split
  · exact bound
  · exact Nat.mod_lt _ positive

theorem word_nat (n : Nat) (bound : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

theorem word_zero (n : Nat) (bound : n < 2 ^ 64) : BitVec.ofNat 64 n = (0 : Addr) ↔ n = 0 := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    rw [VG.Proof.Argon2.AArch64.ReferenceMap.word_nat n bound] at hn
    exact hn
  · intro h; rw [h]; rfl

theorem word_eq (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x = BitVec.ofNat 64 y ↔ x = y := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    rw [VG.Proof.Argon2.AArch64.ReferenceMap.word_nat x hx, VG.Proof.Argon2.AArch64.ReferenceMap.word_nat y hy] at hn
    exact hn
  · intro h; rw [h]

theorem Bounds.laneLength_bound {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.AArch64.ReferenceMap.Bounds p pass lane slice index) : p.laneLen < 2 ^ 32 := by
  have hb : p.laneLen ≤ p.blocks := by
    rw [Proof.Argon2.blocks_lanes p h.lanesPositive]
    exact Nat.le_mul_of_pos_left _ h.lanesPositive
  exact Nat.lt_of_le_of_lt (Nat.le_trans hb (Proof.Argon2.blocks_le_memory p)) h.memoryBound

theorem Bounds.window_positive {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.AArch64.ReferenceMap.Bounds p pass lane slice index) :
    0 < ReferenceCount.windowBase p pass slice + index ∧
      (index = 0 → 0 < ReferenceCount.windowBase p pass slice) := by
  have hp := Proof.Argon2.reference_count_positive p h.lanesPositive h.memoryMinimum
    pass slice index true h.active (by intro _ _; rfl)
  rw [ReferenceCount.spec_count] at hp
  change 0 < ReferenceCount.windowBase p pass slice + index - 1 at hp
  constructor
  · omega
  · intro zero; rw [zero, Nat.add_zero] at hp; omega

def windowSize (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) : Nat :=
  Spec.Argon2.referenceCount p pass slice index (VG.Proof.Argon2.AArch64.ReferenceMap.chosenLane p pass lane slice random == lane)

def windowStart (p : Spec.Argon2.Params) (pass slice : Nat) : Nat :=
  if pass = 0 then 0 else (slice + 1) * p.segmentLen % p.laneLen

def relativeValue (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) : Nat :=
  let count := VG.Proof.Argon2.AArch64.ReferenceMap.windowSize p pass lane slice index random
  let j := (random &&& 0xffffffff).toNat
  count - 1 - count * (j * j / 2 ^ 32) / 2 ^ 32

theorem Bounds.segment_le_lane {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.AArch64.ReferenceMap.Bounds p pass lane slice index) : p.segmentLen ≤ p.laneLen := by
  have segments := Proof.Argon2.laneLen_segments p h.lanesPositive
  omega

theorem Bounds.index_bound64 {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.AArch64.ReferenceMap.Bounds p pass lane slice index) : index < 2 ^ 64 :=
  Nat.lt_trans (Nat.lt_of_lt_of_le h.indexBound h.segment_le_lane)
    (Nat.lt_trans h.laneLength_bound (by decide))

theorem Bounds.chosenLane_bound64 {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.AArch64.ReferenceMap.Bounds p pass lane slice index) (random : Addr) :
    VG.Proof.Argon2.AArch64.ReferenceMap.chosenLane p pass lane slice random < 2 ^ 64 :=
  Nat.lt_trans (VG.Proof.Argon2.AArch64.ReferenceMap.chosenLane_bound p pass lane slice random h.lanesPositive h.laneBound)
    (Nat.lt_trans h.lanesBound (by decide))

theorem Bounds.lane_bound64 {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.AArch64.ReferenceMap.Bounds p pass lane slice index) : lane < 2 ^ 64 :=
  Nat.lt_trans h.laneBound (Nat.lt_trans h.lanesBound (by decide))

theorem Bounds.windowSize_positive {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.AArch64.ReferenceMap.Bounds p pass lane slice index) (random : Addr) :
    0 < VG.Proof.Argon2.AArch64.ReferenceMap.windowSize p pass lane slice index random := by
  apply Proof.Argon2.reference_count_positive p h.lanesPositive h.memoryMinimum
    pass slice index _ h.active
  intro firstPass firstSlice
  simp only [VG.Proof.Argon2.AArch64.ReferenceMap.chosenLane, firstPass, firstSlice, and_self, ite_true]
  exact beq_iff_eq.mpr rfl

theorem Bounds.windowSize_bound32 {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.AArch64.ReferenceMap.Bounds p pass lane slice index) (random : Addr) :
    VG.Proof.Argon2.AArch64.ReferenceMap.windowSize p pass lane slice index random < 2 ^ 32 :=
  Proof.Argon2.reference_count_32 p h.lanesPositive h.memoryMinimum h.memoryBound
    pass slice index _ h.sliceBound h.indexBound

theorem Bounds.windowSize_lt_lane {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.AArch64.ReferenceMap.Bounds p pass lane slice index) (random : Addr) :
    VG.Proof.Argon2.AArch64.ReferenceMap.windowSize p pass lane slice index random < p.laneLen :=
  Proof.Argon2.reference_count_lt_lane p h.lanesPositive h.memoryMinimum
    pass slice index _ h.sliceBound h.indexBound

theorem Bounds.laneLength_positive {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.AArch64.ReferenceMap.Bounds p pass lane slice index) : 0 < p.laneLen := by
  have seg := Proof.Argon2.segmentLen_ge_two p h.lanesPositive h.memoryMinimum
  have len := Proof.Argon2.laneLen_segments p h.lanesPositive
  omega

theorem Bounds.windowStart_lt_lane {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.AArch64.ReferenceMap.Bounds p pass lane slice index) : VG.Proof.Argon2.AArch64.ReferenceMap.windowStart p pass slice < p.laneLen := by
  unfold VG.Proof.Argon2.AArch64.ReferenceMap.windowStart
  split
  · exact h.laneLength_positive
  · exact Nat.mod_lt _ h.laneLength_positive

theorem Bounds.sum_bound {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.AArch64.ReferenceMap.Bounds p pass lane slice index) (random : Addr) :
    VG.Proof.Argon2.AArch64.ReferenceMap.windowStart p pass slice + VG.Proof.Argon2.AArch64.ReferenceMap.relativeValue p pass lane slice index random < 2 * p.laneLen := by
  have start := h.windowStart_lt_lane
  have relative := Proof.Argon2.reference_relative_bound _ (random &&& 0xffffffff).toNat
    (h.windowSize_positive random)
  have count := h.windowSize_lt_lane random
  change VG.Proof.Argon2.AArch64.ReferenceMap.relativeValue p pass lane slice index random < VG.Proof.Argon2.AArch64.ReferenceMap.windowSize p pass lane slice index random at relative
  omega

end VG.Proof.Argon2.AArch64.ReferenceMap

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.DivideCT`. -/
section

/-! Merged from `Proof.Argon2.AArch64.DivideLit`. -/
section
/-! Checked literal for unrolled ARM64 reference-index division. -/
namespace VG
materialize_code Impl.Argon2.AArch64.Divide.code
end VG
end

/-! # Timing of reference-index division on ARM64 -/
namespace VG.Proof.Argon2.AArch64.Divide
open VG VG.AArch64 VG.Impl.Argon2.AArch64.Divide

theorem code_rel :
    RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1)
      VG.Impl.Argon2.AArch64.Divide.code (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x4, .x5], s.gpr r = t.gpr r) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.x0, .x1])
    (fun _ _ h => ⟨h.1, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.2.1
      · exact h.2.2⟩) [.x4, .x5] (by taint_decide)

theorem code_secret_rel : RelCT isa (fun s t => s.sp = t.sp) VG.Impl.Argon2.AArch64.Divide.code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)
end VG.Proof.Argon2.AArch64.Divide

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMapLane`. -/
section

/-! Merged from `Proof.Argon2.AArch64.ReferenceLane`. -/
section
/-! # Secret J₂ does not affect the lane-selection trace -/

namespace VG.Proof.Argon2.AArch64.ReferenceLane

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceLane
open VG.Impl.Argon2.AArch64

structure Prefix (s t : State) : Prop where
  high : t.gpr .x0 = s.gpr .x0 >>> 32
  original : t.gpr .x7 = s.gpr .x0
  keeps : Divide.Keeps [.x0, .x7, .x15] s t

theorem highArgs_ok (s : State) : WP isa (.block highArgs) s (VG.Proof.Argon2.AArch64.ReferenceLane.Prefix s) := by
  apply WP.of_runBlock
  simp only [highArgs, Instructions.mov, Instructions.shr, Instructions.mark,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 32 < 64 from by decide, show 0 < 4096 from by decide,
    BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

def changed : List Reg := [.x0, .x7, .x15] ++ Divide.changed

theorem code_ok (s : State) (lo : 0 < (s.gpr .x1).toNat)
    (bound : (s.gpr .x1).toNat < 2 ^ 32) :
    WP isa VG.Impl.Argon2.AArch64.ReferenceLane.code s fun t =>
      (t.gpr .x4).toNat = (s.gpr .x0 >>> 32).toNat % (s.gpr .x1).toNat ∧
      t.gpr .x7 = s.gpr .x0 ∧ Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceLane.changed s t := by
  unfold VG.Impl.Argon2.AArch64.ReferenceLane.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.ReferenceLane.highArgs_ok s).mono ?_)
  intro a ha
  have si := ha.keeps.regs .x1 (by decide)
  refine (Divide.code_ok a ?_ (by rw [si]; exact lo) (by rw [si]; exact bound)).mono ?_
  · rw [ha.high]
    simpa only [show 64 - 32 = (32 : Nat) from rfl] using
      BitVec.toNat_ushiftRight_lt (s.gpr .x0) 32 (by decide)
  · intro t ht
    refine ⟨?_, ?_, (ha.keeps.mono ?_).trans (ht.2.2.mono ?_)⟩
    · rw [ht.2.1, ha.high, si]
    · exact (ht.2.2.regs .x7 (by decide)).trans ha.original
    · intro r hr; exact List.mem_append_left _ hr
    · intro r hr; exact List.mem_append_right _ hr

theorem highArgs_secret_rel : RelCT isa (fun s t => s.sp = t.sp) (.block highArgs)
    (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem code_secret_rel : RelCT isa (fun s t => s.sp = t.sp) VG.Impl.Argon2.AArch64.ReferenceLane.code (fun s t => s.sp = t.sp) :=
  highArgs_secret_rel.seq Divide.code_secret_rel

end VG.Proof.Argon2.AArch64.ReferenceLane
end

/-! Merged from `Proof.Argon2.AArch64.FirstLane`. -/
section
/-! The first reference window stays in the current lane. -/

namespace VG.Proof.Argon2.AArch64.FirstLane

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FirstLane
open VG.Impl.Argon2.AArch64

theorem test_ok (s : State) : WP isa (.block VG.Impl.Argon2.AArch64.FirstLane.test) s fun t =>
    t.gpr .x15 = s.gpr .x5 ||| s.gpr .x22 ∧ Divide.Keeps [.x8, .x15] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.AArch64.FirstLane.test, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.logic, Instructions.mark,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    BitVec.setWidth_eq, show 0 < 4096 from by decide, BitVec.add_zero,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

theorem current_ok (s : State) : WP isa (.block VG.Impl.Argon2.AArch64.FirstLane.current) s fun t =>
    t.gpr .x4 = s.gpr .x24 ∧ Divide.Keeps [.x4] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.AArch64.FirstLane.current, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, ite_true, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.AArch64.FirstLane.code s fun t =>
    t.gpr .x4 = (if s.gpr .x5 = 0 ∧ s.gpr .x22 = 0 then s.gpr .x24 else s.gpr .x4) ∧
    Divide.Keeps [.x8, .x4, .x15] s t := by
  unfold VG.Impl.Argon2.AArch64.FirstLane.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.FirstLane.test_ok s).mono ?_)
  rintro a ⟨flag, keeps⟩
  refine WP.ite (decide (s.gpr .x5 = 0 ∧ s.gpr .x22 = 0))
    (by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag]
      apply congrArg some
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      exact BitVec.or_eq_zero_iff) ?_ ?_
  · intro h
    have position := of_decide_eq_true h
    refine (VG.Proof.Argon2.AArch64.FirstLane.current_ok a).mono ?_
    rintro t ⟨out, tail⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (tail.mono (by decide))⟩
    simpa only [position, and_self, ite_true, keeps.regs .x24 (by decide)] using out
  · intro h
    have position := of_decide_eq_false h
    apply WP.of_runBlock
    simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
    refine ⟨?_, keeps.mono (by decide)⟩
    simp only [position, ite_false]
    exact keeps.regs .x4 (by decide)

end VG.Proof.Argon2.AArch64.FirstLane
end

/-! Choose the reference lane, restore the pass and prepare the window inputs. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

structure Chosen (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .x4 = BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.ReferenceMap.chosenLane p pass lane slice (s.gpr .x0))
  pass : t.gpr .x5 = BitVec.ofNat 64 pass
  original : t.gpr .x7 = s.gpr .x0
  position : VG.Proof.Argon2.AArch64.ReferenceMap.Position p lane slice index t
  keeps : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed s t

theorem chooseLane_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : VG.Proof.Argon2.AArch64.ReferenceMap.Ready p pass lane slice index s) :
    WP isa chooseLane s (VG.Proof.Argon2.AArch64.ReferenceMap.Chosen p pass lane slice index s) := by
  have lanesNat : (s.gpr .x1).toNat = p.lanes := by
    rw [ready.lanes, VG.Proof.Argon2.AArch64.ReferenceMap.word_nat _ (by have := ready.bounds.lanesBound; omega)]
  unfold chooseLane
  refine WP.seq ((ReferenceLane.code_ok s
    (by rw [lanesNat]; exact ready.bounds.lanesPositive)
    (by rw [lanesNat]; exact ready.bounds.lanesBound)).mono ?_)
  rintro a ⟨laneNat, original, ka⟩
  have ka' : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed s a := ka.mono (by decide)
  have readA : InRegions (a.rd ++ a.wr) (a.gpr .x19) 8 := by
    rw [ka'.rd, ka'.wr, ka'.regs .x19 (by decide)]
    exact ready.passRead
  have laneWord : a.gpr .x4 = BitVec.ofNat 64 ((s.gpr .x0 >>> 32).toNat % p.lanes) := by
    calc
      a.gpr .x4 = BitVec.ofNat 64 (a.gpr .x4).toNat := by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      _ = _ := by rw [laneNat, lanesNat]
  refine WP.seq ((VG.Proof.Argon2.AArch64.ReferenceMap.loadPass_ok a readA).mono ?_)
  rintro b ⟨loaded, kb⟩
  have kb' : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed a b := kb.mono (by decide)
  have kab := ka'.trans kb'
  have pb := ready.position.of_keeps kab
  have passWord : b.gpr .x5 = BitVec.ofNat 64 pass := by
    rw [loaded, ka'.mem, ka'.regs .x19 (by decide)]
    exact ready.passWord
  have passZero : b.gpr .x5 = 0 ↔ pass = 0 := by
    rw [passWord]
    exact VG.Proof.Argon2.AArch64.ReferenceMap.word_zero _ (by have := ready.bounds.passBound; omega)
  have sliceZero : b.gpr .x22 = 0 ↔ slice = 0 := by
    rw [pb.slice]
    exact VG.Proof.Argon2.AArch64.ReferenceMap.word_zero _ (by have := ready.bounds.sliceBound; omega)
  refine (FirstLane.code_ok b).mono ?_
  rintro t ⟨out, kt⟩
  have kt' : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ready.position.of_keeps (kab.trans kt'), kab.trans kt'⟩
  · rw [out]
    by_cases position : pass = 0 ∧ slice = 0 <;>
      simp only [passZero, sliceZero, pb.current, kb.regs .x4 (by decide), laneWord,
        VG.Proof.Argon2.AArch64.ReferenceMap.chosenLane, position, and_self, ite_true, ite_false]
  · exact (kt.regs .x5 (by decide)).trans passWord
  · exact (kt.regs .x7 (by decide)).trans ((kb.regs .x7 (by decide)).trans original)

structure Prepared (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .x0 = BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.ReferenceMap.chosenLane p pass lane slice (s.gpr .x0))
  current : t.gpr .x1 = BitVec.ofNat 64 lane
  pass : (t.gpr .x5).toNat = pass
  original : t.gpr .x7 = s.gpr .x0
  position : VG.Proof.Argon2.AArch64.ReferenceMap.Position p lane slice index t
  keeps : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed s t

theorem prepareLanes_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : VG.Proof.Argon2.AArch64.ReferenceMap.Ready p pass lane slice index s) :
    WP isa prepareLanes s (VG.Proof.Argon2.AArch64.ReferenceMap.Prepared p pass lane slice index s) := by
  unfold prepareLanes
  refine WP.seq ((VG.Proof.Argon2.AArch64.ReferenceMap.chooseLane_ok s p pass lane slice index ready).mono ?_)
  intro a ha
  refine (VG.Proof.Argon2.AArch64.ReferenceMap.laneArgs_ok a).mono ?_
  rintro t ⟨laneOut, currentOut, kt⟩
  have kt' : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed a t := kt.mono (by decide)
  refine ⟨laneOut.trans ha.selected, currentOut.trans ha.position.current, ?_,
    (kt.regs .x7 (by decide)).trans ha.original,
    ha.position.of_keeps kt', ha.keeps.trans kt'⟩
  rw [kt.regs .x5 (by decide), ha.pass, VG.Proof.Argon2.AArch64.ReferenceMap.word_nat _ (by have := ready.bounds.passBound; omega)]

end VG.Proof.Argon2.AArch64.ReferenceMap

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMap`. -/
section

/-! Merged from `Proof.Argon2.AArch64.ReferenceMapWindow`. -/
section
/-! The selected eligible window and its chronological starting column. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

structure Counted (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .x0 = BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.ReferenceMap.chosenLane p pass lane slice (s.gpr .x0))
  current : t.gpr .x1 = BitVec.ofNat 64 lane
  count : t.gpr .x4 = BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.ReferenceMap.windowSize p pass lane slice index (s.gpr .x0))
  start : t.gpr .x6 = BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.ReferenceMap.windowStart p pass slice)
  original : t.gpr .x7 = s.gpr .x0
  position : VG.Proof.Argon2.AArch64.ReferenceMap.Position p lane slice index t
  keeps : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed s t

theorem window_ok (s a : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (bounds : VG.Proof.Argon2.AArch64.ReferenceMap.Bounds p pass lane slice index) (prepared : VG.Proof.Argon2.AArch64.ReferenceMap.Prepared p pass lane slice index s a) :
    WP isa window a (VG.Proof.Argon2.AArch64.ReferenceMap.Counted p pass lane slice index s) := by
  have segmentPositive : 0 < p.segmentLen :=
    Nat.lt_of_lt_of_le (by decide : 0 < 2)
      (Proof.Argon2.segmentLen_ge_two p bounds.lanesPositive bounds.memoryMinimum)
  unfold window
  refine WP.seq ((ReferenceStart.code_nat_ok a p pass slice bounds.lanesPositive
    segmentPositive bounds.sliceBound prepared.pass prepared.position.slice
    prepared.position.segmentLength).mono ?_)
  rintro b ⟨startWord, kb⟩
  have kb' : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed a b := kb.mono (by decide)
  have pb := prepared.position.of_keeps kb'
  have passB : (b.gpr .x5).toNat = pass := by
    rw [kb.regs .x5 (by decide), prepared.pass]
  have same : decide (b.gpr .x0 = b.gpr .x1) =
      (VG.Proof.Argon2.AArch64.ReferenceMap.chosenLane p pass lane slice (s.gpr .x0) == lane) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, beq_iff_eq]
    rw [kb.regs .x0 (by decide), kb.regs .x1 (by decide), prepared.selected, prepared.current]
    exact VG.Proof.Argon2.AArch64.ReferenceMap.word_eq _ _ (bounds.chosenLane_bound64 _) bounds.lane_bound64
  refine (ReferenceCount.code_nat_ok b p pass slice index passB pb.laneLength
    pb.segmentLength pb.slice pb.index bounds.segment_le_lane bounds.index_bound64
    bounds.window_positive.1 bounds.window_positive.2).mono ?_
  rintro t ⟨countWord, kt⟩
  have kt' : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, pb.of_keeps kt', prepared.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .x0 (by decide)).trans ((kb.regs .x0 (by decide)).trans prepared.selected)
  · exact (kt.regs .x1 (by decide)).trans ((kb.regs .x1 (by decide)).trans prepared.current)
  · simpa only [VG.Proof.Argon2.AArch64.ReferenceMap.windowSize, same] using countWord
  · exact (kt.regs .x6 (by decide)).trans startWord
  · exact (kt.regs .x7 (by decide)).trans ((kb.regs .x7 (by decide)).trans prepared.original)

end VG.Proof.Argon2.AArch64.ReferenceMap
end

/-! Merged from `Proof.Argon2.AArch64.ReferenceMapRelative`. -/
section
/-! Apply the squared J₁ mapping while retaining the lane and window start. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

theorem relativeWord_ok (s : State) (positive : 0 < (s.gpr .x1).toNat)
    (bound : (s.gpr .x1).toNat < 2 ^ 32) :
    WP isa VG.Impl.Argon2.AArch64.Relative.code s fun t =>
      t.gpr .x8 = BitVec.ofNat 64
        ((s.gpr .x1).toNat - 1 - (s.gpr .x1).toNat *
          ((s.gpr .x0 &&& 0xffffffff).toNat * (s.gpr .x0 &&& 0xffffffff).toNat / 2 ^ 32) /
          2 ^ 32) ∧ Divide.Keeps [.x8, .x2, .x3, .x12, .x15] s t := by
  obtain ⟨tr, t, he, out, other, mem, rd, wr⟩ := Relative.code_nat_ok s positive bound
  refine ⟨tr, t, he, out, ?_⟩
  refine ⟨?_, mem, rd, wr, VG.AArch64.Exec.sp he⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact other r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2

structure Mapped (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .x5 = BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.ReferenceMap.chosenLane p pass lane slice (s.gpr .x0))
  relative : t.gpr .x8 = BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.ReferenceMap.relativeValue p pass lane slice index (s.gpr .x0))
  start : t.gpr .x6 = BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.ReferenceMap.windowStart p pass slice)
  original : t.gpr .x7 = s.gpr .x0
  position : VG.Proof.Argon2.AArch64.ReferenceMap.Position p lane slice index t
  keeps : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed s t

theorem relative_ok (s a : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (bounds : VG.Proof.Argon2.AArch64.ReferenceMap.Bounds p pass lane slice index) (counted : VG.Proof.Argon2.AArch64.ReferenceMap.Counted p pass lane slice index s a) :
    WP isa relative a (VG.Proof.Argon2.AArch64.ReferenceMap.Mapped p pass lane slice index s) := by
  unfold relative
  refine WP.seq ((VG.Proof.Argon2.AArch64.ReferenceMap.relativeArgs_ok a).mono ?_)
  rintro b ⟨selected, random, count, kb⟩
  have countNat : (b.gpr .x1).toNat = VG.Proof.Argon2.AArch64.ReferenceMap.windowSize p pass lane slice index (s.gpr .x0) := by
    rw [count, counted.count, VG.Proof.Argon2.AArch64.ReferenceMap.word_nat _ (Nat.lt_trans (bounds.windowSize_bound32 _) (by decide))]
  have randomWord : b.gpr .x0 = s.gpr .x0 := random.trans counted.original
  refine (VG.Proof.Argon2.AArch64.ReferenceMap.relativeWord_ok b
    (by rw [countNat]; exact bounds.windowSize_positive _)
    (by rw [countNat]; exact bounds.windowSize_bound32 _)).mono ?_
  rintro t ⟨out, kt⟩
  have kb' : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed a b := kb.mono (by decide)
  have kt' : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ?_, counted.position.of_keeps (kb'.trans kt'),
    counted.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .x5 (by decide)).trans (selected.trans counted.selected)
  · simpa only [VG.Proof.Argon2.AArch64.ReferenceMap.relativeValue, countNat, randomWord] using out
  · exact (kt.regs .x6 (by decide)).trans ((kb.regs .x6 (by decide)).trans counted.start)
  · exact (kt.regs .x7 (by decide)).trans ((kb.regs .x7 (by decide)).trans counted.original)

end VG.Proof.Argon2.AArch64.ReferenceMap
end

/-! Merged from `Proof.Argon2.AArch64.ReferenceMapFinish`. -/
section
/-! Wrap the selected relative position into the lane's columns. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

structure Result (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .x5 = BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.ReferenceMap.chosenLane p pass lane slice (s.gpr .x0))
  column : t.gpr .x0 = BitVec.ofNat 64
    ((VG.Proof.Argon2.AArch64.ReferenceMap.windowStart p pass slice + VG.Proof.Argon2.AArch64.ReferenceMap.relativeValue p pass lane slice index (s.gpr .x0)) % p.laneLen)
  original : t.gpr .x7 = s.gpr .x0
  position : VG.Proof.Argon2.AArch64.ReferenceMap.Position p lane slice index t
  keeps : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed s t

theorem finish_ok (s a : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (bounds : VG.Proof.Argon2.AArch64.ReferenceMap.Bounds p pass lane slice index) (mapped : VG.Proof.Argon2.AArch64.ReferenceMap.Mapped p pass lane slice index s a) :
    WP isa VG.Impl.Argon2.AArch64.ReferenceMap.finish a (VG.Proof.Argon2.AArch64.ReferenceMap.Result p pass lane slice index s) := by
  unfold VG.Impl.Argon2.AArch64.ReferenceMap.finish
  refine WP.seq ((VG.Proof.Argon2.AArch64.ReferenceMap.wrapArgs_ok a).mono ?_)
  rintro b ⟨sum, length, kb⟩
  have sumWord : b.gpr .x0 = BitVec.ofNat 64
      (VG.Proof.Argon2.AArch64.ReferenceMap.windowStart p pass slice + VG.Proof.Argon2.AArch64.ReferenceMap.relativeValue p pass lane slice index (s.gpr .x0)) := by
    rw [sum, mapped.relative, mapped.start, ← BitVec.ofNat_add, Nat.add_comm]
  have sumBound : VG.Proof.Argon2.AArch64.ReferenceMap.windowStart p pass slice + VG.Proof.Argon2.AArch64.ReferenceMap.relativeValue p pass lane slice index (s.gpr .x0)
      < 2 ^ 64 := by
    have small := bounds.sum_bound (s.gpr .x0)
    have q := bounds.laneLength_bound
    omega
  have sumNat : (b.gpr .x0).toNat =
      VG.Proof.Argon2.AArch64.ReferenceMap.windowStart p pass slice + VG.Proof.Argon2.AArch64.ReferenceMap.relativeValue p pass lane slice index (s.gpr .x0) := by
    rw [sumWord, VG.Proof.Argon2.AArch64.ReferenceMap.word_nat _ sumBound]
  have lengthNat : (b.gpr .x1).toNat = p.laneLen := by
    rw [length, mapped.position.laneLength,
      VG.Proof.Argon2.AArch64.ReferenceMap.word_nat _ (Nat.lt_trans bounds.laneLength_bound (by decide))]
  refine (Wrap.code_nat_ok b (by rw [sumNat, lengthNat]; exact bounds.sum_bound _)).mono ?_
  rintro t ⟨out, kt⟩
  have kb' : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed a b := kb.mono (by decide)
  have kt' : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, mapped.position.of_keeps (kb'.trans kt'),
    mapped.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .x5 (by decide)).trans ((kb.regs .x5 (by decide)).trans mapped.selected)
  · rw [out, sumNat, lengthNat]
  · exact (kt.regs .x7 (by decide)).trans ((kb.regs .x7 (by decide)).trans mapped.original)

end VG.Proof.Argon2.AArch64.ReferenceMap
end

/-! Complete reference mapping against the reviewed RFC specification. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

theorem code_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : VG.Proof.Argon2.AArch64.ReferenceMap.Ready p pass lane slice index s) :
    WP isa VG.Impl.Argon2.AArch64.ReferenceMap.code s (VG.Proof.Argon2.AArch64.ReferenceMap.Result p pass lane slice index s) := by
  unfold VG.Impl.Argon2.AArch64.ReferenceMap.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.ReferenceMap.prepareLanes_ok s p pass lane slice index ready).mono ?_)
  intro a ha
  refine WP.seq ((VG.Proof.Argon2.AArch64.ReferenceMap.window_ok s a p pass lane slice index ready.bounds ha).mono ?_)
  intro b hb
  refine WP.seq ((VG.Proof.Argon2.AArch64.ReferenceMap.relative_ok s b p pass lane slice index ready.bounds hb).mono ?_)
  intro c hc
  exact VG.Proof.Argon2.AArch64.ReferenceMap.finish_ok s c p pass lane slice index ready.bounds hc

theorem spec_lane (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) :
    (Spec.Argon2.reference p pass lane slice index random).1 = VG.Proof.Argon2.AArch64.ReferenceMap.chosenLane p pass lane slice random := rfl

theorem spec_column (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) :
    (Spec.Argon2.reference p pass lane slice index random).2 =
      (VG.Proof.Argon2.AArch64.ReferenceMap.windowStart p pass slice + VG.Proof.Argon2.AArch64.ReferenceMap.relativeValue p pass lane slice index random) % p.laneLen := rfl

theorem code_spec_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : VG.Proof.Argon2.AArch64.ReferenceMap.Ready p pass lane slice index s) :
    WP isa VG.Impl.Argon2.AArch64.ReferenceMap.code s fun t =>
      t.gpr .x5 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .x0)).1 ∧
      t.gpr .x0 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .x0)).2 ∧
      t.gpr .x7 = s.gpr .x0 ∧ Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed s t := by
  refine (VG.Proof.Argon2.AArch64.ReferenceMap.code_ok s p pass lane slice index ready).mono ?_
  intro t h
  rw [VG.Proof.Argon2.AArch64.ReferenceMap.spec_lane, VG.Proof.Argon2.AArch64.ReferenceMap.spec_column]
  exact ⟨h.selected, h.column, h.original, h.keeps⟩

end VG.Proof.Argon2.AArch64.ReferenceMap

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillCompressLit`. -/
section

/-! Checked literals for compression and the enclosing argument setup. -/

namespace VG

materialize_code Impl.Argon2.AArch64.FillCompress.operation
materialize_code Impl.Argon2.AArch64.FillCompress.code

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillCompress`. -/
section

/-! The complete compression/update sequence from allocation and frame invariants. -/

namespace VG.Proof.Argon2.AArch64.FillCompress

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillCompress

def writes (s : State) : List Region :=
  [⟨s.gpr .x6, 1024⟩, ⟨VG.Proof.Argon2.AArch64.FillCompress.work s + 4096, 1024⟩, ⟨VG.Proof.Argon2.AArch64.FillCompress.work s, 4096⟩,
    below s.sp 8, ⟨off (s.gpr .x19) 16, 8⟩]

structure Done (s t : State) : Prop where
  block : VG.Spec.Argon2.blockAt t.mem (s.gpr .x6) =
    let next := Spec.Argon2.compress (VG.Spec.Argon2.blockAt s.mem (s.gpr .x0)) (VG.Spec.Argon2.blockAt s.mem (s.gpr .x1))
    if VG.Proof.Argon2.AArch64.FillCompress.pass s = 0 then next else xorBlock next (VG.Spec.Argon2.blockAt s.mem (s.gpr .x6))
  regs : ∀ r ∈ VG.Proof.Argon2.AArch64.FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (VG.Proof.Argon2.AArch64.FillCompress.writes s) s.mem t.mem

theorem code_ok (s : State) (h : VG.Proof.Argon2.AArch64.FillCompress.Ready s) : WP isa VG.Impl.Argon2.AArch64.FillCompress.code s (VG.Proof.Argon2.AArch64.FillCompress.Done s) := by
  unfold VG.Impl.Argon2.AArch64.FillCompress.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillCompress.setup_ok s h).mono ?_)
  intro a prepared
  refine (VG.Proof.Argon2.AArch64.FillCompress.operation_ok a prepared.ready).mono ?_
  intro t done
  refine ⟨?_, fun r hr => (done.regs r hr).trans (prepared.regs r hr),
    done.rd.trans prepared.rd, done.wr.trans prepared.wr, done.sp.trans prepared.sp, ?_⟩
  · have block := done.block
    rw [prepared.oldBlock, prepared.dest, prepared.counter, prepared.leftBlock,
      prepared.rightBlock] at block
    exact block
  · have frame : Frame (VG.Proof.Argon2.AArch64.FillCompress.writes s) a.mem t.mem := by
      have original := done.frame
      rw [prepared.dest] at original
      simp only [VG.Proof.Argon2.AArch64.FillCompress.callWrites, prepared.output, prepared.scratch,
        prepared.sp] at original
      exact original.mono (by intro r hr; exact List.mem_append_left _ hr)
    have savedFrame : Frame (VG.Proof.Argon2.AArch64.FillCompress.writes s) s.mem a.mem := prepared.frame.mono (by
      intro r hr
      simp only [VG.Proof.Argon2.AArch64.FillCompress.prefixWrites, List.mem_singleton] at hr
      subst r
      simp [VG.Proof.Argon2.AArch64.FillCompress.writes])
    exact savedFrame.trans frame

theorem code_sp_ok (s : State) (h : VG.Proof.Argon2.AArch64.FillCompress.Ready s) :
    WP isa VG.Impl.Argon2.AArch64.FillCompress.code s fun t => VG.Proof.Argon2.AArch64.FillCompress.Done s t ∧ t.sp = s.sp :=
  (VG.Proof.Argon2.AArch64.FillCompress.code_ok s h).mono (fun _ done => ⟨done, done.sp⟩)

end VG.Proof.Argon2.AArch64.FillCompress

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillKernelArgs`. -/
section

/-! Merged from `Proof.Argon2.AArch64.FillPointersNat`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillPointersArgs`. -/
section
/-! Short register-setup steps for the filling pointers. -/

namespace VG.Proof.Argon2.AArch64.FillPointers

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillPointers
open VG.Impl.Argon2.AArch64

theorem saveReference_ok (s : State) : WP isa (.block saveReference) s fun t =>
    t.gpr .x1 = s.gpr .x0 ∧ Divide.Keeps [.x1] s t := by
  apply WP.of_runBlock
  simp only [saveReference, Instructions.mov, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact by simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem currentArgs_ok (s : State) : WP isa (.block currentArgs) s fun t =>
    t.gpr .x8 = s.gpr .x24 ∧ Divide.Keeps [.x8] s t := by
  apply WP.of_runBlock
  simp only [currentArgs, Instructions.mov, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact by simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem previousArgs_ok (s : State) : WP isa (.block previousArgs) s fun t =>
    t.gpr .x6 = s.gpr .x8 ∧ t.gpr .x3 = s.gpr .x0 ∧ t.gpr .x8 = s.gpr .x24 ∧
    Divide.Keeps [.x6, .x3, .x8] s t := by
  apply WP.of_runBlock
  simp only [previousArgs, Instructions.mov, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem referenceArgs_ok (s : State) : WP isa (.block referenceArgs) s fun t =>
    t.gpr .x7 = s.gpr .x8 ∧ t.gpr .x3 = s.gpr .x1 ∧ t.gpr .x8 = s.gpr .x5 ∧
    Divide.Keeps [.x7, .x3, .x8] s t := by
  apply WP.of_runBlock
  simp only [referenceArgs, Instructions.mov, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem finishArgs_ok (s : State) : WP isa (.block finishArgs) s fun t =>
    t.gpr .x1 = s.gpr .x8 ∧ t.gpr .x0 = s.gpr .x7 ∧
    Divide.Keeps [.x1, .x0] s t := by
  apply WP.of_runBlock
  simp only [finishArgs, Instructions.mov, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.AArch64.FillPointers
end

/-! Merged from `Proof.Argon2.AArch64.FillPointers`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillColumn`. -/
section
/-! Current-column arithmetic and the cyclic predecessor, preserving the
matrix, enclosing loop registers and the stack pointer. -/

namespace VG.Proof.Argon2.AArch64.FillColumn

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillColumn
open VG.Impl.Argon2.AArch64

theorem current_ok (s : State) : WP isa (.block VG.Impl.Argon2.AArch64.FillColumn.current) s fun t =>
    t.gpr .x3 = s.gpr .x22 * s.gpr .x21 + s.gpr .x23 ∧
    Divide.Keeps [.x8, .x2, .x3, .x12, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.AArch64.FillColumn.current, Instructions.mov, Instructions.mul, Instructions.add,
    Instructions.mark, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left' ]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.2.2.2, ite_false]
  all_goals rfl

theorem compare_ok (s : State) : WP isa (.block [Instructions.comparei .x3 0].flatten) s
    fun t => t.gpr .x15 = s.gpr .x3 ∧ Divide.Keeps [.x12, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [Instructions.comparei, Instructions.compare, Instructions.imm,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    reduceCtorEq, ite_true, ite_false, show 0 < 65536 from by decide,
    Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceLT,
    BitVec.shiftLeft_zero, Bool.toNat_true, sub_value,
    show (BitVec.ofNat 16 0).setWidth 64 = 0#64 from rfl,
    BitVec.sub_zero, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem move_ok (s : State) (r : Reg) : WP isa (.block [Instructions.mov .x0 r].flatten) s
    fun t => t.gpr .x0 = s.gpr r ∧ Divide.Keeps [.x0, .x12, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [Instructions.mov, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    ite_true, Option.some.injEq, exists_eq_left' ]
  refine ⟨trivial, ?_⟩
  constructor
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, ite_false]
  all_goals rfl

theorem decrement_ok (s : State) : WP isa (.block [Instructions.subi .x0 1].flatten) s
    fun t => t.gpr .x0 = s.gpr .x0 - 1 ∧ Divide.Keeps [.x0, .x12, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [Instructions.subi, Instructions.sub, Instructions.imm, Instructions.mark, Instructions.mov,
    RegUpd.gpr_addWithCarry, show 1 < 65536 from by decide,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    Bool.toNat_true, sub_value,
    show (BitVec.ofNat 16 1).setWidth 64 = 1#64 from rfl, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left' ]
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.1, hr.2.1, hr.2.2.2.2, ite_false]
  all_goals rfl

theorem previous_ok (s : State) : WP isa VG.Impl.Argon2.AArch64.FillColumn.previous s fun t =>
    t.gpr .x0 = (if s.gpr .x3 = 0 then s.gpr .x20 else s.gpr .x3) - 1 ∧
    Divide.Keeps [.x0, .x12, .x13, .x14, .x15] s t := by
  unfold VG.Impl.Argon2.AArch64.FillColumn.previous
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillColumn.compare_ok s).mono ?_)
  rintro a ⟨flag, ka⟩
  have selected : WP isa VG.Impl.Argon2.AArch64.FillColumn.select a fun b =>
      b.gpr .x0 = (if s.gpr .x3 = 0 then s.gpr .x20 else s.gpr .x3) ∧
      Divide.Keeps [.x0, .x12, .x13, .x14, .x15] s b := by
    unfold VG.Impl.Argon2.AArch64.FillColumn.select
    refine WP.ite (decide (s.gpr .x3 = 0)) (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag, Bool.beq_eq_decide_eq]) ?_ ?_
    · intro h
      have zero := of_decide_eq_true h
      refine (VG.Proof.Argon2.AArch64.FillColumn.move_ok a .x20).mono ?_
      rintro b ⟨value, kb⟩
      exact ⟨by rw [value, ka.regs .x20 (by decide), ite_eq_left zero],
        (ka.mono (by decide)).trans kb⟩
    · intro h
      have nonzero := of_decide_eq_false h
      refine (VG.Proof.Argon2.AArch64.FillColumn.move_ok a .x3).mono ?_
      rintro b ⟨value, kb⟩
      exact ⟨by rw [value, ka.regs .x3 (by decide), ite_eq_right nonzero],
        (ka.mono (by decide)).trans kb⟩
  refine WP.seq (selected.mono ?_)
  rintro b ⟨value, kb⟩
  refine (VG.Proof.Argon2.AArch64.FillColumn.decrement_ok b).mono ?_
  rintro t ⟨result, kt⟩
  exact ⟨by rw [result, value], kb.trans kt⟩

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.AArch64.FillColumn.code s fun t =>
    let column := s.gpr .x22 * s.gpr .x21 + s.gpr .x23
    t.gpr .x3 = column ∧
    t.gpr .x0 = (if column = 0 then s.gpr .x20 else column) - 1 ∧
    Divide.Keeps [.x8, .x2, .x3, .x0, .x12, .x13, .x14, .x15] s t := by
  unfold VG.Impl.Argon2.AArch64.FillColumn.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillColumn.current_ok s).mono ?_)
  rintro a ⟨column, ka⟩
  refine (VG.Proof.Argon2.AArch64.FillColumn.previous_ok a).mono ?_
  rintro t ⟨previous, kt⟩
  refine ⟨(kt.regs .x3 (by decide)).trans column, ?_,
    (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [previous, column, ka.regs .x20 (by decide)]

theorem previous_nat (column q : Nat) (positive : 0 < q) (bound : column < q) :
    (if column = 0 then q else column) - 1 = (column + q - 1) % q := by
  by_cases zero : column = 0
  · simp only [zero, ite_true, Nat.zero_add]
    exact (Nat.mod_eq_of_lt (by omega : q - 1 < q)).symm
  · simp only [zero, ite_false]
    have sub : column + q - 1 - q = column - 1 := by omega
    rw [Nat.mod_eq_sub_mod (by omega : q ≤ column + q - 1), sub,
      Nat.mod_eq_of_lt (by omega : column - 1 < q)]

theorem previous_word_nat (column q : Nat) (positive : 0 < q) (qBound : q < 2 ^ 64)
    (bound : column < q) :
    (if BitVec.ofNat 64 column = 0#64 then BitVec.ofNat 64 q else BitVec.ofNat 64 column) - 1 =
      BitVec.ofNat 64 ((column + q - 1) % q) := by
  have zero : BitVec.ofNat 64 column = 0#64 ↔
      column = 0 := by
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans bound qBound)] at hn
      exact hn
    · intro h; rw [h]
  simp only [zero]
  by_cases h : column = 0
  · simp only [h, ite_true]
    rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat positive, Nat.zero_add, Nat.mod_eq_of_lt (by omega : q - 1 < q)]
  · simp only [h, ite_false]
    rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega : 1 ≤ column),
      ← VG.Proof.Argon2.AArch64.FillColumn.previous_nat _ q positive bound, ite_eq_right h]

theorem code_nat_ok (s : State) (slice segment index q : Nat)
    (hs : s.gpr .x22 = BitVec.ofNat 64 slice)
    (hg : s.gpr .x21 = BitVec.ofNat 64 segment)
    (hi : s.gpr .x23 = BitVec.ofNat 64 index)
    (hq : s.gpr .x20 = BitVec.ofNat 64 q)
    (positive : 0 < q) (qBound : q < 2 ^ 64)
    (bound : slice * segment + index < q) :
    WP isa VG.Impl.Argon2.AArch64.FillColumn.code s fun t =>
      t.gpr .x3 = BitVec.ofNat 64 (slice * segment + index) ∧
      t.gpr .x0 = BitVec.ofNat 64 ((slice * segment + index + q - 1) % q) ∧
      Divide.Keeps [.x8, .x2, .x3, .x0, .x12, .x13, .x14, .x15] s t := by
  refine (VG.Proof.Argon2.AArch64.FillColumn.code_ok s).mono ?_
  rintro t ⟨column, previous, keeps⟩
  have word : s.gpr .x22 * s.gpr .x21 + s.gpr .x23 =
      BitVec.ofNat 64 (slice * segment + index) := by
    rw [hs, hg, hi, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  refine ⟨column.trans word, ?_, keeps⟩
  rw [previous, word, hq]
  exact VG.Proof.Argon2.AArch64.FillColumn.previous_word_nat _ q positive qBound bound

end VG.Proof.Argon2.AArch64.FillColumn
end

/-! Compose the matrix addresses while retaining the enclosing loop position. -/

namespace VG.Proof.Argon2.AArch64.FillPointers

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillPointers
open VG.Impl.Argon2.AArch64

def address (base lane column q : Addr) : Addr := (lane * q + column) * 1024 + base

def column (s : State) : Addr := s.gpr .x22 * s.gpr .x21 + s.gpr .x23

def predecessor (s : State) : Addr :=
  (if VG.Proof.Argon2.AArch64.FillPointers.column s = 0 then s.gpr .x20 else VG.Proof.Argon2.AArch64.FillPointers.column s) - 1

def changed : List Reg := [.x8, .x2, .x3, .x0, .x1, .x6, .x7, .x12, .x13, .x14, .x15]

theorem current_ok (s : State) : WP isa VG.Impl.Argon2.AArch64.FillPointers.current s fun t =>
    t.gpr .x8 = VG.Proof.Argon2.AArch64.FillPointers.address (s.gpr .x4) (s.gpr .x24) (s.gpr .x3) (s.gpr .x20) ∧
    Divide.Keeps [.x8, .x2, .x15] s t := by
  unfold VG.Impl.Argon2.AArch64.FillPointers.current
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillPointers.currentArgs_ok s).mono ?_)
  rintro a ⟨lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨?_, (ka.mono (by decide)).trans kt⟩
  rw [pointer, lane, ka.regs .x20 (by decide), ka.regs .x3 (by decide), ka.regs .x4 (by decide), VG.Proof.Argon2.AArch64.FillPointers.address]

theorem previous_ok (s : State) : WP isa VG.Impl.Argon2.AArch64.FillPointers.previous s fun t =>
    t.gpr .x6 = s.gpr .x8 ∧
    t.gpr .x8 = VG.Proof.Argon2.AArch64.FillPointers.address (s.gpr .x4) (s.gpr .x24) (s.gpr .x0) (s.gpr .x20) ∧
    Divide.Keeps [.x8, .x2, .x3, .x6, .x15] s t := by
  unfold VG.Impl.Argon2.AArch64.FillPointers.previous
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillPointers.previousArgs_ok s).mono ?_)
  rintro a ⟨saved, col, lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨(kt.regs .x6 (by decide)).trans saved, ?_,
    (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [pointer, lane, col, ka.regs .x20 (by decide), ka.regs .x4 (by decide), VG.Proof.Argon2.AArch64.FillPointers.address]

theorem reference_ok (s : State) : WP isa reference s fun t =>
    t.gpr .x7 = s.gpr .x8 ∧
    t.gpr .x8 = VG.Proof.Argon2.AArch64.FillPointers.address (s.gpr .x4) (s.gpr .x5) (s.gpr .x1) (s.gpr .x20) ∧
    Divide.Keeps [.x8, .x2, .x3, .x7, .x15] s t := by
  unfold reference
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillPointers.referenceArgs_ok s).mono ?_)
  rintro a ⟨saved, col, lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨(kt.regs .x7 (by decide)).trans saved, ?_,
    (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [pointer, lane, col, ka.regs .x20 (by decide), ka.regs .x4 (by decide), VG.Proof.Argon2.AArch64.FillPointers.address]

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.AArch64.FillPointers.code s fun t =>
    t.gpr .x6 = VG.Proof.Argon2.AArch64.FillPointers.address (s.gpr .x4) (s.gpr .x24) (VG.Proof.Argon2.AArch64.FillPointers.column s) (s.gpr .x20) ∧
    t.gpr .x0 = VG.Proof.Argon2.AArch64.FillPointers.address (s.gpr .x4) (s.gpr .x24) (VG.Proof.Argon2.AArch64.FillPointers.predecessor s) (s.gpr .x20) ∧
    t.gpr .x1 = VG.Proof.Argon2.AArch64.FillPointers.address (s.gpr .x4) (s.gpr .x5) (s.gpr .x0) (s.gpr .x20) ∧
    Divide.Keeps VG.Proof.Argon2.AArch64.FillPointers.changed s t := by
  unfold VG.Impl.Argon2.AArch64.FillPointers.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillPointers.saveReference_ok s).mono ?_)
  rintro a ⟨refColumn, ka⟩
  refine WP.seq ((FillColumn.code_ok a).mono ?_)
  rintro b ⟨curColumn, prevColumn, kb⟩
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillPointers.current_ok b).mono ?_)
  rintro c ⟨curPointer, kc⟩
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillPointers.previous_ok c).mono ?_)
  rintro d ⟨savedCurrent, prevPointer, kd⟩
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillPointers.reference_ok d).mono ?_)
  rintro e ⟨savedPrevious, refPointer, ke⟩
  refine (VG.Proof.Argon2.AArch64.FillPointers.finishArgs_ok e).mono ?_
  rintro t ⟨referenceResult, previousResult, kt⟩
  have coords : VG.Proof.Argon2.AArch64.FillPointers.column a = VG.Proof.Argon2.AArch64.FillPointers.column s := by
    unfold VG.Proof.Argon2.AArch64.FillPointers.column
    rw [ka.regs .x22 (by decide), ka.regs .x21 (by decide), ka.regs .x23 (by decide)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [kt.regs .x6 (by decide), ke.regs .x6 (by decide), savedCurrent, curPointer,
      kb.regs .x4 (by decide), ka.regs .x4 (by decide), kb.regs .x24 (by decide),
      ka.regs .x24 (by decide), kb.regs .x20 (by decide), ka.regs .x20 (by decide), curColumn]
    exact congrArg (fun col => VG.Proof.Argon2.AArch64.FillPointers.address (s.gpr .x4) (s.gpr .x24) col (s.gpr .x20)) coords
  · rw [previousResult, savedPrevious, prevPointer, kc.regs .x4 (by decide),
      kc.regs .x24 (by decide), kc.regs .x0 (by decide), kc.regs .x20 (by decide),
      kb.regs .x4 (by decide), ka.regs .x4 (by decide), kb.regs .x24 (by decide),
      ka.regs .x24 (by decide), kb.regs .x20 (by decide), ka.regs .x20 (by decide), prevColumn]
    change VG.Proof.Argon2.AArch64.FillPointers.address _ _ ((if VG.Proof.Argon2.AArch64.FillPointers.column a = 0 then a.gpr .x20 else VG.Proof.Argon2.AArch64.FillPointers.column a) - 1) _ = _
    rw [coords, ka.regs .x20 (by decide), VG.Proof.Argon2.AArch64.FillPointers.predecessor]
  · rw [referenceResult, refPointer, kd.regs .x4 (by decide), kd.regs .x5 (by decide),
      kd.regs .x1 (by decide), kd.regs .x20 (by decide), kc.regs .x4 (by decide),
      kc.regs .x5 (by decide), kc.regs .x1 (by decide), kc.regs .x20 (by decide),
      kb.regs .x4 (by decide), kb.regs .x5 (by decide), kb.regs .x1 (by decide),
      kb.regs .x20 (by decide), ka.regs .x4 (by decide), ka.regs .x5 (by decide),
      ka.regs .x20 (by decide), refColumn]
  · exact (((((ka.mono (by simp [VG.Proof.Argon2.AArch64.FillPointers.changed])).trans (kb.mono (by simp [VG.Proof.Argon2.AArch64.FillPointers.changed]))).trans
      (kc.mono (by simp [VG.Proof.Argon2.AArch64.FillPointers.changed]))).trans (kd.mono (by simp [VG.Proof.Argon2.AArch64.FillPointers.changed]))).trans
      (ke.mono (by simp [VG.Proof.Argon2.AArch64.FillPointers.changed]))).trans (kt.mono (by simp [VG.Proof.Argon2.AArch64.FillPointers.changed]))

end VG.Proof.Argon2.AArch64.FillPointers
end

/-! Matrix pointers are the natural-number block offsets in the specification. -/

namespace VG.Proof.Argon2.AArch64.FillPointers

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillPointers

def cell (base : Addr) (p : Spec.Argon2.Params) (lane column : Nat) : Addr :=
  off base ((lane * p.laneLen + column) * 1024)

theorem address_nat (base : Addr) (lane column q : Nat) :
    VG.Proof.Argon2.AArch64.FillPointers.address base (BitVec.ofNat 64 lane) (BitVec.ofNat 64 column) (BitVec.ofNat 64 q) =
      off base ((lane * q + column) * 1024) := by
  unfold VG.Proof.Argon2.AArch64.FillPointers.address off
  change (BitVec.ofNat 64 lane * BitVec.ofNat 64 q + BitVec.ofNat 64 column) *
    BitVec.ofNat 64 1024 + base = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, ← BitVec.ofNat_mul, BitVec.add_comm]

theorem code_nat_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index refLane refColumn : Nat)
    (bounds : ReferenceMap.Bounds p pass lane slice index)
    (position : ReferenceMap.Position p lane slice index s)
    (rl : s.gpr .x5 = BitVec.ofNat 64 refLane)
    (rc : s.gpr .x0 = BitVec.ofNat 64 refColumn) :
    WP isa VG.Impl.Argon2.AArch64.FillPointers.code s fun t =>
      t.gpr .x6 = VG.Proof.Argon2.AArch64.FillPointers.cell (s.gpr .x4) p lane (slice * p.segmentLen + index) ∧
      t.gpr .x0 = VG.Proof.Argon2.AArch64.FillPointers.cell (s.gpr .x4) p lane ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen) ∧
      t.gpr .x1 = VG.Proof.Argon2.AArch64.FillPointers.cell (s.gpr .x4) p refLane refColumn ∧ Divide.Keeps VG.Proof.Argon2.AArch64.FillPointers.changed s t := by
  refine (VG.Proof.Argon2.AArch64.FillPointers.code_ok s).mono ?_
  rintro t ⟨current, previous, reference, keeps⟩
  have col : VG.Proof.Argon2.AArch64.FillPointers.column s = BitVec.ofNat 64 (slice * p.segmentLen + index) := by
    unfold VG.Proof.Argon2.AArch64.FillPointers.column
    rw [position.slice, position.segmentLength, position.index, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  have prev : VG.Proof.Argon2.AArch64.FillPointers.predecessor s = BitVec.ofNat 64
      ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen) := by
    unfold VG.Proof.Argon2.AArch64.FillPointers.predecessor
    rw [col, position.laneLength]
    have positive := Proof.Argon2.segmentLen_ge_two p bounds.lanesPositive bounds.memoryMinimum
    have q := Proof.Argon2.laneLen_segments p bounds.lanesPositive
    exact FillColumn.previous_word_nat _ _ (by omega)
      (Nat.lt_trans bounds.laneLength_bound (by decide))
      (Proof.Argon2.column_lt p bounds.lanesPositive bounds.sliceBound bounds.indexBound)
  refine ⟨?_, ?_, ?_, keeps⟩
  · rw [current, position.current, col, position.laneLength, VG.Proof.Argon2.AArch64.FillPointers.address_nat]; rfl
  · rw [previous, position.current, prev, position.laneLength, VG.Proof.Argon2.AArch64.FillPointers.address_nat]; rfl
  · rw [reference, rl, rc, position.laneLength, VG.Proof.Argon2.AArch64.FillPointers.address_nat]; rfl

end VG.Proof.Argon2.AArch64.FillPointers
end

/-! Merged from `Proof.Argon2.AArch64.FillKernelLayout`. -/
section
/-! One allocation invariant covers all matrix cells used by the filling step. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

def matrix (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 232) 64

def work (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 248) 64

structure Layout (p : VG.Spec.Argon2.Params) (s : State) : Prop where
  frameRead : ∀ d ∈ [0, 16, 184, 232, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  frameWrite : InRegions s.wr (off (s.gpr .x19) 16) 8
  matrixWrite : Covers [⟨VG.Proof.Argon2.AArch64.FillKernel.matrix s, p.blocks * 1024⟩] s.wr
  workWrite : Covers [⟨VG.Proof.Argon2.AArch64.FillKernel.work s, 5120⟩] s.wr
  matrixWork : (⟨VG.Proof.Argon2.AArch64.FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨VG.Proof.Argon2.AArch64.FillKernel.work s, 5120⟩
  matrixFrame : (⟨VG.Proof.Argon2.AArch64.FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩
  matrixStack : (⟨VG.Proof.Argon2.AArch64.FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint (below s.sp 8)
  frameWork : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨VG.Proof.Argon2.AArch64.FillKernel.work s, 5120⟩
  frameStack : (⟨s.gpr .x19, 272⟩ : Region).Disjoint (below s.sp 8)
  stackWork : (below s.sp 8).Disjoint ⟨VG.Proof.Argon2.AArch64.FillKernel.work s, 5120⟩

theorem Layout.of_keeps {p : VG.Spec.Argon2.Params} {s t : State} (h : VG.Proof.Argon2.AArch64.FillKernel.Layout p s)
    (k : Divide.Keeps ReferenceMap.changed s t) : VG.Proof.Argon2.AArch64.FillKernel.Layout p t := by
  have bp := k.regs .x19 (by decide)
  have sp := k.sp
  have matrix' : VG.Proof.Argon2.AArch64.FillKernel.matrix t = VG.Proof.Argon2.AArch64.FillKernel.matrix s := by unfold VG.Proof.Argon2.AArch64.FillKernel.matrix; rw [bp, k.mem]
  have work' : VG.Proof.Argon2.AArch64.FillKernel.work t = VG.Proof.Argon2.AArch64.FillKernel.work s := by unfold VG.Proof.Argon2.AArch64.FillKernel.work; rw [bp, k.mem]
  constructor
  · rw [k.rd, k.wr, bp]; exact h.frameRead
  · rw [k.wr, bp]; exact h.frameWrite
  · rw [matrix', k.wr]; exact h.matrixWrite
  · rw [work', k.wr]; exact h.workWrite
  · rw [matrix', work']; exact h.matrixWork
  · rw [matrix', bp]; exact h.matrixFrame
  · rw [matrix', sp]; exact h.matrixStack
  · rw [bp, work']; exact h.frameWork
  · rw [bp, sp]; exact h.frameStack
  · rw [sp, work']; exact h.stackWork

theorem cell_sub (p : VG.Spec.Argon2.Params) (base : Addr) (positive : 0 < p.lanes) {lane column : Nat}
    (hl : lane < p.lanes) (hc : column < p.laneLen) :
    Region.Sub ⟨FillPointers.cell base p lane column, 1024⟩ ⟨base, p.blocks * 1024⟩ :=
  Offset.sub_base base (Proof.Argon2.cell_bytes p positive hl hc)

theorem Layout.cell_cover {p : VG.Spec.Argon2.Params} {s : State} (h : VG.Proof.Argon2.AArch64.FillKernel.Layout p s) (positive : 0 < p.lanes)
    {lane column : Nat} (hl : lane < p.lanes) (hc : column < p.laneLen) :
    Covers [⟨FillPointers.cell (VG.Proof.Argon2.AArch64.FillKernel.matrix s) p lane column, 1024⟩] s.wr := by
  have sub : Covers [⟨FillPointers.cell (VG.Proof.Argon2.AArch64.FillKernel.matrix s) p lane column, 1024⟩]
      [⟨VG.Proof.Argon2.AArch64.FillKernel.matrix s, p.blocks * 1024⟩] := Covers.of_sub (by
        intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact ⟨⟨VG.Proof.Argon2.AArch64.FillKernel.matrix s, p.blocks * 1024⟩, by simp, (lane * p.laneLen + column) * 1024,
          rfl, Proof.Argon2.cell_bytes p positive hl hc⟩)
  exact fun a n ha => h.matrixWrite a n (sub a n ha)

theorem compress_ready (p : VG.Spec.Argon2.Params) (s : State) (layout : VG.Proof.Argon2.AArch64.FillKernel.Layout p s)
    (positive : 0 < p.lanes) (leftLane leftColumn rightLane rightColumn destLane destColumn : Nat)
    (ll : leftLane < p.lanes) (lc : leftColumn < p.laneLen)
    (rl : rightLane < p.lanes) (rc : rightColumn < p.laneLen)
    (dl : destLane < p.lanes) (dc : destColumn < p.laneLen)
    (left : s.gpr .x0 = FillPointers.cell (VG.Proof.Argon2.AArch64.FillKernel.matrix s) p leftLane leftColumn)
    (right : s.gpr .x1 = FillPointers.cell (VG.Proof.Argon2.AArch64.FillKernel.matrix s) p rightLane rightColumn)
    (dest : s.gpr .x6 = FillPointers.cell (VG.Proof.Argon2.AArch64.FillKernel.matrix s) p destLane destColumn) : FillCompress.Ready s := by
  have leftSub := VG.Proof.Argon2.AArch64.FillKernel.cell_sub p (VG.Proof.Argon2.AArch64.FillKernel.matrix s) positive ll lc
  have rightSub := VG.Proof.Argon2.AArch64.FillKernel.cell_sub p (VG.Proof.Argon2.AArch64.FillKernel.matrix s) positive rl rc
  have destSub := VG.Proof.Argon2.AArch64.FillKernel.cell_sub p (VG.Proof.Argon2.AArch64.FillKernel.matrix s) positive dl dc
  have read (lane column : Nat) (hl : lane < p.lanes) (hc : column < p.laneLen) :
      Covers [⟨FillPointers.cell (VG.Proof.Argon2.AArch64.FillKernel.matrix s) p lane column, 1024⟩] (s.rd ++ s.wr) := by
    intro a n ha
    obtain ⟨r, hr, hc⟩ := layout.cell_cover positive hl hc a n ha
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  constructor
  · intro d hd
    exact layout.frameRead d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> simp)
  · exact layout.frameWrite
  · rw [left]; exact read leftLane leftColumn ll lc
  · rw [right]; exact read rightLane rightColumn rl rc
  · rw [dest]; exact layout.cell_cover positive dl dc
  · exact layout.workWrite
  · rw [left]; exact layout.matrixWork.sub_left leftSub
  · rw [right]; exact layout.matrixWork.sub_left rightSub
  · rw [dest]; exact layout.matrixWork.sub_left destSub
  · exact layout.frameWork
  · rw [left]; exact layout.matrixFrame.sub_left leftSub
  · rw [right]; exact layout.matrixFrame.sub_left rightSub
  · rw [dest]; exact layout.matrixFrame.sub_left destSub
  · rw [left]; exact (layout.matrixStack.sub_left leftSub).symm
  · rw [right]; exact (layout.matrixStack.sub_left rightSub).symm
  · exact layout.stackWork
  · rw [dest]; exact layout.matrixStack.sub_left destSub
  · exact layout.frameStack

end VG.Proof.Argon2.AArch64.FillKernel
end

/-! Reload frame arguments and compose reference mapping with matrix addresses. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

theorem load_ok (s : State) (r : Reg) (d : Nat) (ha : d % 8 = 0) (hb : d < 32768)
    (read : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.load r .x19 d].flatten) s fun t =>
      t.gpr r = s.mem.readW (off (s.gpr .x19) d) 64 ∧ Divide.Keeps [r] s t := by
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using
    Instructions.load_ok s r .x19 d ha hb read

structure Ready (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat) (s : State) : Prop where
  layout : VG.Proof.Argon2.AArch64.FillKernel.Layout p s
  bounds : ReferenceMap.Bounds p pass lane slice index
  position : ReferenceMap.Position p lane slice index s
  passWord : s.mem.readW (off (s.gpr .x19) 0) 64 = BitVec.ofNat 64 pass
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

structure Mapped (s t : State) (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat) : Prop where
  selected : t.gpr .x5 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .x0)).1
  column : t.gpr .x0 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .x0)).2
  original : t.gpr .x7 = s.gpr .x0
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem mapping_ok (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat)
    (h : VG.Proof.Argon2.AArch64.FillKernel.Ready p pass lane slice index s) :
    WP isa Impl.Argon2.AArch64.FillKernel.mapping s (VG.Proof.Argon2.AArch64.FillKernel.Mapped s · p pass lane slice index) := by
  unfold Impl.Argon2.AArch64.FillKernel.mapping Impl.Argon2.AArch64.FillKernel.lanes
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillKernel.load_ok s .x1 184 (by decide) (by decide) (h.layout.frameRead 184 (by simp))).mono ?_)
  rintro a ⟨lanes, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s a := keeps.mono (by decide)
  have ready : ReferenceMap.Ready p pass lane slice index a := by
    refine ⟨h.bounds, h.position.of_keeps k, lanes.trans h.lanesWord, ?_, ?_⟩
    · rw [k.rd, k.wr, k.regs .x19 (by decide)]
      simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
        using h.layout.frameRead 0 (by simp)
    · rw [k.mem, k.regs .x19 (by decide)]
      simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using h.passWord
  refine (ReferenceMap.code_spec_ok a p pass lane slice index ready).mono ?_
  rintro t ⟨lane, column, original, tail⟩
  rw [keeps.regs .x0 (by decide)] at lane column original
  exact ⟨lane, column, original, k.trans tail⟩

structure Pointers (s t : State) (p : VG.Spec.Argon2.Params) (lane slice index refLane refColumn : Nat) : Prop where
  current : t.gpr .x6 = FillPointers.cell (VG.Proof.Argon2.AArch64.FillKernel.matrix s) p lane (slice * p.segmentLen + index)
  previous : t.gpr .x0 = FillPointers.cell (VG.Proof.Argon2.AArch64.FillKernel.matrix s) p lane
    ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen)
  reference : t.gpr .x1 = FillPointers.cell (VG.Proof.Argon2.AArch64.FillKernel.matrix s) p refLane refColumn
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem pointers_ok (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice index refLane refColumn : Nat)
    (layout : VG.Proof.Argon2.AArch64.FillKernel.Layout p s) (bounds : ReferenceMap.Bounds p pass lane slice index)
    (position : ReferenceMap.Position p lane slice index s)
    (laneWord : s.gpr .x5 = BitVec.ofNat 64 refLane) (columnWord : s.gpr .x0 = BitVec.ofNat 64 refColumn) :
    WP isa Impl.Argon2.AArch64.FillKernel.pointers s (VG.Proof.Argon2.AArch64.FillKernel.Pointers s · p lane slice index refLane refColumn) := by
  unfold Impl.Argon2.AArch64.FillKernel.pointers Impl.Argon2.AArch64.FillKernel.matrix
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillKernel.load_ok s .x4 232 (by decide) (by decide) (layout.frameRead 232 (by simp))).mono ?_)
  rintro a ⟨base, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s a := keeps.mono (by decide)
  have lane' : a.gpr .x5 = BitVec.ofNat 64 refLane := (keeps.regs .x5 (by decide)).trans laneWord
  have col' : a.gpr .x0 = BitVec.ofNat 64 refColumn := (keeps.regs .x0 (by decide)).trans columnWord
  refine (FillPointers.code_nat_ok a p pass lane slice index refLane refColumn bounds
    (position.of_keeps k) lane' col').mono ?_
  rintro t ⟨current, previous, reference, tail⟩
  rw [base] at current previous reference
  exact ⟨current, previous, reference, k.trans (tail.mono (by decide))⟩

end VG.Proof.Argon2.AArch64.FillKernel

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillKernelPrepare`. -/
section

/-! Complete active-cell update from a random word and the matrix allocation. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

def currentColumn (p : VG.Spec.Argon2.Params) (slice index : Nat) : Nat := slice * p.segmentLen + index

def previousColumn (p : VG.Spec.Argon2.Params) (slice index : Nat) : Nat :=
  (VG.Proof.Argon2.AArch64.FillKernel.currentColumn p slice index + p.laneLen - 1) % p.laneLen

def current (s : State) (p : VG.Spec.Argon2.Params) (lane slice index : Nat) : Addr :=
  FillPointers.cell (VG.Proof.Argon2.AArch64.FillKernel.matrix s) p lane (VG.Proof.Argon2.AArch64.FillKernel.currentColumn p slice index)

def previous (s : State) (p : VG.Spec.Argon2.Params) (lane slice index : Nat) : Addr :=
  FillPointers.cell (VG.Proof.Argon2.AArch64.FillKernel.matrix s) p lane (VG.Proof.Argon2.AArch64.FillKernel.previousColumn p slice index)

def referenced (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat) : Addr :=
  let ref := Spec.Argon2.reference p pass lane slice index (s.gpr .x0)
  FillPointers.cell (VG.Proof.Argon2.AArch64.FillKernel.matrix s) p ref.1 ref.2

structure Prepared (s t : State) (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat) : Prop where
  ready : FillCompress.Ready t
  currentPtr : t.gpr .x6 = VG.Proof.Argon2.AArch64.FillKernel.current s p lane slice index
  previousPtr : t.gpr .x0 = VG.Proof.Argon2.AArch64.FillKernel.previous s p lane slice index
  referencePtr : t.gpr .x1 = VG.Proof.Argon2.AArch64.FillKernel.referenced s p pass lane slice index
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem prepare_ok (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat)
    (h : VG.Proof.Argon2.AArch64.FillKernel.Ready p pass lane slice index s) :
    WP isa Impl.Argon2.AArch64.FillKernel.prepare s (VG.Proof.Argon2.AArch64.FillKernel.Prepared s · p pass lane slice index) := by
  unfold Impl.Argon2.AArch64.FillKernel.prepare
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillKernel.mapping_ok s p pass lane slice index h).mono ?_)
  intro a mapped
  let ref := Spec.Argon2.reference p pass lane slice index (s.gpr .x0)
  refine ((VG.Proof.Argon2.AArch64.FillKernel.pointers_ok a p pass lane slice index ref.1 ref.2
    (h.layout.of_keeps mapped.keeps) h.bounds (h.position.of_keeps mapped.keeps)
    mapped.selected mapped.column).mono ?_)
  intro b pointers
  have keeps := mapped.keeps.trans pointers.keeps
  have matrixA : VG.Proof.Argon2.AArch64.FillKernel.matrix a = VG.Proof.Argon2.AArch64.FillKernel.matrix s := by
    unfold VG.Proof.Argon2.AArch64.FillKernel.matrix; rw [mapped.keeps.mem, mapped.keeps.regs .x19 (by decide)]
  have matrixB : VG.Proof.Argon2.AArch64.FillKernel.matrix b = VG.Proof.Argon2.AArch64.FillKernel.matrix a := by
    unfold VG.Proof.Argon2.AArch64.FillKernel.matrix; rw [pointers.keeps.mem, pointers.keeps.regs .x19 (by decide)]
  have cur : b.gpr .x6 = VG.Proof.Argon2.AArch64.FillKernel.current s p lane slice index := by
    rw [pointers.current, matrixA]; rfl
  have prev : b.gpr .x0 = VG.Proof.Argon2.AArch64.FillKernel.previous s p lane slice index := by
    rw [pointers.previous, matrixA]; rfl
  have other : b.gpr .x1 = VG.Proof.Argon2.AArch64.FillKernel.referenced s p pass lane slice index := by
    rw [pointers.reference, matrixA]; rfl
  have columnBound := Proof.Argon2.column_lt p h.bounds.lanesPositive h.bounds.sliceBound h.bounds.indexBound
  have previousBound := Proof.Argon2.previous_column_lt p h.bounds.lanesPositive h.bounds.memoryMinimum
    (slice * p.segmentLen + index)
  obtain ⟨refLane, refColumn⟩ := Proof.Argon2.reference_bounds p h.bounds.lanesPositive
    h.bounds.memoryMinimum pass lane slice index (s.gpr .x0) h.bounds.laneBound
  have compressReady : FillCompress.Ready b := by
    apply VG.Proof.Argon2.AArch64.FillKernel.compress_ready p b (h.layout.of_keeps keeps) h.bounds.lanesPositive
      lane (VG.Proof.Argon2.AArch64.FillKernel.previousColumn p slice index) ref.1 ref.2 lane (VG.Proof.Argon2.AArch64.FillKernel.currentColumn p slice index)
      h.bounds.laneBound previousBound refLane refColumn h.bounds.laneBound columnBound
    · rw [pointers.previous, matrixB]; rfl
    · rw [pointers.reference, matrixB]
    · rw [pointers.current, matrixB]; rfl
  exact ⟨compressReady, cur, prev, other, keeps⟩

end VG.Proof.Argon2.AArch64.FillKernel

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillKernel`. -/
section

/-! Complete active-cell update from a random word and the matrix allocation. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

def writes (s : State) (p : VG.Spec.Argon2.Params) (lane slice index : Nat) : List Region :=
  [⟨VG.Proof.Argon2.AArch64.FillKernel.current s p lane slice index, 1024⟩, ⟨VG.Proof.Argon2.AArch64.FillKernel.work s, 5120⟩,
    below s.sp 8, ⟨off (s.gpr .x19) 16, 8⟩]

structure Done (s t : State) (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat) : Prop where
  block : VG.Spec.Argon2.blockAt t.mem (VG.Proof.Argon2.AArch64.FillKernel.current s p lane slice index) =
    let next := Spec.Argon2.compress (VG.Spec.Argon2.blockAt s.mem (VG.Proof.Argon2.AArch64.FillKernel.previous s p lane slice index))
      (VG.Spec.Argon2.blockAt s.mem (VG.Proof.Argon2.AArch64.FillKernel.referenced s p pass lane slice index))
    if pass = 0 then next else xorBlock next (VG.Spec.Argon2.blockAt s.mem (VG.Proof.Argon2.AArch64.FillKernel.current s p lane slice index))
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.AArch64.FillKernel.writes s p lane slice index) s.mem t.mem
  sp : t.sp = s.sp

theorem code_ok (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat)
    (h : VG.Proof.Argon2.AArch64.FillKernel.Ready p pass lane slice index s) :
    WP isa Impl.Argon2.AArch64.FillKernel.code s (VG.Proof.Argon2.AArch64.FillKernel.Done s · p pass lane slice index) := by
  unfold Impl.Argon2.AArch64.FillKernel.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillKernel.prepare_ok s p pass lane slice index h).mono ?_)
  intro b prepared
  have keeps := prepared.keeps
  have cur := prepared.currentPtr
  have prev := prepared.previousPtr
  have other := prepared.referencePtr
  refine (FillCompress.code_sp_ok b prepared.ready).mono ?_
  rintro t ⟨done, mx⟩
  have counter : FillCompress.pass b = BitVec.ofNat 64 pass := by
    unfold FillCompress.pass
    rw [keeps.mem, keeps.regs .x19 (by decide)]
    exact h.passWord
  refine ⟨?_, ?_, done.rd.trans keeps.rd, done.wr.trans keeps.wr, ?_, mx.trans keeps.sp⟩
  · have block := done.block
    rw [cur, prev, other, keeps.mem, counter] at block
    simp only [ReferenceMap.word_zero pass (Nat.lt_trans h.bounds.passBound (by decide))] at block
    exact block
  · intro r hr
    have ne : r ∉ ReferenceMap.changed := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (done.regs r hr).trans (keeps.regs r ne)
  · have workB : FillCompress.work b = VG.Proof.Argon2.AArch64.FillKernel.work s := by
      unfold FillCompress.work VG.Proof.Argon2.AArch64.FillKernel.work
      rw [keeps.regs .x19 (by decide), keeps.mem]
    have frame := done.frame
    rw [FillCompress.writes, workB, cur, keeps.sp, keeps.regs .x19 (by decide), keeps.mem] at frame
    change Frame [⟨VG.Proof.Argon2.AArch64.FillKernel.current s p lane slice index, 1024⟩, ⟨VG.Proof.Argon2.AArch64.FillKernel.work s + 4096, 1024⟩,
      ⟨VG.Proof.Argon2.AArch64.FillKernel.work s, 4096⟩, below s.sp 8, ⟨off (s.gpr .x19) 16, 8⟩] s.mem t.mem at frame
    apply frame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [VG.Proof.Argon2.AArch64.FillKernel.writes], fun _ h => h⟩
    · exact ⟨⟨VG.Proof.Argon2.AArch64.FillKernel.work s, 5120⟩, by simp [VG.Proof.Argon2.AArch64.FillKernel.writes], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨VG.Proof.Argon2.AArch64.FillKernel.work s, 5120⟩, by simp [VG.Proof.Argon2.AArch64.FillKernel.writes], Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp [VG.Proof.Argon2.AArch64.FillKernel.writes], fun _ h => h⟩
    · exact ⟨_, by simp [VG.Proof.Argon2.AArch64.FillKernel.writes], fun _ h => h⟩

end VG.Proof.Argon2.AArch64.FillKernel

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillKernelSpec`. -/
section

/-! Merged from `Proof.Argon2.AArch64.FillKernelMatrix`. -/
section
/-! The filling step updates exactly one cell of the specification's block array. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

def currentIndex (p : VG.Spec.Argon2.Params) (lane slice index : Nat) : Nat :=
  lane * p.laneLen + VG.Proof.Argon2.AArch64.FillKernel.currentColumn p slice index

def previousIndex (p : VG.Spec.Argon2.Params) (lane slice index : Nat) : Nat :=
  lane * p.laneLen + VG.Proof.Argon2.AArch64.FillKernel.previousColumn p slice index

def referenceIndex (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat) : Nat :=
  let ref := Spec.Argon2.reference p pass lane slice index (s.gpr .x0)
  ref.1 * p.laneLen + ref.2

def nextBlock (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat) (blocks : Array VG.Spec.Argon2.Block) : VG.Spec.Argon2.Block :=
  let next := Spec.Argon2.compress (blocks[VG.Proof.Argon2.AArch64.FillKernel.previousIndex p lane slice index]?.getD zeroBlock)
    (blocks[VG.Proof.Argon2.AArch64.FillKernel.referenceIndex s p pass lane slice index]?.getD zeroBlock)
  if pass = 0 then next else xorBlock next (blocks[VG.Proof.Argon2.AArch64.FillKernel.currentIndex p lane slice index]?.getD zeroBlock)

theorem Done.represents {s t : State} {p : VG.Spec.Argon2.Params} {pass lane slice index : Nat}
    (ready : VG.Proof.Argon2.AArch64.FillKernel.Ready p pass lane slice index s) (done : VG.Proof.Argon2.AArch64.FillKernel.Done s t p pass lane slice index)
    (blocks : Array VG.Spec.Argon2.Block) (represented : Proof.Argon2.Represents s.mem (VG.Proof.Argon2.AArch64.FillKernel.matrix s) p.blocks blocks) :
    Proof.Argon2.Represents t.mem (VG.Proof.Argon2.AArch64.FillKernel.matrix s) p.blocks
      (blocks.set! (VG.Proof.Argon2.AArch64.FillKernel.currentIndex p lane slice index) (VG.Proof.Argon2.AArch64.FillKernel.nextBlock s p pass lane slice index blocks)) := by
  have currentBound := Proof.Argon2.current_cell_lt p ready.bounds.lanesPositive
    ready.bounds.laneBound ready.bounds.sliceBound ready.bounds.indexBound
  have previousBound := Proof.Argon2.previous_cell_lt p ready.bounds.lanesPositive
    ready.bounds.memoryMinimum ready.bounds.laneBound (column := VG.Proof.Argon2.AArch64.FillKernel.currentColumn p slice index)
  have referenceBound := Proof.Argon2.reference_cell_lt p ready.bounds.lanesPositive
    ready.bounds.memoryMinimum pass lane slice index (s.gpr .x0) ready.bounds.laneBound
  apply represented.update (VG.Proof.Argon2.AArch64.FillKernel.currentIndex p lane slice index) currentBound (VG.Proof.Argon2.AArch64.FillKernel.nextBlock s p pass lane slice index blocks)
  · have block := done.block
    change VG.Spec.Argon2.blockAt t.mem (Proof.Argon2.matrixCell (VG.Proof.Argon2.AArch64.FillKernel.matrix s) (VG.Proof.Argon2.AArch64.FillKernel.currentIndex p lane slice index)) = _ at block
    have prev := represented.block (VG.Proof.Argon2.AArch64.FillKernel.previousIndex p lane slice index) previousBound
    have other := represented.block (VG.Proof.Argon2.AArch64.FillKernel.referenceIndex s p pass lane slice index) referenceBound
    have old := represented.block (VG.Proof.Argon2.AArch64.FillKernel.currentIndex p lane slice index) currentBound
    change VG.Spec.Argon2.blockAt s.mem (VG.Proof.Argon2.AArch64.FillKernel.previous s p lane slice index) = _ at prev
    change VG.Spec.Argon2.blockAt s.mem (VG.Proof.Argon2.AArch64.FillKernel.referenced s p pass lane slice index) = _ at other
    change VG.Spec.Argon2.blockAt s.mem (VG.Proof.Argon2.AArch64.FillKernel.current s p lane slice index) = _ at old
    rw [prev, other, old] at block
    exact block
  · intro j hj different
    apply FillCompress.block_frame done.frame
    intro r hr
    simp only [VG.Proof.Argon2.AArch64.FillKernel.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · have blocksBound := Nat.lt_of_le_of_lt (Proof.Argon2.blocks_le_memory p) ready.bounds.memoryBound
      exact Proof.Argon2.matrixCell_disjoint _ p.blocks j (VG.Proof.Argon2.AArch64.FillKernel.currentIndex p lane slice index)
        (Nat.lt_trans (Nat.mul_lt_mul_of_pos_right blocksBound (by decide)) (by decide)) hj currentBound different
    · exact ready.layout.matrixWork.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hj)
    · exact ready.layout.matrixStack.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hj)
    · exact (ready.layout.matrixFrame.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hj)).sub_right
        (Offset.sub_base _ (by decide))

end VG.Proof.Argon2.AArch64.FillKernel
end

/-! Relate the complete assembly step to the reviewed filling-state transition. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

theorem update_spec (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat) (state : FillState)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index)
    (random : s.gpr .x0 = Proof.Argon2.FillStep.random p pass lane slice index state.memory) :
    state.memory.set! (VG.Proof.Argon2.AArch64.FillKernel.currentIndex p lane slice index) (VG.Proof.Argon2.AArch64.FillKernel.nextBlock s p pass lane slice index state.memory) =
      (fillBlock p pass slice lane index state).memory := by
  rw [Proof.Argon2.FillStep.memory p pass lane slice index state active]
  unfold VG.Proof.Argon2.AArch64.FillKernel.nextBlock VG.Proof.Argon2.AArch64.FillKernel.referenceIndex
  rw [random]
  rfl

theorem code_spec_ok (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : VG.Proof.Argon2.AArch64.FillKernel.Ready p pass lane slice index s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (VG.Proof.Argon2.AArch64.FillKernel.matrix s) p.blocks state.memory)
    (random : s.gpr .x0 = Proof.Argon2.FillStep.random p pass lane slice index state.memory) :
    WP isa Impl.Argon2.AArch64.FillKernel.code s fun t => VG.Proof.Argon2.AArch64.FillKernel.Done s t p pass lane slice index ∧
      Proof.Argon2.Represents t.mem (VG.Proof.Argon2.AArch64.FillKernel.matrix s) p.blocks (fillBlock p pass slice lane index state).memory := by
  refine (VG.Proof.Argon2.AArch64.FillKernel.code_ok s p pass lane slice index ready).mono ?_
  intro t done
  have represented' := done.represents ready state.memory represented
  rw [VG.Proof.Argon2.AArch64.FillKernel.update_spec s p pass lane slice index state ready.bounds.active random] at represented'
  exact ⟨done, represented'⟩

end VG.Proof.Argon2.AArch64.FillKernel

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.DependentWord`. -/
section

/-! Merged from `Proof.Argon2.AArch64.DependentWordPointer`. -/
section
/-! The data-dependent word's address is the specification's cyclic predecessor. -/

namespace VG.Proof.Argon2.AArch64.DependentWord

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.DependentWord

theorem args_ok (s : State) : WP isa (.block VG.Impl.Argon2.AArch64.DependentWord.args) s fun t =>
    t.gpr .x3 = s.gpr .x0 ∧ t.gpr .x8 = s.gpr .x24 ∧ Divide.Keeps [.x3, .x8] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.AArch64.DependentWord.args, Impl.Argon2.AArch64.Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 0 < 4096 from by decide, BitVec.setWidth_eq, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

theorem pointer_ok (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) : WP isa VG.Impl.Argon2.AArch64.DependentWord.pointer s fun t =>
      t.gpr .x8 = FillKernel.previous s p lane slice index ∧ Divide.Keeps ReferenceMap.changed s t := by
  unfold VG.Impl.Argon2.AArch64.DependentWord.pointer Impl.Argon2.AArch64.FillKernel.matrix
  refine WP.seq ((FillKernel.load_ok s .x4 232 (by decide) (by decide) (h.layout.frameRead 232 (by simp))).mono ?_)
  rintro a ⟨base, ka⟩
  have k : Divide.Keeps ReferenceMap.changed s a := ka.mono (by decide)
  have pos := h.position.of_keeps k
  have columnBound := Proof.Argon2.column_lt p h.bounds.lanesPositive h.bounds.sliceBound h.bounds.indexBound
  have segment := Proof.Argon2.segmentLen_ge_two p h.bounds.lanesPositive h.bounds.memoryMinimum
  have q := Proof.Argon2.laneLen_segments p h.bounds.lanesPositive
  refine WP.seq ((FillColumn.code_nat_ok a slice p.segmentLen index p.laneLen
    pos.slice pos.segmentLength pos.index pos.laneLength (by omega)
    (Nat.lt_trans h.bounds.laneLength_bound (by decide)) columnBound).mono ?_)
  rintro b ⟨_, prev, kb⟩
  refine WP.seq ((VG.Proof.Argon2.AArch64.DependentWord.args_ok b).mono ?_)
  rintro c ⟨col, laneReg, kc⟩
  have col' := col.trans prev
  have lane' : c.gpr .x8 = BitVec.ofNat 64 lane := laneReg.trans ((kb.regs .x24 (by decide)).trans pos.current)
  have length : c.gpr .x20 = BitVec.ofNat 64 p.laneLen :=
    (kc.regs .x20 (by decide)).trans ((kb.regs .x20 (by decide)).trans pos.laneLength)
  refine (BlockAddress.code_nat_ok c lane
    ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen) p.laneLen lane' col' length).mono ?_
  rintro t ⟨address, kt⟩
  refine ⟨?_, ((k.trans (kb.mono (by decide))).trans (kc.mono (by decide))).trans (kt.mono (by decide))⟩
  rw [address, kc.regs .x4 (by decide), kb.regs .x4 (by decide), base]
  rfl

end VG.Proof.Argon2.AArch64.DependentWord
end

/-! Select the specified secret random word from the public previous-cell address. -/

namespace VG.Proof.Argon2.AArch64.DependentWord

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.DependentWord

theorem read_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .x8) 8) :
    WP isa (.block Impl.Argon2.AArch64.DependentWord.read) s fun t => t.gpr .x0 = s.mem.readW (s.gpr .x8) 64 ∧ Divide.Keeps [.x0] s t := by
  simpa only [Impl.Argon2.AArch64.DependentWord.read,
    List.flatten_cons, List.flatten_nil, List.append_nil, BitVec.add_zero]
    using Instructions.load_ok s .x0 .x8 0 (by decide) (by decide)
      (by simpa only [BitVec.add_zero] using hr)

theorem code_ok (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) : WP isa VG.Impl.Argon2.AArch64.DependentWord.code s fun t =>
      t.gpr .x0 = (VG.Spec.Argon2.blockAt s.mem (FillKernel.previous s p lane slice index))[0] ∧
      Divide.Keeps ReferenceMap.changed s t := by
  unfold VG.Impl.Argon2.AArch64.DependentWord.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.DependentWord.pointer_ok s p pass lane slice index h).mono ?_)
  rintro a ⟨pointer, keeps⟩
  have bound := Proof.Argon2.previous_column_lt p h.bounds.lanesPositive h.bounds.memoryMinimum
    (slice * p.segmentLen + index)
  have cover := h.layout.cell_cover h.bounds.lanesPositive h.bounds.laneBound bound
  have hr : InRegions (a.rd ++ a.wr) (a.gpr .x8) 8 := by
    rw [keeps.rd, keeps.wr, pointer]
    have contains : (⟨FillKernel.previous s p lane slice index, 1024⟩ : Region).Contains
        (FillKernel.previous s p lane slice index) 8 :=
      by simpa only [BitVec.add_zero] using (Offset.contains_base
        (FillKernel.previous s p lane slice index) (d := 0) (n := 8) (k := 1024) (by decide) (by decide))
    obtain ⟨r, hr, hc⟩ := cover _ _ ⟨⟨FillKernel.previous s p lane slice index, 1024⟩,
      by simp [FillKernel.previous, FillKernel.previousColumn, FillKernel.currentColumn], contains⟩
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine (VG.Proof.Argon2.AArch64.DependentWord.read_ok a hr).mono ?_
  rintro t ⟨random, tail⟩
  refine ⟨?_, keeps.trans (tail.mono (by decide))⟩
  rw [random, pointer, keeps.mem]
  change s.mem.readW _ 64 = (VG.Spec.Argon2.blockAt _ _)[(⟨0, by decide⟩ : Fin 128)]
  rw [blockAt_get]
  change s.mem.readW _ 64 = s.mem.readW (_ + 0#64) 64
  rw [BitVec.add_zero]

theorem code_spec_ok (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (dependent : independent p pass slice = false) : WP isa VG.Impl.Argon2.AArch64.DependentWord.code s fun t =>
      t.gpr .x0 = Proof.Argon2.FillStep.random p pass lane slice index state.memory ∧
      Divide.Keeps ReferenceMap.changed s t := by
  refine (VG.Proof.Argon2.AArch64.DependentWord.code_ok s p pass lane slice index h).mono ?_
  rintro t ⟨random, keeps⟩
  have bound := Proof.Argon2.previous_cell_lt p h.bounds.lanesPositive h.bounds.memoryMinimum
    h.bounds.laneBound (column := FillKernel.currentColumn p slice index)
  have block := represented.block (FillKernel.previousIndex p lane slice index) bound
  change VG.Spec.Argon2.blockAt s.mem (FillKernel.previous s p lane slice index) = _ at block
  rw [block] at random
  refine ⟨?_, keeps⟩
  simpa only [Proof.Argon2.FillStep.random, dependent, Bool.false_eq_true, ite_false, FillKernel.previousIndex, FillKernel.previousColumn,
    FillKernel.currentColumn] using random

end VG.Proof.Argon2.AArch64.DependentWord

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.DeriveAbi`. -/
section

/-! Decode the reviewed ARM64 contract without requiring normalized upper bits. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def abiWord (s : State) (d : Nat) : Addr := s.mem.readW (s.sp + BitVec.ofNat 64 d) 64
def abiParams (s : State) : Spec.Argon2.Params := Spec.Argon2.params
  ((s.gpr .x0).setWidth 32).toNat ((s.gpr .x5).setWidth 32).toNat
  ((s.gpr .x6).setWidth 32).toNat ((s.gpr .x7).setWidth 32).toNat (VG.Proof.Argon2.AArch64.Derive.abiWord s 72).toNat

def abiInputs (s : State) : List Region :=
  [⟨s.gpr .x1, (s.gpr .x2).toNat⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat⟩,
    ⟨VG.Proof.Argon2.AArch64.Derive.abiWord s 8, (VG.Proof.Argon2.AArch64.Derive.abiWord s 16).toNat⟩, ⟨VG.Proof.Argon2.AArch64.Derive.abiWord s 24, (VG.Proof.Argon2.AArch64.Derive.abiWord s 32).toNat⟩]
def abiMatrix (s : State) : Region := ⟨VG.Proof.Argon2.AArch64.Derive.abiWord s 40, (VG.Proof.Argon2.AArch64.Derive.abiWord s 48).toNat * 1024⟩
def abiWork (s : State) : Region := ⟨VG.Proof.Argon2.AArch64.Derive.abiWord s 56, 16384⟩
def abiOutput (s : State) : Region := ⟨VG.Proof.Argon2.AArch64.Derive.abiWord s 64, (VG.Proof.Argon2.AArch64.Derive.abiWord s 72).toNat⟩
def abiArguments (s : State) : Region := ⟨s.sp, 80⟩
def abiBuffers (s : State) : List (Region × Bool) :=
  (VG.Proof.Argon2.AArch64.Derive.abiInputs s).map (·, false) ++ [(VG.Proof.Argon2.AArch64.Derive.abiMatrix s, true), (VG.Proof.Argon2.AArch64.Derive.abiWork s, true), (VG.Proof.Argon2.AArch64.Derive.abiOutput s, true)]

structure AbiEnvironment (s : State) : Prop where
  stack : 400 ≤ (s.sp).toNat
  wrap : (s.sp).toNat + 80 ≤ 2 ^ 64
  rd : s.rd = VG.Proof.Argon2.AArch64.Derive.abiInputs s ++ [VG.Proof.Argon2.AArch64.Derive.abiArguments s]
  wr : s.wr = [VG.Proof.Argon2.AArch64.Derive.abiMatrix s, VG.Proof.Argon2.AArch64.Derive.abiWork s, VG.Proof.Argon2.AArch64.Derive.abiOutput s]
  pairs : (VG.Proof.Argon2.AArch64.Derive.abiBuffers s ++ [(VG.Proof.Argon2.AArch64.Derive.abiArguments s, false)]).Pairwise
    (fun a b => (a.2 || b.2) → a.1.Disjoint b.1)
  reserved : ∀ r ∈ [below (s.sp) 400],
    ∀ b ∈ VG.Proof.Argon2.AArch64.Derive.abiBuffers s ++ [(VG.Proof.Argon2.AArch64.Derive.abiArguments s, false)], r.Disjoint b.1
  bounds : ∀ b ∈ VG.Proof.Argon2.AArch64.Derive.abiBuffers s, b.1.base.toNat + b.1.len ≤ 2 ^ 64
  kind : ((s.gpr .x0).setWidth 32).toNat ≤ 2
  valid : Spec.Argon2.valid (VG.Proof.Argon2.AArch64.Derive.abiParams s) (s.gpr .x2).toNat (s.gpr .x4).toNat
    (VG.Proof.Argon2.AArch64.Derive.abiWord s 16).toNat (VG.Proof.Argon2.AArch64.Derive.abiWord s 32).toNat
  threads : 1 ≤ ((VG.Proof.Argon2.AArch64.Derive.abiWord s 0).setWidth 32).toNat ∧ ((VG.Proof.Argon2.AArch64.Derive.abiWord s 0).setWidth 32).toNat < 2 ^ 24
  blocks : (VG.Proof.Argon2.AArch64.Derive.abiWord s 48).toNat = (VG.Proof.Argon2.AArch64.Derive.abiParams s).blocks

theorem abi_environment (s : State) (h : (Spec.Argon2.deriveContract AArch64.abi 400).pre s) :
    VG.Proof.Argon2.AArch64.Derive.AbiEnvironment s := by
  sig_pre [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, AArch64.abi,
    AArch64.argRegs, AArch64.firstNarrowStack, AArch64.stackArg, AArch64.stackArgAddr, List.range, List.range.loop] at h
  sig_split h
  all_goals simp only [BitVec.add_zero] at *
  constructor
  all_goals sig_eval [VG.Proof.Argon2.AArch64.Derive.abiInputs, VG.Proof.Argon2.AArch64.Derive.abiArguments, VG.Proof.Argon2.AArch64.Derive.abiMatrix, VG.Proof.Argon2.AArch64.Derive.abiWork, VG.Proof.Argon2.AArch64.Derive.abiOutput, VG.Proof.Argon2.AArch64.Derive.abiBuffers,
    VG.Proof.Argon2.AArch64.Derive.abiWord, VG.Proof.Argon2.AArch64.Derive.abiParams, below]
  all_goals try simp only [BitVec.add_zero]
  all_goals sig_and_intros
  all_goals sig_close
  all_goals with_reducible assumption

end VG.Proof.Argon2.AArch64.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.DeriveFrame`. -/
section

/-! Compose the saved-register frames and the 272-byte local allocation. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

def frameStart (s : State) : List Reg → State
  | [] => allocated 272 s
  | r :: rs => VG.Proof.Argon2.AArch64.Derive.frameStart (pushed r s) rs

def frameEnd (s : State) : List Reg → State
  | [] => freed 272 s
  | r :: rs => popped r (VG.Proof.Argon2.AArch64.Derive.frameEnd s rs)

theorem frameEnd_metadata (s t : State) (rs : List Reg)
    (sp : t.sp = (VG.Proof.Argon2.AArch64.Derive.frameStart s rs).sp)
    (wr : t.wr = (VG.Proof.Argon2.AArch64.Derive.frameStart s rs).wr) :
    (VG.Proof.Argon2.AArch64.Derive.frameEnd t rs).sp = s.sp ∧ (VG.Proof.Argon2.AArch64.Derive.frameEnd t rs).wr = s.wr := by
  induction rs generalizing s with
  | nil =>
    constructor
    · change t.sp + BitVec.ofNat 64 272 = s.sp
      rw [sp]; exact BitVec.sub_add_cancel _ _
    · change t.wr.tail = s.wr
      rw [wr]; rfl
  | cons r rs ih =>
    obtain ⟨innerSp, innerWr⟩ := ih (pushed r s) sp wr
    constructor
    · change (VG.Proof.Argon2.AArch64.Derive.frameEnd t rs).sp + 16 = s.sp
      rw [innerSp]; exact BitVec.sub_add_cancel _ _
    · change (VG.Proof.Argon2.AArch64.Derive.frameEnd t rs).wr.tail = s.wr
      rw [innerWr]; rfl

theorem frame_ok (s : State) (rs : List Reg) (body : Prog isa) (Q : State → Prop)
    (space : 272 + 16 * rs.length ≤ s.sp.toNat)
    (run : WP isa body (VG.Proof.Argon2.AArch64.Derive.frameStart s rs) fun t =>
      t.sp = (VG.Proof.Argon2.AArch64.Derive.frameStart s rs).sp ∧ t.wr = (VG.Proof.Argon2.AArch64.Derive.frameStart s rs).wr ∧ Q (VG.Proof.Argon2.AArch64.Derive.frameEnd t rs)) :
    WP isa (Impl.Argon2.AArch64.Derive.frame body rs) s Q := by
  induction rs generalizing s Q with
  | nil =>
    exact WP.alloc (by decide) (by simpa using space) (run.mono fun _ h => h.2.2)
  | cons r rs ih =>
    have pushedBound : (pushed r s).sp.toNat = s.sp.toNat - 16 := by
      change (s.sp - 16).toNat = s.sp.toNat - 16
      rw [BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def]
        change 16 ≤ s.sp.toNat
        simp only [List.length_cons] at space; omega)]
      rfl
    have innerSpace : 272 + 16 * rs.length ≤ (pushed r s).sp.toNat := by
      rw [pushedBound]; simp only [List.length_cons] at space; omega
    apply WP.frame (by simp only [List.length_cons] at space; omega)
    apply ih (pushed r s) (fun t => Q (popped r t)) innerSpace
    apply run.mono
    rintro t ⟨sp, wr, result⟩
    exact ⟨sp, wr, result⟩
end VG.Proof.Argon2.AArch64.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.Parameters`. -/
section

/-! Merged from `Proof.Argon2.AArch64.ParametersSteps`. -/
section
/-! Public frame loads and fixed arithmetic for the RFC's rounded memory dimensions. -/

namespace VG.Proof.Argon2.AArch64.Parameters

open VG VG.AArch64

theorem args_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 176) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 184) 8) :
    WP isa (.block Impl.Argon2.AArch64.Parameters.args) s fun t =>
      t.gpr .x0 = s.mem.readW (off (s.gpr .x19) 176) 64 ∧
      t.gpr .x1 = (s.mem.readW (off (s.gpr .x19) 184) 64) * 4 ∧ Divide.Keeps [.x0, .x1, .x15] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.Parameters.args,
    Impl.Argon2.AArch64.Instructions.load, Impl.Argon2.AArch64.Instructions.add,
    Impl.Argon2.AArch64.Instructions.mark, Impl.Argon2.AArch64.Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.load, State.read,
    addr, Size.bytes, Size.bits, show 0 < 4096 from by decide,
    show 176 % 8 = 0 ∧ 176 < 4096 * 8 from by decide,
    show 184 % 8 = 0 ∧ 184 < 4096 * 8 from by decide, and_self,
    memoryRead, lanesRead, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, ?_⟩
  · simp only [show (4 : Addr) = 2#64 + 2#64 from rfl, BitVec.mul_add, BitVec.mul_two]
    rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
    all_goals rfl

theorem finish_ok (s : State) : WP isa (.block Impl.Argon2.AArch64.Parameters.finish) s fun t =>
    t.gpr .x21 = s.gpr .x5 * 4 ∧ Divide.Keeps [.x21, .x15] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.Parameters.finish,
    Impl.Argon2.AArch64.Instructions.mov, Impl.Argon2.AArch64.Instructions.add,
    Impl.Argon2.AArch64.Instructions.mark, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, Size.bits, show 0 < 4096 from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · simp only [show (4 : Addr) = 2#64 + 2#64 from rfl, BitVec.mul_add, BitVec.mul_two]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
    all_goals rfl

end VG.Proof.Argon2.AArch64.Parameters
end

/-! Exact rounded lane length using the verified fixed-time divider. -/

namespace VG.Proof.Argon2.AArch64.Parameters

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : VG.Spec.Argon2.Params) (s : State) : Prop where
  memoryRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 176) 8
  lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 184) 8
  memoryWord : s.mem.readW (off (s.gpr .x19) 176) 64 = BitVec.ofNat 64 p.memory
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes
  positive : 0 < p.lanes
  memoryBound : p.memory < 2 ^ 32
  lanesBound : p.lanes < 2 ^ 24

def changed : List Reg := [.x0, .x1, .x15] ++ Divide.changed ++ [.x21, .x15]

theorem code_ok (s : State) (p : VG.Spec.Argon2.Params) (h : VG.Proof.Argon2.AArch64.Parameters.Ready p s) :
    WP isa Impl.Argon2.AArch64.Parameters.code s fun t =>
      t.gpr .x21 = BitVec.ofNat 64 p.laneLen ∧ Divide.Keeps VG.Proof.Argon2.AArch64.Parameters.changed s t := by
  unfold Impl.Argon2.AArch64.Parameters.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.Parameters.args_ok s h.memoryRead h.lanesRead).mono ?_)
  rintro a ⟨memory, lanes, ka⟩
  have divisor : a.gpr .x1 = BitVec.ofNat 64 (4 * p.lanes) := by
    rw [lanes, h.lanesWord, show (4 : Addr) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_mul, Nat.mul_comm]
  have n : (a.gpr .x0).toNat = p.memory := by
    rw [memory, h.memoryWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.memoryBound (by decide))]
  have bound : 4 * p.lanes < 2 ^ 32 := by have lanesBound := h.lanesBound; omega
  have d : (a.gpr .x1).toNat = 4 * p.lanes := by
    rw [divisor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans bound (by decide))]
  refine WP.seq ((Divide.code_ok a (by rw [n]; exact h.memoryBound)
    (by rw [d]; have positive := h.positive; omega) (by rw [d]; exact bound)).mono ?_)
  rintro b ⟨quotient, _, kb⟩
  rw [n, d] at quotient
  have word : b.gpr .x5 = BitVec.ofNat 64 (p.memory / (4 * p.lanes)) := by
    rw [← quotient]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine (VG.Proof.Argon2.AArch64.Parameters.finish_ok b).mono ?_
  rintro t ⟨value, kt⟩
  refine ⟨?_, (ka.mono (by simp [VG.Proof.Argon2.AArch64.Parameters.changed])).trans
    ((kb.mono (by
      intro r hr
      simp only [VG.Proof.Argon2.AArch64.Parameters.changed, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inl (Or.inr hr))).trans (kt.mono (by simp [VG.Proof.Argon2.AArch64.Parameters.changed])))⟩
  rw [value, word, show (4 : Addr) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_mul,
    Nat.mul_comm, ← Proof.Argon2.laneLen_eq p h.positive]

end VG.Proof.Argon2.AArch64.Parameters

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.DeriveSaved`. -/
section

/-! Merged from `Proof.Argon2.AArch64.DeriveFrameState`. -/
section
/-! Exact stack depth and memory modified by the entry-point prologue. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

theorem frameStart_sp (s : State) (rs : List Reg) :
    (VG.Proof.Argon2.AArch64.Derive.frameStart s rs).sp = s.sp - BitVec.ofNat 64 (272 + 16 * rs.length) := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    rw [VG.Proof.Argon2.AArch64.Derive.frameStart, ih]
    change s.sp - 16 - BitVec.ofNat 64 (272 + 16 * rs.length) = _
    rw [BitVec.sub_sub, show (16 : Addr) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]
    exact congrArg (fun n => s.sp - BitVec.ofNat 64 n) (by simp only [List.length_cons]; omega)

theorem frameStart_reg (s : State) (rs : List Reg) (r : Reg) :
    (VG.Proof.Argon2.AArch64.Derive.frameStart s rs).gpr r = s.gpr r := by
  induction rs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (pushed x s)

theorem frameStart_rd (s : State) (rs : List Reg) : (VG.Proof.Argon2.AArch64.Derive.frameStart s rs).rd = s.rd := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => exact ih (pushed r s)

theorem frameStart_frame (s : State) (rs : List Reg)
    (space : 272 + 16 * rs.length ≤ s.sp.toNat) :
    Frame [below s.sp (272 + 16 * rs.length)] s.mem (VG.Proof.Argon2.AArch64.Derive.frameStart s rs).mem := by
  induction rs generalizing s with
  | nil => exact Frame.refl _ _
  | cons r rs ih =>
    have enough : 16 ≤ s.sp.toNat := by simp only [List.length_cons] at space; omega
    have innerSpace : 272 + 16 * rs.length ≤ (pushed r s).sp.toNat := by
      change 272 + 16 * rs.length ≤ (s.sp - 16).toNat
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact enough)]
      change 272 + 16 * rs.length ≤ s.sp.toNat - 16
      simp only [List.length_cons] at space; omega
    have outer : Frame [below s.sp 16] s.mem (pushed r s).mem := by
      change Frame [⟨s.sp - 16, 16⟩] s.mem (s.mem.writeW (s.sp - 16) (s.gpr r))
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (by simpa only [BitVec.add_zero] using
          Offset.contains_base (s.sp - 16) (d := 0) (n := 8) (k := 16) (by decide) (by decide))
    have inner := ih (pushed r s) innerSpace
    apply (outer.sub ?_).trans (inner.sub ?_)
    · intro region hr
      simp only [List.mem_singleton] at hr; subst region
      exact ⟨_, List.mem_singleton_self _, below_sub (by simp only [List.length_cons]; omega) (by
        have := s.sp.isLt; omega)⟩
    · intro region hr
      simp only [List.mem_singleton] at hr; subst region
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      change Region.Sub ⟨s.sp - 16 - BitVec.ofNat 64 (272 + 16 * rs.length), 272 + 16 * rs.length⟩
        (below s.sp (272 + 16 * (r :: rs).length))
      simp only [List.length_cons, below]
      rw [BitVec.sub_sub, show (16 : Addr) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add,
        show 16 + (272 + 16 * rs.length) = 272 + 16 * (rs.length + 1) by omega]
      exact Region.sub_prefix (by omega)

theorem frameEnd_mem (s : State) (rs : List Reg) : (VG.Proof.Argon2.AArch64.Derive.frameEnd s rs).mem = s.mem := by
  induction rs with
  | nil => rfl
  | cons r rs ih => exact ih

theorem frameEnd_rd (s : State) (rs : List Reg) : (VG.Proof.Argon2.AArch64.Derive.frameEnd s rs).rd = s.rd := by
  induction rs with
  | nil => rfl
  | cons r rs ih => exact ih
end VG.Proof.Argon2.AArch64.Derive
end

/-! Each saved register occupies the low eight bytes of its 16-byte slot. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

theorem frameStart_word (s : State) (rs : List Reg)
    (space : 272 + 16 * rs.length ≤ s.sp.toNat) (j : Nat) (bound : j < rs.length) :
    (VG.Proof.Argon2.AArch64.Derive.frameStart s rs).mem.readW (s.sp - BitVec.ofNat 64 (16 * (j + 1))) 64 = s.gpr rs[j] := by
  induction rs generalizing s j with
  | nil => exact absurd bound (Nat.not_lt_zero _)
  | cons r rs ih =>
    have enough : 16 ≤ s.sp.toNat := by simp only [List.length_cons] at space; omega
    have innerSpace : 272 + 16 * rs.length ≤ (pushed r s).sp.toNat := by
      change 272 + 16 * rs.length ≤ (s.sp - 16).toNat
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact enough)]
      change 272 + 16 * rs.length ≤ s.sp.toNat - 16
      simp only [List.length_cons] at space; omega
    cases j with
    | zero =>
      have inner := VG.Proof.Argon2.AArch64.Derive.frameStart_frame (pushed r s) rs innerSpace
      have unchanged : (VG.Proof.Argon2.AArch64.Derive.frameStart (pushed r s) rs).mem.readW (pushed r s).sp 64 =
          (pushed r s).mem.readW (pushed r s).sp 64 := inner.readW
        (r := ⟨(pushed r s).sp, 8⟩) (Region.contains_self _ _) (by
          intro region hr
          simp only [List.mem_singleton] at hr; subst region
          apply Offset.base_disjoint_below
          have limit := s.sp.isLt
          simp only [List.length_cons] at space; omega) (by decide)
      change (VG.Proof.Argon2.AArch64.Derive.frameStart (pushed r s) rs).mem.readW (s.sp - 16) 64 = s.gpr r
      change (VG.Proof.Argon2.AArch64.Derive.frameStart (pushed r s) rs).mem.readW (s.sp - 16) 64 =
        (pushed r s).mem.readW (s.sp - 16) 64 at unchanged
      rw [unchanged]
      exact Mem.readW_writeW_self64 ..
    | succ j =>
      have jBound : j < rs.length := by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using bound
      have word := ih (pushed r s) innerSpace j (by simpa using bound)
      change (VG.Proof.Argon2.AArch64.Derive.frameStart (pushed r s) rs).mem.readW
        (s.sp - 16 - BitVec.ofNat 64 (16 * (j + 1))) 64 = s.gpr rs[j] at word
      rw [BitVec.sub_sub, show (16 : Addr) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add,
        show 16 + 16 * (j + 1) = 16 * (j + 1 + 1) by omega] at word
      exact word
end VG.Proof.Argon2.AArch64.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.InitialArgs`. -/
section

/-! Argument handling for the H₀ streaming hash. -/
namespace VG.Proof.Argon2.AArch64.Initial
open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial

theorem headerWord_ok (s : State) (source destination : Nat)
    (sourceAlign : source % 8 = 0) (sourceBound : source < 32768)
    (destinationAlign : destination % 4 = 0) (destinationBound : destination < 16384)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 source) 8)
    (hw : InRegions s.wr (s.gpr .x24 + BitVec.ofNat 64 destination) 4) :
    WP isa (.block (headerWord source destination)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .x24 + BitVec.ofNat 64 destination)
        ((s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 source) 64).setWidth 32) ∧
      (∀ r, r ≠ .x8 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [headerWord, Impl.Argon2.AArch64.Instructions.load,
    Impl.Argon2.AArch64.Instructions.store32, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, State.load, State.store, addr, Size.bytes, Size.bits,
    sourceAlign, sourceBound, destinationAlign, destinationBound, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hr, hw, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, trivial, trivial, rfl⟩
  intro r hr
  simp only [hr, ite_false]

structure LengthArgs (s : State) (offset : Nat) (t : State) : Prop where
  length : t.gpr .x22 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 offset) 64
  count : t.gpr .x1 = s.gpr .x20
  pointer : t.gpr .x2 = s.gpr .x24 + 792
  size : t.gpr .x3 = 4
  other : ∀ r, r ∉ [Reg.x22, .x1, .x2, .x3, .x15] → t.gpr r = s.gpr r
  mem : t.mem = s.mem.writeW (s.gpr .x24 + 792)
    ((s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 offset) 64).setWidth 32)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem lengthArgs_ok (s : State) (offset : Nat)
    (aligned : offset % 8 = 0) (bound : offset < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 offset) 8)
    (hw : InRegions s.wr (s.gpr .x24 + 792) 4) :
    WP isa (.block (lengthArgs offset)) s (VG.Proof.Argon2.AArch64.Initial.LengthArgs s offset) := by
  have hwLiteral : InRegions s.wr (s.gpr .x24 + 792#64) 4 := hw
  apply WP.of_runBlock
  simp only [lengthArgs, Impl.Argon2.AArch64.Instructions.load,
    Impl.Argon2.AArch64.Instructions.store32, Impl.Argon2.AArch64.Instructions.mov,
    Impl.Argon2.AArch64.Instructions.addi, Impl.Argon2.AArch64.Instructions.mark,
    Impl.Argon2.AArch64.Instructions.imm, show 4 < 65536 from by decide,
    show 792 < 4096 from by decide, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, State.load, State.store, addr, Size.bytes, Size.bits,
    aligned, bound, show 792 % 4 = 0 ∧ 792 < 4096 * 4 from by decide, and_self,
    show 0 < 4096 from by decide, Nat.reduceMul, Nat.reduceLT,
    BitVec.shiftLeft_zero, show (4#16).setWidth 64 = 4#64 from rfl,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hr, hwLiteral, BitVec.setWidth_eq, BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  constructor
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, ite_true]; rfl
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  · simp only [RegUpd.mem_write]; rfl
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

structure InputArgs (s t : State) (offset : Nat) : Prop where
  total : t.gpr .x20 = s.gpr .x20 + 4
  count : t.gpr .x1 = s.gpr .x20 + 4
  pointer : t.gpr .x2 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 offset) 64
  length : t.gpr .x3 = s.gpr .x22
  other : ∀ r, r ∉ [Reg.x20, .x1, .x2, .x3, .x15] → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem inputArgs_ok (s : State) (offset : Nat)
    (aligned : offset % 8 = 0) (bound : offset < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 offset) 8) :
    WP isa (.block (inputArgs offset)) s (fun t => VG.Proof.Argon2.AArch64.Initial.InputArgs s t offset) := by
  apply WP.of_runBlock
  simp only [inputArgs, Impl.Argon2.AArch64.Instructions.addi,
    Impl.Argon2.AArch64.Instructions.mark, Impl.Argon2.AArch64.Instructions.mov,
    Impl.Argon2.AArch64.Instructions.load, show 4 < 4096 from by decide,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.load,
    addr, Size.bytes, Size.bits, aligned, bound, and_self,
    show 0 < 4096 from by decide, RegUpd.gpr_write,
    RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hr,
    BitVec.setWidth_eq, BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  constructor
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, ite_true, BitVec.setWidth_eq]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]
end VG.Proof.Argon2.AArch64.Initial

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.DeriveRegions`. -/
section

/-! Merged from `Proof.Argon2.AArch64.DeriveNormalize`. -/
section
/-! Normalize u32 stack arguments without assuming anything about their upper bits. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64
open VG.Impl.Argon2.AArch64.Derive

structure Normalized (s t : State) (d : Nat) : Prop where
  mem : t.mem = s.mem.writeW (s.gpr .x19 + BitVec.ofNat 64 d)
    (((s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64)
  regs : ∀ r, r ≠ .x8 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem normalize_ok (s : State) (d : Nat)
    (aligned : d % 8 = 0) (bound : d < 32768)
    (read : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 d) 8)
    (write : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 8) :
    WP isa (.block (normalize d)) s (VG.Proof.Argon2.AArch64.Derive.Normalized s · d) := by
  apply WP.of_runBlock
  simp only [normalize, Impl.Argon2.AArch64.Instructions.load,
    Impl.Argon2.AArch64.Instructions.mov32, Impl.Argon2.AArch64.Instructions.store,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, State.load, State.store, addr, Size.bytes, Size.bits,
    aligned, bound, and_self, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, read, write, BitVec.setWidth_eq,
    BitVec.or_self, reduceCtorEq, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  intro r hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem Normalized.word {s t : State} {d : Nat} (h : VG.Proof.Argon2.AArch64.Derive.Normalized s t d) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 =
      (((s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64) := by
  rw [h.regs .x19 (by decide), h.mem, Mem.readW_writeW_self64]

theorem Normalized.frame {s t : State} {d : Nat} (h : VG.Proof.Argon2.AArch64.Derive.Normalized s t d) :
    Frame [⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem Normalized.other_word {s t : State} {d : Nat} (h : VG.Proof.Argon2.AArch64.Derive.Normalized s t d)
    (e : Nat) (separate : e + 8 ≤ d ∨ d + 8 ≤ e) (ed : e + 8 < 2 ^ 64) (dd : d + 8 < 2 ^ 64) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 e) 64 := by
  rw [h.regs .x19 (by decide), h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ separate (Nat.le_of_lt ed) (Nat.le_of_lt dd)) (by decide)

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveStore`. -/
section
/-! Save each incoming argument with one short symbolic execution. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

structure Stored (s t : State) (d : Nat) (r : Reg) : Prop where
  mem : t.mem = s.mem.writeW (s.gpr .x19 + BitVec.ofNat 64 d) (s.gpr r)
  regs : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem store_ok (s : State) (d : Nat) (r : Reg)
    (aligned : d % 8 = 0) (bound : d < 32768)
    (write : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 8) :
    WP isa (.block [.str .x r .x19 d]) s (VG.Proof.Argon2.AArch64.Derive.Stored s · d r) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.store,
    addr, Size.bytes, Size.bits, aligned, bound, and_self, write,
    BitVec.setWidth_eq, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Stored.word {s t : State} {d : Nat} {r : Reg} (h : VG.Proof.Argon2.AArch64.Derive.Stored s t d r) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 = s.gpr r := by
  rw [h.regs, h.mem, Mem.readW_writeW_self64]

theorem Stored.frame {s t : State} {d : Nat} {r : Reg} (h : VG.Proof.Argon2.AArch64.Derive.Stored s t d r) :
    Frame [⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem Stored.other_word {s t : State} {d : Nat} {r : Reg} (h : VG.Proof.Argon2.AArch64.Derive.Stored s t d r)
    (e : Nat) (separate : e + 8 ≤ d ∨ d + 8 ≤ e) (ed : e + 8 ≤ 2 ^ 64) (dd : d + 8 ≤ 2 ^ 64) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 e) 64 := by
  rw [h.regs, h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ separate ed dd) (by decide)

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveStores`. -/
section
/-! Compose argument stores without re-executing a growing symbolic memory state. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def saveMemory (s : State) (args : List (Nat × Reg)) : Mem :=
  args.foldl (fun m arg => m.writeW (s.gpr .x19 + BitVec.ofNat 64 arg.1) (s.gpr arg.2)) s.mem

structure Saved (s t : State) (args : List (Nat × Reg)) : Prop where
  mem : t.mem = VG.Proof.Argon2.AArch64.Derive.saveMemory s args
  regs : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (args.map fun arg => (⟨s.gpr .x19 + BitVec.ofNat 64 arg.1, 8⟩ : Region)) s.mem t.mem

theorem stores_ok (args : List (Nat × Reg)) (s : State)
    (encoding : ∀ arg ∈ args, arg.1 % 8 = 0 ∧ arg.1 < 32768)
    (write : ∀ arg ∈ args, InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 arg.1) 8) :
    WP isa (.block (args.map fun arg => .str .x arg.2 .x19 arg.1)) s (VG.Proof.Argon2.AArch64.Derive.Saved s · args) := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | cons arg args ih =>
    rw [List.map_cons]
    change WP isa (.block (([.str .x arg.2 .x19 arg.1] : List Instr) ++ _)) s _
    rw [WP.block_append_iff]
    refine (VG.Proof.Argon2.AArch64.Derive.store_ok s arg.1 arg.2 (encoding arg (List.mem_cons_self ..)).1
      (encoding arg (List.mem_cons_self ..)).2 (write arg (List.mem_cons_self ..))).mono ?_
    intro t ht
    refine (ih t (fun a ha => encoding a (List.mem_cons_of_mem arg ha)) (fun a ha => by rw [ht.wr, ht.regs]; exact write a (List.mem_cons_of_mem arg ha))).mono ?_
    intro u hu
    refine ⟨?_, hu.regs.trans ht.regs, hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.sp.trans ht.sp, ?_⟩
    · rw [hu.mem]
      unfold VG.Proof.Argon2.AArch64.Derive.saveMemory
      rw [ht.regs, ht.mem, List.foldl_cons]
    · apply (ht.frame.mono ?_).trans
      · have frame := hu.frame
        rw [ht.regs] at frame
        exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)
      · intro region hr
        simp only [List.mem_singleton] at hr; subst region
        exact List.mem_cons_self ..

theorem Saved.other_word {s t : State} {args : List (Nat × Reg)} (h : VG.Proof.Argon2.AArch64.Derive.Saved s t args)
    (e : Nat) (bound : e + 8 ≤ 2 ^ 64)
    (separate : ∀ arg ∈ args, e + 8 ≤ arg.1 ∨ arg.1 + 8 ≤ e)
    (bounds : ∀ arg ∈ args, arg.1 + 8 ≤ 2 ^ 64) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 e) 64 := by
  rw [h.regs]
  apply h.frame.readW (r := ⟨s.gpr .x19 + BitVec.ofNat 64 e, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  obtain ⟨arg, member, rfl⟩ := List.mem_map.mp hr
  exact Offset.disjoint _ (separate arg member) bound (bounds arg member)

theorem stores_values_ok (args : List (Nat × Reg)) (s : State)
    (encoding : ∀ arg ∈ args, arg.1 % 8 = 0 ∧ arg.1 < 32768)
    (write : ∀ arg ∈ args, InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 arg.1) 8)
    (separate : args.Pairwise fun a b => a.1 + 8 ≤ b.1 ∨ b.1 + 8 ≤ a.1)
    (bounds : ∀ arg ∈ args, arg.1 + 8 ≤ 2 ^ 64) :
    WP isa (.block (args.map fun arg => .str .x arg.2 .x19 arg.1)) s fun t =>
      VG.Proof.Argon2.AArch64.Derive.Saved s t args ∧ ∀ arg ∈ args, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 arg.1) 64 = s.gpr arg.2 := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩, by simp⟩
  | cons arg args ih =>
    obtain ⟨headSep, tailSep⟩ := List.pairwise_cons.mp separate
    rw [List.map_cons]
    change WP isa (.block (([.str .x arg.2 .x19 arg.1] : List Instr) ++ _)) s _
    rw [WP.block_append_iff]
    refine (VG.Proof.Argon2.AArch64.Derive.store_ok s arg.1 arg.2 (encoding arg (List.mem_cons_self ..)).1
      (encoding arg (List.mem_cons_self ..)).2 (write arg (List.mem_cons_self ..))).mono ?_
    intro t ht
    refine (ih t (fun a ha => encoding a (List.mem_cons_of_mem arg ha)) (fun a ha => by rw [ht.wr, ht.regs]; exact write a (List.mem_cons_of_mem arg ha))
      tailSep (fun a ha => bounds a (List.mem_cons_of_mem arg ha))).mono ?_
    rintro u ⟨hu, values⟩
    have saved : VG.Proof.Argon2.AArch64.Derive.Saved s u (arg :: args) := by
      refine ⟨?_, hu.regs.trans ht.regs, hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.sp.trans ht.sp, ?_⟩
      · rw [hu.mem]; unfold VG.Proof.Argon2.AArch64.Derive.saveMemory; rw [ht.regs, ht.mem, List.foldl_cons]
      · apply (ht.frame.mono ?_).trans
        · have frame := hu.frame
          rw [ht.regs] at frame
          exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)
        · intro region hr
          simp only [List.mem_singleton] at hr; subst region
          exact List.mem_cons_self ..
    refine ⟨saved, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [hu.other_word a.1 (bounds a (List.mem_cons_self ..)) headSep
        (fun b hb => bounds b (List.mem_cons_of_mem a hb))]
      exact ht.word
    · rw [values a ha, ht.regs]

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveSetup`. -/
section
/-! Merged from `Proof.Argon2.AArch64.DeriveScratch`. -/
section
/-! Load the caller-supplied hash workspace after saving incoming arguments. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

structure ScratchLoaded (s t : State) : Prop where
  scratch : t.gpr .x24 = s.mem.readW (s.gpr .x19 + 248) 64
  regs : ∀ r, r ≠ .x24 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem scratch_ok (s : State) (read : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 248) 8) :
    WP isa (.block [.ldr .x .x24 .x19 248]) s (VG.Proof.Argon2.AArch64.Derive.ScratchLoaded s) := by
  refine (Instructions.load_ok s .x24 .x19 248 (by decide) (by decide) read).mono ?_
  rintro t ⟨value, kept⟩
  refine ⟨value, ?_, kept.mem, kept.rd, kept.wr, kept.sp⟩
  intro r hr
  exact kept.regs r (by simpa only [List.mem_singleton] using hr)

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveEntry`. -/
section
/-! Normalize the four register-passed u32 parameters. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

structure Entered (s t : State) : Prop where
  values : ∀ r ∈ [Reg.x0, .x5, .x6, .x7], t.gpr r = ((s.gpr r).setWidth 32).setWidth 64
  regs : ∀ r, r ∉ [Reg.x0, .x5, .x6, .x7] → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem entry_ok (s : State) :
    WP isa (.block (([.x0, .x5, .x6, .x7] : List Reg).flatMap
      (fun r => Impl.Argon2.AArch64.Instructions.mov32 r r))) s (VG.Proof.Argon2.AArch64.Derive.Entered s) := by
  apply WP.of_runBlock
  simp only [List.flatMap_cons, List.flatMap_nil, Impl.Argon2.AArch64.Instructions.mov32,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, BitVec.or_self, RegUpd.gpr_write,
    reduceCtorEq, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> rfl
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
end VG.Proof.Argon2.AArch64.Derive
end

/-! Save the register arguments into the local derivation frame. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def arguments : List (Nat × Reg) :=
  [(72, .x5), (80, .x4), (88, .x3), (96, .x2), (104, .x1), (112, .x0), (176, .x6), (184, .x7)]

def argumentValue (s : State) (r : Reg) : Addr :=
  if r ∈ [Reg.x0, .x5, .x6, .x7] then ((s.gpr r).setWidth 32).setWidth 64 else s.gpr r

theorem Entered.argument {s t : State} (h : VG.Proof.Argon2.AArch64.Derive.Entered s t) (r : Reg) :
    t.gpr r = VG.Proof.Argon2.AArch64.Derive.argumentValue s r := by
  unfold VG.Proof.Argon2.AArch64.Derive.argumentValue
  split
  · next hr => exact h.values r hr
  · next hr => exact h.regs r hr

structure SetupDone (s t : State) : Prop where
  bp : t.gpr .x19 = s.gpr .x19
  sp : t.sp = s.sp
  scratch : t.gpr .x24 = s.mem.readW (s.gpr .x19 + 248) 64
  values : ∀ arg ∈ VG.Proof.Argon2.AArch64.Derive.arguments, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 arg.1) 64 = VG.Proof.Argon2.AArch64.Derive.argumentValue s arg.2
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x19 → r ≠ .x24 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .x19, 192⟩] s.mem t.mem

theorem setup_ok (s : State) (frameWrite : Covers [⟨s.gpr .x19, 192⟩] s.wr)
    (read : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 248) 8) :
    WP isa (.block Impl.Argon2.AArch64.Derive.setup) s (VG.Proof.Argon2.AArch64.Derive.SetupDone s) := by
  change WP isa (.block ((([.x0, .x5, .x6, .x7] : List Reg).flatMap
    (fun r => Impl.Argon2.AArch64.Instructions.mov32 r r)) ++
    (arguments.map fun arg => .str .x arg.2 .x19 arg.1) ++
    ([.ldr .x .x24 .x19 248] : List Instr))) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine (VG.Proof.Argon2.AArch64.Derive.entry_ok s).mono ?_
  intro a entered
  rw [WP.block_append_iff]
  have write : ∀ arg ∈ VG.Proof.Argon2.AArch64.Derive.arguments, InRegions a.wr (a.gpr .x19 + BitVec.ofNat 64 arg.1) 8 := by
    intro arg ha
    rw [entered.wr, entered.regs .x19 (by decide)]
    apply frameWrite
    have bounds : ∀ arg ∈ VG.Proof.Argon2.AArch64.Derive.arguments, arg.1 + 8 ≤ 192 := by decide
    exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (bounds arg ha) (by have := bounds arg ha; omega)⟩
  refine (VG.Proof.Argon2.AArch64.Derive.stores_values_ok VG.Proof.Argon2.AArch64.Derive.arguments a (by decide) write (by decide) (by decide)).mono ?_
  rintro b ⟨saved, values⟩
  have bp : b.gpr .x19 = s.gpr .x19 := by rw [saved.regs, entered.regs .x19 (by decide)]
  have scratchWord : b.mem.readW (b.gpr .x19 + 248) 64 = s.mem.readW (s.gpr .x19 + 248) 64 := by
    have kept := saved.other_word 248 (by decide) (by decide) (by decide)
    change b.mem.readW (b.gpr .x19 + 248) 64 = a.mem.readW (a.gpr .x19 + 248) 64 at kept
    rw [kept, entered.regs .x19 (by decide), entered.mem]
  refine (VG.Proof.Argon2.AArch64.Derive.scratch_ok b (by rw [saved.rd, saved.wr, bp, entered.rd, entered.wr]; exact read)).mono ?_
  intro t loaded
  refine ⟨(loaded.regs .x19 (by decide)).trans bp, ?_, loaded.scratch.trans scratchWord, ?_, ?_,
    loaded.rd.trans (saved.rd.trans entered.rd), loaded.wr.trans (saved.wr.trans entered.wr),
    ?_⟩
  · exact loaded.sp.trans (saved.sp.trans entered.sp)
  · intro arg ha
    rw [loaded.mem, loaded.regs .x19 (by decide), values arg ha]
    exact entered.argument arg.2
  · intro r hr hb hx
    have other : ∀ r ∈ FillCompress.loopRegs, r ∉ [Reg.x0, .x5, .x6, .x7] := by decide
    rw [loaded.regs r hx, saved.regs]
    exact entered.regs r (other r hr)
  · rw [loaded.mem, ← entered.mem]
    have frame := saved.frame
    rw [entered.regs .x19 (by decide)] at frame
    apply frame.sub
    intro region hr
    obtain ⟨arg, ha, rfl⟩ := List.mem_map.mp hr
    have bounds : ∀ arg ∈ VG.Proof.Argon2.AArch64.Derive.arguments, arg.1 + 8 ≤ 192 := by decide
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (bounds arg ha)⟩

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DerivePrologue`. -/
section
/-! Merged from `Proof.Argon2.AArch64.DerivePrivatePrepare`. -/
section
/-! Merged from `Proof.Argon2.AArch64.DerivePrepare`. -/
section
/-! Merged from `Proof.Argon2.AArch64.DeriveNormalizeArgs`. -/
section
/-! Normalize distinct stack slots while retaining every other frame word. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def normalizedWord (s : State) (d : Nat) : Addr :=
  (((s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64)

structure NormalizedArgs (s t : State) (ds : List Nat) : Prop where
  values : ∀ d ∈ ds, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 = VG.Proof.Argon2.AArch64.Derive.normalizedWord s d
  regs : ∀ r, r ≠ .x8 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (ds.map fun d => (⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩ : Region)) s.mem t.mem

theorem NormalizedArgs.other_word {s t : State} {ds : List Nat} (h : VG.Proof.Argon2.AArch64.Derive.NormalizedArgs s t ds)
    (e : Nat) (bound : e + 8 < 2 ^ 64)
    (separate : ∀ d ∈ ds, e + 8 ≤ d ∨ d + 8 ≤ e)
    (bounds : ∀ d ∈ ds, d + 8 < 2 ^ 64) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 e) 64 := by
  rw [h.regs .x19 (by decide)]
  apply h.frame.readW (r := ⟨s.gpr .x19 + BitVec.ofNat 64 e, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
  exact Offset.disjoint _ (separate d hd) (Nat.le_of_lt bound) (Nat.le_of_lt (bounds d hd))

theorem normalizeArgs_ok (ds : List Nat) (s : State)
    (encoding : ∀ d ∈ ds, d % 8 = 0 ∧ d < 32768)
    (read : ∀ d ∈ ds, InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 d) 8)
    (write : ∀ d ∈ ds, InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 8)
    (separate : ds.Pairwise fun d e => d + 8 ≤ e ∨ e + 8 ≤ d)
    (bounds : ∀ d ∈ ds, d + 8 < 2 ^ 64) :
    WP isa (Impl.Argon2.AArch64.Derive.normalizeArgs ds) s (VG.Proof.Argon2.AArch64.Derive.NormalizedArgs s · ds) := by
  induction ds generalizing s with
  | nil => exact WP.block_nil ⟨by simp, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | cons d ds ih =>
    cases ds with
    | nil =>
      refine (VG.Proof.Argon2.AArch64.Derive.normalize_ok s d (encoding d (by simp)).1 (encoding d (by simp)).2 (read d (by simp)) (write d (by simp))).mono ?_
      intro t ht
      exact ⟨fun e he => by simp only [List.mem_singleton] at he; subst e; exact ht.word,
        ht.regs, ht.rd, ht.wr, ht.sp, ht.frame⟩
    | cons e ds =>
      obtain ⟨headSep, tailSep⟩ := List.pairwise_cons.mp separate
      refine WP.seq ((VG.Proof.Argon2.AArch64.Derive.normalize_ok s d (encoding d (List.mem_cons_self ..)).1
        (encoding d (List.mem_cons_self ..)).2 (read d (List.mem_cons_self ..))
        (write d (List.mem_cons_self ..))).mono ?_)
      intro t ht
      refine (ih t (fun x hx => encoding x (List.mem_cons_of_mem d hx))
        (fun x hx => by rw [ht.rd, ht.wr, ht.regs .x19 (by decide)]; exact read x (List.mem_cons_of_mem d hx))
        (fun x hx => by rw [ht.wr, ht.regs .x19 (by decide)]; exact write x (List.mem_cons_of_mem d hx))
        tailSep (fun x hx => bounds x (List.mem_cons_of_mem d hx))).mono ?_
      intro u hu
      refine ⟨?_, fun r hr => (hu.regs r hr).trans (ht.regs r hr),
        hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.sp.trans ht.sp, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [hu.other_word x (bounds x (List.mem_cons_self ..)) headSep
            (fun a ha => bounds a (List.mem_cons_of_mem x ha))]
          exact ht.word
        · rw [hu.values x hx]
          unfold VG.Proof.Argon2.AArch64.Derive.normalizedWord
          have sep : x + 8 ≤ d ∨ d + 8 ≤ x := (headSep x hx).symm
          rw [ht.other_word x sep (bounds x (List.mem_cons_of_mem d hx)) (bounds d (List.mem_cons_self ..))]
      · apply (ht.frame.mono ?_).trans
        · have frame := hu.frame
          rw [ht.regs .x19 (by decide)] at frame
          exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)
        · intro region hr
          simp only [List.mem_singleton] at hr; subst region
          exact List.mem_cons_self ..

end VG.Proof.Argon2.AArch64.Derive
end

/-! Complete ABI preparation retains the inputs and exposes normalized public arguments. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def normalizedOffsets : List Nat := [192]

def prepareWrites (s : State) : List Region :=
  ⟨s.gpr .x19, 192⟩ :: normalizedOffsets.map fun d => ⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩

theorem SetupDone.other_word {s t : State} (h : VG.Proof.Argon2.AArch64.Derive.SetupDone s t) (d : Nat)
    (afterFrame : 192 ≤ d) (bound : d + 8 < 2 ^ 64) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64 := by
  rw [h.bp]
  apply h.frame.readW (r := ⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  simp only [List.mem_singleton] at hr; subst region
  simpa only [BitVec.add_zero] using Offset.disjoint (s.gpr .x19) (d := d) (n := 8) (e := 0) (k := 192)
    (Or.inr afterFrame) (Nat.le_of_lt bound) (by decide)

structure Prepared (s t : State) : Prop where
  bp : t.gpr .x19 = s.gpr .x19
  sp : t.sp = s.sp
  scratch : t.gpr .x24 = s.mem.readW (s.gpr .x19 + 248) 64
  values : ∀ arg ∈ VG.Proof.Argon2.AArch64.Derive.arguments, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 arg.1) 64 = VG.Proof.Argon2.AArch64.Derive.argumentValue s arg.2
  normalized : ∀ d ∈ VG.Proof.Argon2.AArch64.Derive.normalizedOffsets, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 =
    (((s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64)
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x19 → r ≠ .x24 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.AArch64.Derive.prepareWrites s) s.mem t.mem

theorem Prepared.other_word {s t : State} (h : VG.Proof.Argon2.AArch64.Derive.Prepared s t) (d : Nat)
    (afterFrame : 192 ≤ d) (bound : d + 8 < 2 ^ 64)
    (separate : ∀ e ∈ VG.Proof.Argon2.AArch64.Derive.normalizedOffsets, d + 8 ≤ e ∨ e + 8 ≤ d) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 =
      s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64 := by
  rw [h.bp]
  apply h.frame.readW (r := ⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simpa only [BitVec.add_zero] using Offset.disjoint (s.gpr .x19) (d := d) (n := 8) (e := 0) (k := 192)
      (Or.inr afterFrame) (Nat.le_of_lt bound) (by decide)
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    have bounds : ∀ e ∈ VG.Proof.Argon2.AArch64.Derive.normalizedOffsets, e + 8 ≤ 2 ^ 64 := by decide
    exact Offset.disjoint _ (separate e he) (Nat.le_of_lt bound) (bounds e he)

theorem prepareLocal_ok (s : State) (frameWrite : Covers [⟨s.gpr .x19, 192⟩] s.wr)
    (read : ∀ d ∈ 248 :: VG.Proof.Argon2.AArch64.Derive.normalizedOffsets, InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 d) 8)
    (write : ∀ d ∈ VG.Proof.Argon2.AArch64.Derive.normalizedOffsets, InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 8) :
    WP isa Impl.Argon2.AArch64.Derive.prepareLocal s (VG.Proof.Argon2.AArch64.Derive.Prepared s) := by
  unfold Impl.Argon2.AArch64.Derive.prepareLocal
  have scratchRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 248) 8 := read 248 (List.mem_cons_self ..)
  refine WP.seq ((VG.Proof.Argon2.AArch64.Derive.setup_ok s frameWrite scratchRead).mono ?_)
  intro a setup
  refine (VG.Proof.Argon2.AArch64.Derive.normalizeArgs_ok VG.Proof.Argon2.AArch64.Derive.normalizedOffsets a (by decide)
    (fun d hd => by rw [setup.rd, setup.wr, setup.bp]; exact read d (List.mem_cons_of_mem _ hd))
    (fun d hd => by rw [setup.wr, setup.bp]; exact write d hd) (by decide) (by decide)).mono ?_
  intro t normalized
  refine ⟨(normalized.regs .x19 (by decide)).trans setup.bp,
    normalized.sp.trans setup.sp,
    (normalized.regs .x24 (by decide)).trans setup.scratch, ?_, ?_, ?_,
    normalized.rd.trans setup.rd, normalized.wr.trans setup.wr, ?_⟩
  · intro arg ha
    have bound : ∀ arg ∈ VG.Proof.Argon2.AArch64.Derive.arguments, arg.1 + 8 < 2 ^ 64 := by decide
    have separate : ∀ arg ∈ VG.Proof.Argon2.AArch64.Derive.arguments, ∀ d ∈ VG.Proof.Argon2.AArch64.Derive.normalizedOffsets, arg.1 + 8 ≤ d ∨ d + 8 ≤ arg.1 := by decide
    rw [normalized.other_word arg.1 (bound arg ha) (separate arg ha) (by decide)]
    exact setup.values arg ha
  · intro d hd
    rw [normalized.values d hd]
    unfold VG.Proof.Argon2.AArch64.Derive.normalizedWord
    have afterFrame : ∀ d ∈ VG.Proof.Argon2.AArch64.Derive.normalizedOffsets, 192 ≤ d := by decide
    have bound : ∀ d ∈ VG.Proof.Argon2.AArch64.Derive.normalizedOffsets, d + 8 < 2 ^ 64 := by decide
    rw [setup.other_word d (afterFrame d hd) (bound d hd)]
  · intro r hr hb hx
    have notAx : ∀ r ∈ FillCompress.loopRegs, r ≠ .x8 := by decide
    exact (normalized.regs r (notAx r hr)).trans (setup.regs r hr hb hx)
  · apply (setup.frame.mono (by
      intro region hr
      simp only [List.mem_singleton] at hr
      subst region
      exact List.mem_cons_self ..)).trans
    have frame := normalized.frame
    rw [setup.bp] at frame
    exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveCopyArgs`. -/
section
/-! Merged from `Proof.Argon2.AArch64.DeriveCopyArg`. -/
section
/-! Copy a read-only caller argument into the private derivation frame. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def copySource (j : Nat) : Nat := 384 + 8 * j
def copyDestination (j : Nat) : Nat := 192 + 8 * j

structure CopiedArg (s t : State) (j : Nat) : Prop where
  mem : t.mem = s.mem.writeW (s.sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copyDestination j))
    (s.mem.readW (s.sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copySource j)) 64)
  regs : ∀ r, r ≠ .x8 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem copyArg_ok (s : State) (j : Nat)
    (bound : j < 10) (bp : s.gpr .x19 = s.sp)
    (read : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copySource j)) 8)
    (write : InRegions s.wr (s.sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copyDestination j)) 8) :
    WP isa (.block (Impl.Argon2.AArch64.Derive.copyArg j)) s (VG.Proof.Argon2.AArch64.Derive.CopiedArg s · j) := by
  have sourceAlign : VG.Proof.Argon2.AArch64.Derive.copySource j % 8 = 0 := by unfold VG.Proof.Argon2.AArch64.Derive.copySource; omega
  have sourceBound : VG.Proof.Argon2.AArch64.Derive.copySource j < 32768 := by unfold VG.Proof.Argon2.AArch64.Derive.copySource; omega
  have destAlign : VG.Proof.Argon2.AArch64.Derive.copyDestination j % 8 = 0 := by unfold VG.Proof.Argon2.AArch64.Derive.copyDestination; omega
  have destBound : VG.Proof.Argon2.AArch64.Derive.copyDestination j < 32768 := by unfold VG.Proof.Argon2.AArch64.Derive.copyDestination; omega
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.Derive.copyArg,
    show 384 + 8 * j = VG.Proof.Argon2.AArch64.Derive.copySource j from rfl,
    show 192 + 8 * j = VG.Proof.Argon2.AArch64.Derive.copyDestination j from rfl,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.load,
    State.store, addr, Size.bytes, Size.bits,
    sourceAlign, sourceBound, destAlign, destBound, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    bp, read, write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  intro r hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem CopiedArg.frame {s t : State} {j : Nat} (h : VG.Proof.Argon2.AArch64.Derive.CopiedArg s t j) :
    Frame [⟨s.sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copyDestination j), 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem CopiedArg.word {s t : State} {j : Nat} (h : VG.Proof.Argon2.AArch64.Derive.CopiedArg s t j) :
    t.mem.readW (t.sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copyDestination j)) 64 =
      s.mem.readW (s.sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copySource j)) 64 := by
  rw [h.sp, h.mem, Mem.readW_writeW_self64]

end VG.Proof.Argon2.AArch64.Derive
end

/-! Copy all stack arguments without modifying their caller-owned storage. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

structure CopiedArgs (s t : State) (js : List Nat) : Prop where
  values : ∀ j ∈ js, t.mem.readW (t.sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copyDestination j)) 64 =
    s.mem.readW (s.sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copySource j)) 64
  regs : ∀ r, r ≠ .x8 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (js.map fun j => (⟨s.sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copyDestination j), 8⟩ : Region)) s.mem t.mem

theorem CopiedArgs.other_word {s t : State} {js : List Nat} (h : VG.Proof.Argon2.AArch64.Derive.CopiedArgs s t js)
    (d : Nat) (bound : d + 8 ≤ 2 ^ 64)
    (separate : ∀ j ∈ js, d + 8 ≤ VG.Proof.Argon2.AArch64.Derive.copyDestination j ∨ VG.Proof.Argon2.AArch64.Derive.copyDestination j + 8 ≤ d)
    (bounds : ∀ j ∈ js, VG.Proof.Argon2.AArch64.Derive.copyDestination j + 8 ≤ 2 ^ 64) :
    t.mem.readW (t.sp + BitVec.ofNat 64 d) 64 = s.mem.readW (s.sp + BitVec.ofNat 64 d) 64 := by
  rw [h.sp]
  apply h.frame.readW (r := ⟨s.sp + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  exact Offset.disjoint _ (separate j hj) bound (bounds j hj)

theorem copyArgs_ok (js : List Nat) (s : State) (bp : s.gpr .x19 = s.sp) (bounds : ∀ j ∈ js, j < 10)
    (distinct : js.Nodup)
    (read : ∀ j ∈ js, InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copySource j)) 8)
    (write : ∀ j ∈ js, InRegions s.wr (s.sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copyDestination j)) 8) :
    WP isa (.block (js.flatMap Impl.Argon2.AArch64.Derive.copyArg)) s (VG.Proof.Argon2.AArch64.Derive.CopiedArgs s · js) := by
  induction js generalizing s with
  | nil => exact WP.block_nil ⟨by simp, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | cons j js ih =>
    have nodup := List.nodup_cons.mp distinct
    have jBound := bounds j (List.mem_cons_self ..)
    have tailBounds : ∀ x ∈ js, x < 10 := fun x hx => bounds x (List.mem_cons_of_mem _ hx)
    rw [List.flatMap_cons, WP.block_append_iff]
    refine (VG.Proof.Argon2.AArch64.Derive.copyArg_ok s j jBound bp (read j (List.mem_cons_self ..)) (write j (List.mem_cons_self ..))).mono ?_
    intro t ht
    refine (ih t (by rw [ht.regs .x19 (by decide), ht.sp]; exact bp) tailBounds nodup.2
      (fun x hx => by rw [ht.rd, ht.wr, ht.sp]; exact read x (List.mem_cons_of_mem _ hx))
      (fun x hx => by rw [ht.wr, ht.sp]; exact write x (List.mem_cons_of_mem _ hx))).mono ?_
    intro u hu
    refine ⟨?_, fun r hr => (hu.regs r hr).trans (ht.regs r hr),
      hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.sp.trans ht.sp, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hu.other_word (VG.Proof.Argon2.AArch64.Derive.copyDestination x) (by unfold VG.Proof.Argon2.AArch64.Derive.copyDestination; omega) (by
          intro y hy
          have ne : y ≠ x := fun eq => nodup.1 (eq ▸ hy)
          unfold VG.Proof.Argon2.AArch64.Derive.copyDestination; omega) (by
          intro y hy; have := tailBounds y hy; unfold VG.Proof.Argon2.AArch64.Derive.copyDestination; omega)]
        exact ht.word
      · rw [hu.values x hx, ht.sp, ht.mem]
        apply Mem.readW_writeW_sep ?_ (by decide)
        have xBound := tailBounds x hx
        exact Offset.sep _ (Or.inr (by unfold VG.Proof.Argon2.AArch64.Derive.copyDestination VG.Proof.Argon2.AArch64.Derive.copySource; omega))
          (by unfold VG.Proof.Argon2.AArch64.Derive.copySource; omega) (by unfold VG.Proof.Argon2.AArch64.Derive.copyDestination; omega)
    · apply (ht.frame.mono ?_).trans
      · have frame := hu.frame
        rw [ht.sp] at frame
        exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)
      · intro region hr
        simp only [List.mem_singleton] at hr; subst region
        exact List.mem_cons_self ..

end VG.Proof.Argon2.AArch64.Derive
end

/-! Prepare private copies of every ABI argument, preserving caller-owned storage. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def privateWrites (s : State) : List Region := [⟨s.sp, 192⟩, ⟨s.sp + 192, 80⟩]

structure PrivatePrepared (s t : State) : Prop where
  bp : t.gpr .x19 = s.sp
  sp : t.sp = s.sp
  scratch : t.gpr .x24 = s.mem.readW (s.sp + 440) 64
  values : ∀ arg ∈ VG.Proof.Argon2.AArch64.Derive.arguments, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 arg.1) 64 = VG.Proof.Argon2.AArch64.Derive.argumentValue s arg.2
  stackWords : ∀ j < 10, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copyDestination j)) 64 =
    let w := s.mem.readW (s.sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copySource j)) 64
    if j < 1 then (w.setWidth 32).setWidth 64 else w
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x19 → r ≠ .x24 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.AArch64.Derive.privateWrites s) s.mem t.mem

theorem private_prepare_local_ok (s : State) (bp : s.gpr .x19 = s.sp) (locals : Covers [⟨s.sp, 272⟩] s.wr)
    (read : ∀ j < 10, InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copySource j)) 8) :
    WP isa (.seq (.block Impl.Argon2.AArch64.Derive.copyArgs) Impl.Argon2.AArch64.Derive.prepareLocal) s (VG.Proof.Argon2.AArch64.Derive.PrivatePrepared s) := by
  have localWord : ∀ d, d + 8 ≤ 272 → InRegions s.wr (s.sp + BitVec.ofNat 64 d) 8 := by
    intro d hd
    exact locals _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ hd (by omega)⟩
  unfold Impl.Argon2.AArch64.Derive.copyArgs
  refine WP.seq ((VG.Proof.Argon2.AArch64.Derive.copyArgs_ok (List.range 10) s bp
    (fun _ h => List.mem_range.mp h) List.nodup_range (fun j h => read j (List.mem_range.mp h))
    (fun j h => localWord _ (by have := List.mem_range.mp h; unfold VG.Proof.Argon2.AArch64.Derive.copyDestination; omega))).mono ?_)
  intro a copied
  have sp := copied.sp
  have base : a.gpr .x19 = s.sp := (copied.regs .x19 (by decide)).trans bp
  refine (VG.Proof.Argon2.AArch64.Derive.prepareLocal_ok a (by
    intro p n h
    rw [copied.wr]
    rw [base] at h
    apply locals p n
    exact Covers.of_sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨_, List.mem_singleton_self _, 0, (BitVec.add_zero _).symm, show 0 + 192 ≤ 272 by decide⟩) p n h)
    (by
      intro d hd
      rw [copied.rd, copied.wr, base]
      have bound : ∀ d ∈ 248 :: VG.Proof.Argon2.AArch64.Derive.normalizedOffsets, d + 8 ≤ 272 := by decide
      obtain ⟨region, member, contains⟩ := localWord d (bound d hd)
      exact ⟨region, List.mem_append_right _ member, contains⟩)
    (by
      intro d hd; rw [copied.wr, base]
      have bound : ∀ d ∈ VG.Proof.Argon2.AArch64.Derive.normalizedOffsets, d + 8 ≤ 272 := by decide
      exact localWord d (bound d hd))).mono ?_
  intro t prepared
  have copiedValues (j : Nat) (hj : j < 10) :
      a.mem.readW (s.sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copyDestination j)) 64 =
        s.mem.readW (s.sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copySource j)) 64 := by
    have word := copied.values j (List.mem_range.mpr hj)
    rw [sp] at word
    exact word
  refine ⟨prepared.bp.trans base, prepared.sp.trans sp, ?_, ?_, ?_, ?_,
    prepared.rd.trans copied.rd, prepared.wr.trans copied.wr, ?_⟩
  · have word := copied.values 7 (by decide)
    change a.mem.readW (a.sp + 248) 64 = s.mem.readW (s.sp + 440) 64 at word
    rw [prepared.scratch, base]
    rw [sp] at word
    exact word
  · intro arg ha
    rw [prepared.values arg ha]
    unfold VG.Proof.Argon2.AArch64.Derive.argumentValue
    have notAx : ∀ arg ∈ VG.Proof.Argon2.AArch64.Derive.arguments, arg.2 ≠ .x8 := by decide
    rw [copied.regs arg.2 (notAx arg ha)]
  · intro j hj
    by_cases small : j < 1
    · have slot : ∀ j < 1, VG.Proof.Argon2.AArch64.Derive.copyDestination j ∈ VG.Proof.Argon2.AArch64.Derive.normalizedOffsets := by
        intro j hj
        have zero : j = 0 := by omega
        subst j
        decide
      rw [prepared.normalized _ (slot j small), base, copiedValues j hj, ite_eq_left small]
    · rw [ite_eq_right small, prepared.other_word _ (by unfold VG.Proof.Argon2.AArch64.Derive.copyDestination; omega)
        (by unfold VG.Proof.Argon2.AArch64.Derive.copyDestination; omega) (by
          intro d hd
          have upper : ∀ d ∈ VG.Proof.Argon2.AArch64.Derive.normalizedOffsets, d + 8 ≤ 200 := by decide
          have := upper d hd; unfold VG.Proof.Argon2.AArch64.Derive.copyDestination; omega)]
      rw [base]
      exact copiedValues j hj
  · intro r hr hb hx
    have notAx : ∀ r ∈ FillCompress.loopRegs, r ≠ .x8 := by decide
    exact (prepared.regs r hr hb hx).trans (copied.regs r (notAx r hr))
  · apply (copied.frame.sub ?_).trans (prepared.frame.sub ?_)
    · intro region hr
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      have bound := List.mem_range.mp hj
      refine ⟨⟨s.sp + 192, 80⟩, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
      unfold VG.Proof.Argon2.AArch64.Derive.copyDestination
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      exact Offset.sub_base _ (by omega)
    · intro region hr
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [base]; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
        rw [base]
        have bounds : ∀ d ∈ VG.Proof.Argon2.AArch64.Derive.normalizedOffsets, 192 ≤ d ∧ d + 8 ≤ 272 := by decide
        obtain ⟨lo, hi⟩ := bounds d hd
        refine ⟨⟨s.sp + 192, 80⟩, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
        rw [show d = 192 + (d - 192) by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
        exact Offset.sub_base _ (by omega)

end VG.Proof.Argon2.AArch64.Derive

namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

theorem base_ok (s : State) : WP isa (.block [.addSp .x19 0]) s fun t =>
    t.gpr .x19 = s.sp ∧ Divide.Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 0 < 4096 from by decide,
    ite_true, BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem private_prepare_ok (s : State) (locals : Covers [⟨s.sp, 272⟩] s.wr)
    (read : ∀ j < 10, InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copySource j)) 8) :
    WP isa Impl.Argon2.AArch64.Derive.prepare s (VG.Proof.Argon2.AArch64.Derive.PrivatePrepared s) := by
  unfold Impl.Argon2.AArch64.Derive.prepare
  refine WP.seq ((VG.Proof.Argon2.AArch64.Derive.base_ok s).mono ?_)
  rintro a ⟨base, kept⟩
  refine (VG.Proof.Argon2.AArch64.Derive.private_prepare_local_ok a (base.trans kept.sp.symm)
    (by rw [kept.sp, kept.wr]; exact locals)
    (by rw [kept.sp, kept.rd, kept.wr]; exact read)).mono ?_
  intro t prepared
  refine ⟨prepared.bp.trans kept.sp, prepared.sp.trans kept.sp, ?_, ?_, ?_, ?_,
    prepared.rd.trans kept.rd, prepared.wr.trans kept.wr, ?_⟩
  · rw [prepared.scratch, kept.sp, kept.mem]
  · intro arg ha
    rw [prepared.values arg ha]
    unfold VG.Proof.Argon2.AArch64.Derive.argumentValue
    have other : ∀ arg ∈ VG.Proof.Argon2.AArch64.Derive.arguments, arg.2 ∉ [Reg.x19] := by decide
    rw [kept.regs arg.2 (other arg ha)]
  · intro j hj
    rw [prepared.stackWords j hj, kept.sp, kept.mem]
  · intro r hr hb hx
    exact (prepared.regs r hr hb hx).trans (kept.regs r (by simpa only [List.mem_singleton] using hb))
  · have frame := prepared.frame
    simp only [VG.Proof.Argon2.AArch64.Derive.privateWrites, kept.sp, kept.mem] at frame
    exact frame
end VG.Proof.Argon2.AArch64.Derive
end

/-! Private frame permissions and caller argument values after the ABI prologue. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def prologueState (s : State) : State := VG.Proof.Argon2.AArch64.Derive.frameStart s Impl.Argon2.AArch64.Derive.saved

theorem prologue_sp (s : State) : (VG.Proof.Argon2.AArch64.Derive.prologueState s).sp = s.sp - BitVec.ofNat 64 384 :=
  VG.Proof.Argon2.AArch64.Derive.frameStart_sp s _

theorem frameStart_locals (s : State) (rs : List Reg) :
    (⟨(VG.Proof.Argon2.AArch64.Derive.frameStart s rs).sp, 272⟩ : Region) ∈ (VG.Proof.Argon2.AArch64.Derive.frameStart s rs).wr := by
  induction rs generalizing s with
  | nil => exact List.mem_cons_self ..
  | cons r rs ih => exact ih (pushed r s)

theorem prologue_locals (s : State) : Covers [⟨(VG.Proof.Argon2.AArch64.Derive.prologueState s).sp, 272⟩] (VG.Proof.Argon2.AArch64.Derive.prologueState s).wr := by
  intro p n ⟨region, member, contains⟩
  simp only [List.mem_singleton] at member; subst region
  exact ⟨_, VG.Proof.Argon2.AArch64.Derive.frameStart_locals s _, contains⟩

theorem prologue_source (s : State) (j : Nat) :
    (VG.Proof.Argon2.AArch64.Derive.prologueState s).sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copySource j) =
      s.sp + BitVec.ofNat 64 (8 * j) := by
  rw [VG.Proof.Argon2.AArch64.Derive.prologue_sp]
  unfold VG.Proof.Argon2.AArch64.Derive.copySource
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem prologue_reads {s : State} (h : VG.Proof.Argon2.AArch64.Derive.AbiEnvironment s) :
    ∀ j < 10, InRegions ((VG.Proof.Argon2.AArch64.Derive.prologueState s).rd ++ (VG.Proof.Argon2.AArch64.Derive.prologueState s).wr)
      ((VG.Proof.Argon2.AArch64.Derive.prologueState s).sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copySource j)) 8 := by
  intro j hj
  rw [VG.Proof.Argon2.AArch64.Derive.prologue_source]
  refine ⟨VG.Proof.Argon2.AArch64.Derive.abiArguments s, List.mem_append_left _ ?_, ?_⟩
  · change VG.Proof.Argon2.AArch64.Derive.abiArguments s ∈ (VG.Proof.Argon2.AArch64.Derive.frameStart s Impl.Argon2.AArch64.Derive.saved).rd
    rw [VG.Proof.Argon2.AArch64.Derive.frameStart_rd, h.rd]; exact List.mem_append_right _ (List.mem_singleton_self _)
  · unfold VG.Proof.Argon2.AArch64.Derive.abiArguments
    exact Offset.contains_base _ (by omega) (by omega)

theorem prologue_word {s : State} (h : VG.Proof.Argon2.AArch64.Derive.AbiEnvironment s) (j : Nat) (hj : j < 10) :
    (VG.Proof.Argon2.AArch64.Derive.prologueState s).mem.readW ((VG.Proof.Argon2.AArch64.Derive.prologueState s).sp + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copySource j)) 64 =
      VG.Proof.Argon2.AArch64.Derive.abiWord s (8 * j) := by
  rw [VG.Proof.Argon2.AArch64.Derive.prologue_source]
  have frame := VG.Proof.Argon2.AArch64.Derive.frameStart_frame s Impl.Argon2.AArch64.Derive.saved (by
    have space := h.stack; change 384 ≤ s.sp.toNat; omega)
  apply frame.readW (r := VG.Proof.Argon2.AArch64.Derive.abiArguments s) ?_ ?_ (by decide)
  · unfold VG.Proof.Argon2.AArch64.Derive.abiArguments
    exact Offset.contains_base _ (by omega) (by omega)
  · intro region hr
    simp only [List.mem_singleton] at hr; subst region
    unfold VG.Proof.Argon2.AArch64.Derive.abiArguments
    exact Offset.base_disjoint_below _ (by decide)

theorem prologue_prepare (s : State) (h : VG.Proof.Argon2.AArch64.Derive.AbiEnvironment s) :
    WP isa Impl.Argon2.AArch64.Derive.prepare (VG.Proof.Argon2.AArch64.Derive.prologueState s) (VG.Proof.Argon2.AArch64.Derive.PrivatePrepared (VG.Proof.Argon2.AArch64.Derive.prologueState s)) :=
  VG.Proof.Argon2.AArch64.Derive.private_prepare_ok _ (VG.Proof.Argon2.AArch64.Derive.prologue_locals s) (VG.Proof.Argon2.AArch64.Derive.prologue_reads h)

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveMetadata`. -/
section
/-! The private frame contains the exact arguments decoded by the shared contract. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

theorem private_stack_word {s t : State} (h : VG.Proof.Argon2.AArch64.Derive.AbiEnvironment s)
    (prepared : VG.Proof.Argon2.AArch64.Derive.PrivatePrepared (VG.Proof.Argon2.AArch64.Derive.prologueState s) t) (j : Nat) (hj : j < 10) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.copyDestination j)) 64 =
      let word := VG.Proof.Argon2.AArch64.Derive.abiWord s (8 * j)
      if j < 1 then (word.setWidth 32).setWidth 64 else word := by
  rw [prepared.stackWords j hj, VG.Proof.Argon2.AArch64.Derive.prologue_word h j hj]

theorem private_argument_word {s t : State} (prepared : VG.Proof.Argon2.AArch64.Derive.PrivatePrepared (VG.Proof.Argon2.AArch64.Derive.prologueState s) t)
    (arg : Nat × Reg) (member : arg ∈ VG.Proof.Argon2.AArch64.Derive.arguments) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 arg.1) 64 = VG.Proof.Argon2.AArch64.Derive.argumentValue s arg.2 := by
  rw [prepared.values arg member]
  unfold VG.Proof.Argon2.AArch64.Derive.argumentValue
  unfold VG.Proof.Argon2.AArch64.Derive.prologueState
  rw [VG.Proof.Argon2.AArch64.Derive.frameStart_reg s _ arg.2]

theorem private_local_write {s t : State} (prepared : VG.Proof.Argon2.AArch64.Derive.PrivatePrepared (VG.Proof.Argon2.AArch64.Derive.prologueState s) t)
    (d n : Nat) (bound : d + n ≤ 272) : InRegions t.wr (t.gpr .x19 + BitVec.ofNat 64 d) n := by
  rw [prepared.wr, prepared.bp]
  apply VG.Proof.Argon2.AArch64.Derive.prologue_locals s
  exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ bound (by omega)⟩

theorem private_local_read {s t : State} (prepared : VG.Proof.Argon2.AArch64.Derive.PrivatePrepared (VG.Proof.Argon2.AArch64.Derive.prologueState s) t)
    (d n : Nat) (bound : d + n ≤ 272) :
    InRegions (t.rd ++ t.wr) (t.gpr .x19 + BitVec.ofNat 64 d) n := by
  obtain ⟨r, hr, hc⟩ := VG.Proof.Argon2.AArch64.Derive.private_local_write prepared d n bound
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem private_parameters {s t : State} (h : VG.Proof.Argon2.AArch64.Derive.AbiEnvironment s)
    (prepared : VG.Proof.Argon2.AArch64.Derive.PrivatePrepared (VG.Proof.Argon2.AArch64.Derive.prologueState s) t) : Parameters.Ready (VG.Proof.Argon2.AArch64.Derive.abiParams s) t := by
  refine ⟨VG.Proof.Argon2.AArch64.Derive.private_local_read prepared 176 8 (by decide), VG.Proof.Argon2.AArch64.Derive.private_local_read prepared 184 8 (by decide),
    ?_, ?_, h.valid.1, h.valid.2.2.2.2.2.1, h.valid.2.1⟩
  · have word := VG.Proof.Argon2.AArch64.Derive.private_argument_word prepared (176, .x6) (by decide)
    change t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 176) 64 =
      (((s.gpr .x6).setWidth 32).setWidth 64) at word
    change t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 176) 64 =
      BitVec.ofNat 64 ((s.gpr .x6).setWidth 32).toNat
    rw [word, BitVec.ofNat_toNat]
  · have word := VG.Proof.Argon2.AArch64.Derive.private_argument_word prepared (184, .x7) (by decide)
    change t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 184) 64 =
      (((s.gpr .x7).setWidth 32).setWidth 64) at word
    change t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 184) 64 =
      BitVec.ofNat 64 ((s.gpr .x7).setWidth 32).toNat
    rw [word, BitVec.ofNat_toNat]

end VG.Proof.Argon2.AArch64.Derive
end

/-! The private frame and called functions stay within the reviewed stack allowance. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

theorem frameStart_wr_member (s : State) (rs : List Reg) (region : Region) (member : region ∈ s.wr) :
    region ∈ (VG.Proof.Argon2.AArch64.Derive.frameStart s rs).wr := by
  induction rs generalizing s with
  | nil => exact List.mem_cons_of_mem _ member
  | cons r rs ih => apply ih; exact List.mem_cons_of_mem _ member

theorem private_wr_member {s t : State} (prepared : VG.Proof.Argon2.AArch64.Derive.PrivatePrepared (VG.Proof.Argon2.AArch64.Derive.prologueState s) t)
    (region : Region) (member : region ∈ s.wr) : region ∈ t.wr := by
  rw [prepared.wr]
  exact VG.Proof.Argon2.AArch64.Derive.frameStart_wr_member s _ region member

theorem private_bp {s t : State} (prepared : VG.Proof.Argon2.AArch64.Derive.PrivatePrepared (VG.Proof.Argon2.AArch64.Derive.prologueState s) t) :
    t.gpr .x19 = s.sp - BitVec.ofNat 64 384 := prepared.bp.trans (VG.Proof.Argon2.AArch64.Derive.prologue_sp s)

theorem private_sp {s t : State} (prepared : VG.Proof.Argon2.AArch64.Derive.PrivatePrepared (VG.Proof.Argon2.AArch64.Derive.prologueState s) t) :
    t.sp = s.sp - BitVec.ofNat 64 384 := prepared.sp.trans (VG.Proof.Argon2.AArch64.Derive.prologue_sp s)

theorem private_stack_minimum {s t : State} (h : VG.Proof.Argon2.AArch64.Derive.AbiEnvironment s)
    (prepared : VG.Proof.Argon2.AArch64.Derive.PrivatePrepared (VG.Proof.Argon2.AArch64.Derive.prologueState s) t) : 16 ≤ t.sp.toNat := by
  rw [VG.Proof.Argon2.AArch64.Derive.private_sp prepared, BitVec.toNat_sub_of_le (by
    rw [BitVec.le_def]
    change 384 ≤ s.sp.toNat
    have := h.stack; omega)]
  change 16 ≤ s.sp.toNat - 384
  have := h.stack; omega

theorem private_frame_sub {s t : State} (prepared : VG.Proof.Argon2.AArch64.Derive.PrivatePrepared (VG.Proof.Argon2.AArch64.Derive.prologueState s) t) :
    Region.Sub ⟨t.gpr .x19, 272⟩ (below (s.sp) 400) := by
  rw [VG.Proof.Argon2.AArch64.Derive.private_bp prepared]
  exact Offset.sub_below _ (by decide) (by decide)

theorem private_stack_sub {s t : State} (prepared : VG.Proof.Argon2.AArch64.Derive.PrivatePrepared (VG.Proof.Argon2.AArch64.Derive.prologueState s) t)
    (n : Nat) (bound : n ≤ 16) : Region.Sub (below (t.sp) n) (below (s.sp) 400) := by
  rw [VG.Proof.Argon2.AArch64.Derive.private_sp prepared]
  unfold below
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  exact Offset.sub_below _ (by omega) (by omega)

theorem private_frame_disjoint {s t : State} (h : VG.Proof.Argon2.AArch64.Derive.AbiEnvironment s)
    (prepared : VG.Proof.Argon2.AArch64.Derive.PrivatePrepared (VG.Proof.Argon2.AArch64.Derive.prologueState s) t) (buffer : Region × Bool)
    (member : buffer ∈ VG.Proof.Argon2.AArch64.Derive.abiBuffers s ++ [(VG.Proof.Argon2.AArch64.Derive.abiArguments s, false)]) :
    (⟨t.gpr .x19, 272⟩ : Region).Disjoint buffer.1 :=
  (h.reserved _ (List.mem_singleton_self _) buffer member).sub_left
    (VG.Proof.Argon2.AArch64.Derive.private_frame_sub prepared)

theorem private_stack_disjoint {s t : State} (h : VG.Proof.Argon2.AArch64.Derive.AbiEnvironment s)
    (prepared : VG.Proof.Argon2.AArch64.Derive.PrivatePrepared (VG.Proof.Argon2.AArch64.Derive.prologueState s) t) (buffer : Region × Bool)
    (member : buffer ∈ VG.Proof.Argon2.AArch64.Derive.abiBuffers s ++ [(VG.Proof.Argon2.AArch64.Derive.abiArguments s, false)]) (n : Nat) (bound : n ≤ 16) :
    (below (t.sp) n).Disjoint buffer.1 :=
  (h.reserved _ (List.mem_singleton_self _) buffer member).sub_left
    (VG.Proof.Argon2.AArch64.Derive.private_stack_sub prepared n bound)

theorem private_frame_stack {s t : State} (prepared : VG.Proof.Argon2.AArch64.Derive.PrivatePrepared (VG.Proof.Argon2.AArch64.Derive.prologueState s) t)
    (n : Nat) (bound : n ≤ 16) : (⟨t.gpr .x19, 272⟩ : Region).Disjoint (below (t.sp) n) := by
  rw [prepared.bp, prepared.sp]
  exact Offset.base_disjoint_below _ (by omega)

theorem private_work_member {s t : State} (h : VG.Proof.Argon2.AArch64.Derive.AbiEnvironment s)
    (prepared : VG.Proof.Argon2.AArch64.Derive.PrivatePrepared (VG.Proof.Argon2.AArch64.Derive.prologueState s) t) : VG.Proof.Argon2.AArch64.Derive.abiWork s ∈ t.wr := by
  apply VG.Proof.Argon2.AArch64.Derive.private_wr_member prepared
  rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

end VG.Proof.Argon2.AArch64.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillKernelStable`. -/
section

/-! Register-only helpers retain the filling allocation and position invariants. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64

theorem Ready.of_keeps {p : Spec.Argon2.Params} {pass lane slice index : Nat} {s t : State}
    (h : VG.Proof.Argon2.AArch64.FillKernel.Ready p pass lane slice index s) (k : Divide.Keeps ReferenceMap.changed s t) :
    VG.Proof.Argon2.AArch64.FillKernel.Ready p pass lane slice index t := by
  refine ⟨h.layout.of_keeps k, h.bounds, h.position.of_keeps k, ?_, ?_⟩
  · rw [k.mem, k.regs .x19 (by decide)]; exact h.passWord
  · rw [k.mem, k.regs .x19 (by decide)]; exact h.lanesWord

end VG.Proof.Argon2.AArch64.FillKernel

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.RandomSourcePrepare`. -/
section

section

/-! Short mask computations for the public addressing-mode predicate. -/

namespace VG.Proof.Argon2.AArch64.AddressMode

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressMode
open VG.Impl.Argon2.AArch64

theorem zero_nat (x : Addr) : x.toNat < 1 ↔ x = 0#64 := by
  constructor
  · intro h; exact BitVec.eq_of_toNat_eq (Nat.lt_one_iff.mp h)
  · intro h; rw [h]; decide

theorem xor_nat (x y : Addr) : (x ^^^ y).toNat < 1 ↔ x = y := by
  rw [VG.Proof.Argon2.AArch64.AddressMode.zero_nat, BitVec.xor_eq_zero_iff]

theorem borrow_lt (a b : Nat) :
    (if decide (b ≤ a) = true then (0 : Addr) else -1) =
      Divide.mask (decide (a < b)) := by
  by_cases h : a < b
  · simp only [show ¬b ≤ a by omega, decide_false, Bool.false_eq_true,
      ite_false, h, decide_true, Divide.mask, ite_true]
  · simp only [show b ≤ a by omega, decide_true, ite_true,
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


    BitVec.setWidth_eq, Bool.toNat_true, sub_value, sub_carry, borrow_mask, VG.Proof.Argon2.AArch64.AddressMode.borrow_lt,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (1#16).setWidth 64 = 1#64 from rfl,
    show (2#16).setWidth 64 = 2#64 from rfl,
    show 1 < 65536 from by decide, show 2 < 65536 from by decide,
    show 0 < 4096 from by decide, show (63 : Nat) < 64 from by decide,
    BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    VG.Proof.Argon2.AArch64.AddressMode.borrow_lt,  VG.Proof.Argon2.AArch64.AddressMode.zero_nat, BitVec.xor_eq_zero_iff,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]
  all_goals rfl

theorem pass_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8) :
    WP isa (.block VG.Impl.Argon2.AArch64.AddressMode.pass) s fun t =>
      t.gpr .x5 = Divide.mask (decide (s.mem.readW (off (s.gpr .x19) 0) 64 = 0#64)) ∧
      Divide.Keeps [.x5, .x13, .x14, .x15] s t := by
  simp only [off, BitVec.add_zero] at hr
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.AArch64.AddressMode.pass, off, show 0 % 8 = 0 ∧ 0 < 4096 * 8 from by decide, hr, and_self,
    show (1#64).toNat = 1 from rfl, Instructions.mov, Instructions.load,
    Instructions.comparei, Instructions.compare, Instructions.sbb, Instructions.imm, Instructions.mark,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.read, Size.bytes, Size.bits,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_write, RegUpd.c_addWithCarry,


    BitVec.setWidth_eq, Bool.toNat_true, sub_value, sub_carry, borrow_mask, VG.Proof.Argon2.AArch64.AddressMode.borrow_lt,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (1#16).setWidth 64 = 1#64 from rfl,

    show 1 < 65536 from by decide,
    show 0 < 4096 from by decide, show (63 : Nat) < 64 from by decide,
    BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    VG.Proof.Argon2.AArch64.AddressMode.borrow_lt,  VG.Proof.Argon2.AArch64.AddressMode.zero_nat,
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


    BitVec.setWidth_eq, Bool.toNat_true, sub_value, sub_carry, borrow_mask, VG.Proof.Argon2.AArch64.AddressMode.borrow_lt,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (1#16).setWidth 64 = 1#64 from rfl,
    show (2#16).setWidth 64 = 2#64 from rfl,
    show 1 < 65536 from by decide, show 2 < 65536 from by decide,
    show 0 < 4096 from by decide, show (63 : Nat) < 64 from by decide,
    BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    VG.Proof.Argon2.AArch64.AddressMode.borrow_lt,
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
    (h : VG.Proof.Argon2.AArch64.FillKernel.Ready p pass lane slice index s) (done : VG.Proof.Argon2.AArch64.FillKernel.Done s t p pass lane slice index)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 16 ∨ 24 ≤ d) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.regs .x19 (by simp [FillCompress.loopRegs])]
  have sub : Region.Sub ⟨off (s.gpr .x19) d, 8⟩ ⟨s.gpr .x19, 272⟩ := Offset.sub_base _ bound
  have currentSub : Region.Sub ⟨VG.Proof.Argon2.AArch64.FillKernel.current s p lane slice index, 1024⟩ ⟨VG.Proof.Argon2.AArch64.FillKernel.matrix s, p.blocks * 1024⟩ :=
    VG.Proof.Argon2.AArch64.FillKernel.cell_sub p _ h.bounds.lanesPositive h.bounds.laneBound
      (Proof.Argon2.column_lt p h.bounds.lanesPositive h.bounds.sliceBound h.bounds.indexBound)
  exact done.frame.readW (r := ⟨off (s.gpr .x19) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [VG.Proof.Argon2.AArch64.FillKernel.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ((h.layout.matrixFrame.sub_left currentSub).symm).sub_left sub
    · exact h.layout.frameWork.sub_left sub
    · exact h.layout.frameStack.sub_left sub
    · exact Offset.disjoint _ separate (by omega) (by decide)) (by decide)

theorem Done.retains {s t : State} {p : Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.AArch64.FillKernel.Ready p pass lane slice index s) (done : VG.Proof.Argon2.AArch64.FillKernel.Done s t p pass lane slice index) :
    VG.Proof.Argon2.AArch64.FillKernel.Ready p pass lane slice index t := by
  have bp := done.regs .x19 (by simp [FillCompress.loopRegs])
  have sp := done.sp
  have matrix' : VG.Proof.Argon2.AArch64.FillKernel.matrix t = VG.Proof.Argon2.AArch64.FillKernel.matrix s := done.frame_word h 232 (by decide) (by decide)
  have work' : VG.Proof.Argon2.AArch64.FillKernel.work t = VG.Proof.Argon2.AArch64.FillKernel.work s := done.frame_word h 248 (by decide) (by decide)
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
    WP isa VG.Impl.Argon2.AArch64.AddressMode.code s fun t => t.gpr .x6 = VG.Proof.Argon2.AArch64.AddressMode.value s ∧ Divide.Keeps VG.Proof.Argon2.AArch64.AddressMode.changed s t := by
  unfold VG.Impl.Argon2.AArch64.AddressMode.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.AddressMode.kind_ok s kindRead).mono ?_)
  rintro a ⟨i, id, ka⟩
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) 0) 8 := by
    rw [ka.rd, ka.wr, ka.regs .x19 (by decide)]; exact passRead
  refine WP.seq ((VG.Proof.Argon2.AArch64.AddressMode.pass_ok a read).mono ?_)
  rintro b ⟨zero, kb⟩
  refine (VG.Proof.Argon2.AArch64.AddressMode.slice_ok b).mono ?_
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
    VG.Proof.Argon2.AArch64.AddressMode.value s = (BitVec.ofBool (Spec.Argon2.independent p pass slice)).setWidth 64 := by
  have passZero : BitVec.ofNat 64 pass = 0#64 ↔ pass = 0 := ReferenceMap.word_zero pass passBound
  unfold VG.Proof.Argon2.AArch64.AddressMode.value
  rw [kindWord, passWord, sliceWord, VG.Proof.Argon2.AArch64.AddressMode.masks,
    ReferenceMap.word_nat slice sliceBound]
  simp only [passZero]
  unfold Spec.Argon2.independent
  rw [VG.Proof.Argon2.AArch64.AddressMode.variants, Bool.beq_eq_decide_eq pass 0]

theorem code_spec_ok (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (kindRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 112) 8)
    (passRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8)
    (kindWord : s.mem.readW (off (s.gpr .x19) 112) 64 = BitVec.ofNat 64 p.variant.code)
    (passWord : s.mem.readW (off (s.gpr .x19) 0) 64 = BitVec.ofNat 64 pass)
    (sliceWord : s.gpr .x22 = BitVec.ofNat 64 slice)
    (passBound : pass < 2 ^ 64) (sliceBound : slice < 2 ^ 64) :
    WP isa VG.Impl.Argon2.AArch64.AddressMode.code s fun t => t.gpr .x6 =
      (BitVec.ofBool (Spec.Argon2.independent p pass slice)).setWidth 64 ∧ Divide.Keeps VG.Proof.Argon2.AArch64.AddressMode.changed s t :=
  (VG.Proof.Argon2.AArch64.AddressMode.code_ok s kindRead passRead).mono (fun _ h =>
    ⟨h.1.trans (VG.Proof.Argon2.AArch64.AddressMode.value_spec s p pass slice kindWord passWord sliceWord passBound sliceBound), h.2⟩)

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
  selected : VG.Proof.Argon2.AArch64.AddressCache.Selected s t p pass lane slice
  random : t.gpr .x0 =
    (addressBlock p pass lane slice (VG.Proof.Argon2.AArch64.AddressCache.wanted s))[(s.gpr .x23).toNat % 128]'(Nat.mod_lt _ (by decide))

theorem code_ok (p : Params) (pass lane slice old : Nat) (s : State)
    (h : VG.Proof.Argon2.AArch64.AddressCache.Ready p pass lane slice old s) :
    WP isa VG.Impl.Argon2.AArch64.AddressCache.code s (VG.Proof.Argon2.AArch64.AddressCache.Done s · p pass lane slice) := by
  unfold VG.Impl.Argon2.AArch64.AddressCache.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.AddressCache.selected_ok p pass lane slice old s h).mono ?_)
  intro a selected
  refine (VG.Proof.Argon2.AArch64.AddressCache.word_ok a selected.layout).mono ?_
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
    (layout : AddressCalls.Ready s) (h : VG.Proof.Argon2.AArch64.AddressCache.Selected s t p pass lane slice)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 8 ∨ 16 ≤ d) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [h.regs .x19 (by simp [FillCompress.loopRegs])]
  have sub : Region.Sub ⟨off (s.gpr .x19) d, 8⟩ ⟨s.gpr .x19, 272⟩ := Offset.sub_base _ bound
  exact h.frame.readW (r := ⟨off (s.gpr .x19) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [VG.Proof.Argon2.AArch64.AddressCache.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact layout.frameWork.sub_left sub
    · exact layout.frameStack.sub_left sub
    · exact Offset.disjoint _ separate (by omega) (by decide)) (by decide)

theorem Selected.words {s t : State} {p : Params} {pass lane slice old : Nat}
    (ready : VG.Proof.Argon2.AArch64.AddressCache.Ready p pass lane slice old s) (h : VG.Proof.Argon2.AArch64.AddressCache.Selected s t p pass lane slice) :
    AddressHeader.Words p pass lane slice (VG.Proof.Argon2.AArch64.AddressCache.wanted s) t := by
  exact ⟨(h.frame_word ready.layout 0 (by decide) (by decide)).trans ready.words.passWord,
    (h.regs .x24 (by simp [FillCompress.loopRegs])).trans ready.words.laneWord,
    (h.regs .x22 (by simp [FillCompress.loopRegs])).trans ready.words.sliceWord,
    (h.frame_word ready.layout 240 (by decide) (by decide)).trans ready.words.blocksWord,
    (h.frame_word ready.layout 72 (by decide) (by decide)).trans ready.words.passesWord,
    (h.frame_word ready.layout 112 (by decide) (by decide)).trans ready.words.variantWord,
    h.counterWord.trans (VG.Proof.Argon2.AArch64.AddressCache.counter_nat _)⟩

theorem Ready.of_keeps {p : Params} {pass lane slice old : Nat} {s t : State}
    (h : VG.Proof.Argon2.AArch64.AddressCache.Ready p pass lane slice old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    VG.Proof.Argon2.AArch64.AddressCache.Ready p pass lane slice old t := by
  have regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r := by
    intro r hr
    apply k.regs
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have stable := AddressCalls.stable_of_frame h.layout regs k.rd k.wr
    (by rw [k.mem]; exact Frame.refl _ _) k.sp
  refine ⟨stable.ready, stable.reads h.reads, ?_, stable.words h.layout h.words, ?_⟩
  · rw [k.wr, k.regs .x19 (by decide)]; exact h.write
  · intro same
    have wanted' : VG.Proof.Argon2.AArch64.AddressCache.wanted t = VG.Proof.Argon2.AArch64.AddressCache.wanted s := by unfold VG.Proof.Argon2.AArch64.AddressCache.wanted; rw [k.regs .x23 (by decide)]
    rw [k.mem, k.regs .x19 (by decide), k.regs .x23 (by decide)] at same
    rw [k.mem, stable.work_eq, wanted']
    exact h.cached same

end VG.Proof.Argon2.AArch64.AddressCache
end

/-! Merged from `Proof.Argon2.AArch64.AddressCacheMatrix`. -/
section
/-! Independent-address generation leaves every matrix cell intact. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Spec.Argon2

theorem Selected.filling_ready {s t : State} {p : Params} {pass lane slice index : Nat}
    (cacheLayout : AddressCalls.Ready s) (h : FillKernel.Ready p pass lane slice index s)
    (done : VG.Proof.Argon2.AArch64.AddressCache.Selected s t p pass lane slice) : FillKernel.Ready p pass lane slice index t := by
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
    (done : VG.Proof.Argon2.AArch64.AddressCache.Selected s t p pass lane slice) (blocks : Array Block)
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
    simp only [VG.Proof.Argon2.AArch64.AddressCache.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
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

theorem wanted_bound (s : State) : VG.Proof.Argon2.AArch64.AddressCache.wanted s < 2 ^ 64 := by
  unfold VG.Proof.Argon2.AArch64.AddressCache.wanted
  have := (s.gpr .x23).isLt
  omega

theorem Invariant.ready {p : Params} {pass lane slice old : Nat} {s : State}
    (h : VG.Proof.Argon2.AArch64.AddressCache.Invariant p pass lane slice old s) : VG.Proof.Argon2.AArch64.AddressCache.Ready p pass lane slice old s := by
  refine ⟨h.layout, h.reads, h.write, h.words, ?_⟩
  intro same
  have word : BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.AddressCache.wanted s) = BitVec.ofNat 64 old := by
    unfold VG.Proof.Argon2.AArch64.AddressCache.wanted
    rw [← VG.Proof.Argon2.AArch64.AddressCache.counter_nat]; exact same.trans h.words.counterWord
  have equal := (ReferenceMap.word_eq _ _ (VG.Proof.Argon2.AArch64.AddressCache.wanted_bound s) h.bound).mp word
  rcases h.cached with zero | cached
  · exfalso
    exact VG.Proof.Argon2.AArch64.AddressCache.counter_ne_zero _ (same.trans (h.words.counterWord.trans (by rw [zero]; rfl)))
  · rw [← equal] at cached
    exact cached

theorem Selected.invariant {s t : State} {p : Params} {pass lane slice old : Nat}
    (ready : VG.Proof.Argon2.AArch64.AddressCache.Ready p pass lane slice old s) (h : VG.Proof.Argon2.AArch64.AddressCache.Selected s t p pass lane slice) :
    VG.Proof.Argon2.AArch64.AddressCache.Invariant p pass lane slice (VG.Proof.Argon2.AArch64.AddressCache.wanted s) t := by
  have bp := h.regs .x19 (by simp [FillCompress.loopRegs])
  refine ⟨h.layout, ?_, ?_, h.words ready, VG.Proof.Argon2.AArch64.AddressCache.wanted_bound s, Or.inr ?_⟩
  · rw [h.rd, h.wr, bp]; exact ready.reads
  · rw [h.wr, bp]; exact ready.write
  · rw [h.work_eq]; exact h.block

theorem Invariant.zero {p : Params} {pass lane slice : Nat} {s : State}
    (h : VG.Proof.Argon2.AArch64.AddressCache.Ready p pass lane slice 0 s) : VG.Proof.Argon2.AArch64.AddressCache.Invariant p pass lane slice 0 s :=
  ⟨h.layout, h.reads, h.write, h.words, by decide, Or.inl rfl⟩

theorem Invariant.of_state {p : Params} {pass lane slice old : Nat} {s t : State}
    (h : VG.Proof.Argon2.AArch64.AddressCache.Invariant p pass lane slice old s)
    (regs : ∀ r ∈ [Reg.x19, .x24, .x22], t.gpr r = s.gpr r)
    (sp : t.sp = s.sp) (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
    VG.Proof.Argon2.AArch64.AddressCache.Invariant p pass lane slice old t := by
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
    (h : VG.Proof.Argon2.AArch64.AddressCache.Invariant p pass lane slice old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    VG.Proof.Argon2.AArch64.AddressCache.Invariant p pass lane slice old t := by
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
    (h : VG.Proof.Argon2.AArch64.RandomSource.Ready p pass lane slice index old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    VG.Proof.Argon2.AArch64.RandomSource.Ready p pass lane slice index old t := by
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
    (h : VG.Proof.Argon2.AArch64.RandomSource.Ready p pass lane slice index old s) : WP isa VG.Impl.Argon2.AArch64.RandomSource.prepare s fun t =>
      eval (.zero .x .x15) t = some (!independent p pass slice) ∧ Divide.Keeps ReferenceMap.changed s t := by
  unfold VG.Impl.Argon2.AArch64.RandomSource.prepare
  refine WP.seq ((AddressMode.code_spec_ok s p pass slice
    (h.cache.reads 112 (by simp)) (h.cache.reads 0 (by simp))
    h.cache.words.variantWord h.filling.passWord h.filling.position.slice
    (Nat.lt_trans h.filling.bounds.passBound (by decide))
    (Nat.lt_trans h.filling.bounds.sliceBound (by decide))).mono ?_)
  rintro a ⟨mode, keeps⟩
  refine (VG.Proof.Argon2.AArch64.RandomSource.test_ok a).mono ?_
  rintro t ⟨flag, tested⟩
  refine ⟨?_, (keeps.mono (by decide)).trans (tested.mono (by decide))⟩
  rw [flag, mode, VG.Proof.Argon2.AArch64.RandomSource.bool_zero]

end VG.Proof.Argon2.AArch64.RandomSource

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.RandomSource`. -/
section

/-! Merged from `Proof.Argon2.AArch64.DependentWordState`. -/
section
/-! The dependent source hands the filling step its random word and unchanged matrix. -/

namespace VG.Proof.Argon2.AArch64.DependentWord

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.DependentWord

theorem state_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (dependent : independent p pass slice = false) : WP isa VG.Impl.Argon2.AArch64.DependentWord.code s fun t =>
      t.gpr .x0 = Proof.Argon2.FillStep.random p pass lane slice index state.memory ∧
      FillKernel.Ready p pass lane slice index t ∧
      Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory ∧
      Divide.Keeps ReferenceMap.changed s t := by
  refine (VG.Proof.Argon2.AArch64.DependentWord.code_spec_ok s p pass lane slice index h state represented dependent).mono ?_
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
  ready : ∃ old, VG.Proof.Argon2.AArch64.RandomSource.Ready p pass lane slice index old t
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.AArch64.RandomSource.writes s) s.mem t.mem
  sp : t.sp = s.sp

theorem Ready.index_nat {p : Params} {pass lane slice index old : Nat} {s : State}
    (h : VG.Proof.Argon2.AArch64.RandomSource.Ready p pass lane slice index old s) : (s.gpr .x23).toNat = index := by
  rw [h.filling.position.index, ReferenceMap.word_nat index h.filling.bounds.index_bound64]

theorem independent_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : VG.Proof.Argon2.AArch64.RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (mode : independent p pass slice = true) :
    WP isa Impl.Argon2.AArch64.AddressCache.code s (VG.Proof.Argon2.AArch64.RandomSource.Done s · p pass lane slice index state) := by
  refine (AddressCache.code_ok p pass lane slice old s h.cache.ready).mono ?_
  intro t done
  have base : FillKernel.matrix t = FillKernel.matrix s :=
    done.selected.frame_word h.cache.layout 232 (by decide) (by decide)
  have nextReady : VG.Proof.Argon2.AArch64.RandomSource.Ready p pass lane slice index (AddressCache.wanted s) t := by
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
    (h : VG.Proof.Argon2.AArch64.RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (mode : independent p pass slice = false) :
    WP isa Impl.Argon2.AArch64.DependentWord.code s (VG.Proof.Argon2.AArch64.RandomSource.Done s · p pass lane slice index state) := by
  refine (DependentWord.state_ok s p pass lane slice index h.filling state represented mode).mono ?_
  rintro t ⟨random, _, matrix, keeps⟩
  refine ⟨random, ⟨old, h.of_keeps keeps⟩, matrix, ?_, keeps.rd, keeps.wr, ?_, keeps.sp⟩
  · intro r hr
    apply keeps.regs
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [keeps.mem]; exact Frame.refl _ _

theorem code_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : VG.Proof.Argon2.AArch64.RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.RandomSource.code s (VG.Proof.Argon2.AArch64.RandomSource.Done s · p pass lane slice index state) := by
  unfold Impl.Argon2.AArch64.RandomSource.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.RandomSource.prepare_ok s p pass lane slice index old h).mono ?_)
  rintro a ⟨flag, keeps⟩
  have next := h.of_keeps keeps
  have representedA : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks state.memory := by
    have base : FillKernel.matrix a = FillKernel.matrix s := by
      unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .x19 (by decide)]
    rw [base, keeps.mem]; exact represented
  have finish {t : State} (done : VG.Proof.Argon2.AArch64.RandomSource.Done a t p pass lane slice index state) :
      VG.Proof.Argon2.AArch64.RandomSource.Done s t p pass lane slice index state := by
    refine ⟨done.random, done.ready, done.represented, ?_, done.rd.trans keeps.rd,
      done.wr.trans keeps.wr, ?_, done.sp.trans keeps.sp⟩
    · intro r hr
      have ne : r ∉ ReferenceMap.changed := by
        simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (done.regs r hr).trans (keeps.regs r ne)
    · have frame := done.frame
      unfold VG.Proof.Argon2.AArch64.RandomSource.writes AddressCache.writes AddressCalls.work at frame ⊢
      rw [keeps.mem, keeps.regs .x19 (by decide), keeps.sp] at frame
      exact frame
  refine WP.ite (!independent p pass slice) flag ?_ ?_
  · intro mode
    have dependent : independent p pass slice = false := by
      cases eq : independent p pass slice <;> simp_all
    exact (VG.Proof.Argon2.AArch64.RandomSource.dependent_ok a p pass lane slice index old next state representedA dependent).mono
      (fun _ done => finish done)
  · intro mode
    have independent : independent p pass slice = true := by
      cases eq : independent p pass slice <;> simp_all
    exact (VG.Proof.Argon2.AArch64.RandomSource.independent_ok a p pass lane slice index old next state representedA independent).mono
      (fun _ done => finish done)

end VG.Proof.Argon2.AArch64.RandomSource

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillBlock`. -/
section

/-! Merged from `Proof.Argon2.AArch64.RandomSourceState`. -/
section
/-! Frame words and public allocation pointers survive random-word dispatch. -/

namespace VG.Proof.Argon2.AArch64.RandomSource

open VG VG.AArch64 VG.Spec.Argon2

theorem Done.frame_word {s t : State} {p : Params} {pass lane slice index old : Nat} {state : FillState}
    (h : VG.Proof.Argon2.AArch64.RandomSource.Ready p pass lane slice index old s) (done : VG.Proof.Argon2.AArch64.RandomSource.Done s t p pass lane slice index state)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 8 ∨ 16 ≤ d) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.regs .x19 (by simp [FillCompress.loopRegs])]
  have sub : Region.Sub ⟨off (s.gpr .x19) d, 8⟩ ⟨s.gpr .x19, 272⟩ := Offset.sub_base _ bound
  exact done.frame.readW (r := ⟨off (s.gpr .x19) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [VG.Proof.Argon2.AArch64.RandomSource.writes, AddressCache.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.cache.layout.frameWork.sub_left sub
    · exact h.cache.layout.frameStack.sub_left sub
    · exact Offset.disjoint _ separate (by omega) (by decide)) (by decide)

end VG.Proof.Argon2.AArch64.RandomSource
end

/-! Merged from `Proof.Argon2.AArch64.FillCacheInvariant`. -/
section
/-! The cell update does not disturb the cached independent-address block. -/

namespace VG.Proof.Argon2.AArch64.RandomSource

open VG VG.AArch64 VG.Spec.Argon2

theorem Ready.after_fill {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : VG.Proof.Argon2.AArch64.RandomSource.Ready p pass lane slice index old s) (done : FillKernel.Done s t p pass lane slice index) :
    VG.Proof.Argon2.AArch64.RandomSource.Ready p pass lane slice index old t := by
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
    (done : RandomSource.Done s t p pass lane slice index state) : Frame (VG.Proof.Argon2.AArch64.FillBlock.writes s p) s.mem t.mem := by
  apply done.frame.sub
  intro r hr
  simp only [RandomSource.writes, AddressCache.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, by simp [VG.Proof.Argon2.AArch64.FillBlock.writes], fun _ h => h⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.AArch64.FillBlock.writes], fun _ h => h⟩
  · exact ⟨⟨off (s.gpr .x19) 8, 16⟩, by simp [VG.Proof.Argon2.AArch64.FillBlock.writes], Region.sub_prefix (by decide)⟩

theorem kernel_frame {s t : State} {p : Params} {pass lane slice index : Nat}
    (ready : FillKernel.Ready p pass lane slice index s) (done : FillKernel.Done s t p pass lane slice index) :
    Frame (VG.Proof.Argon2.AArch64.FillBlock.writes s p) s.mem t.mem := by
  apply done.frame.sub
  intro r hr
  simp only [FillKernel.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [VG.Proof.Argon2.AArch64.FillBlock.writes], FillKernel.cell_sub p _ ready.bounds.lanesPositive ready.bounds.laneBound
      (Proof.Argon2.column_lt p ready.bounds.lanesPositive ready.bounds.sliceBound ready.bounds.indexBound)⟩
  · exact ⟨⟨AddressCalls.work s, 8192⟩, by simp [VG.Proof.Argon2.AArch64.FillBlock.writes], Region.sub_prefix (by decide)⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.AArch64.FillBlock.writes], fun _ h => h⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.AArch64.FillBlock.writes], Offset.sub _ (d := 16) (n := 8) (e := 8) (k := 16)
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
  frame : Frame (VG.Proof.Argon2.AArch64.FillBlock.writes s p) s.mem t.mem
  sp : t.sp = s.sp

theorem code_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillBlock.code s (VG.Proof.Argon2.AArch64.FillBlock.Done s · p pass lane slice index state) := by
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
  · have frame := VG.Proof.Argon2.AArch64.FillBlock.kernel_frame ready.filling done
    rw [VG.Proof.Argon2.AArch64.FillBlock.writes, baseA, workA, source.sp,
      source.regs .x19 (by simp [FillCompress.loopRegs])] at frame
    exact (VG.Proof.Argon2.AArch64.FillBlock.source_frame source).trans frame

end VG.Proof.Argon2.AArch64.FillBlock

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FinalCall`. -/
section

/-! The final H′ call accepts a complete reduced block and a public tag length. -/

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

theorem hPrime_call_hyps (len : Nat) (s : State) (h : VG.Proof.Argon2.AArch64.FinalCall.CallReady len s)
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

theorem hPrime_depth (v : HPrime.Backend) : (VG.Impl.Argon2.AArch64.HPrime.code v.hash).aarch64Depth = 1 := by
  simp only [VG.Impl.Argon2.AArch64.HPrime.code, Impl.Argon2.AArch64.HPrime.first,
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
    (len : Nat) (s : State) (h : VG.Proof.Argon2.AArch64.FinalCall.CallReady len s) (inputLength : s.gpr .x1 = 1024)
    (outputLength : s.gpr .x3 = BitVec.ofNat 64 len) :
    WP isa (.call name (VG.Impl.Argon2.AArch64.HPrime.code v.hash)) s (VG.Proof.Argon2.AArch64.FinalCall.Called len s) := by
  obtain ⟨pre, cover, writes⟩ := VG.Proof.Argon2.AArch64.FinalCall.hPrime_call_hyps len s h inputLength outputLength
  refine WP.callF (k := HPrime.localContract) (HPrime.code_correct v) pre cover writes ?_
    (by rw [VG.Proof.Argon2.AArch64.FinalCall.hPrime_depth]; decide)
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
  · simpa only [VG.Proof.Argon2.AArch64.FinalCall.hPrime_depth, Nat.mul_one, List.cons_append, List.nil_append] using frame

end VG.Proof.Argon2.AArch64.FinalCall

end
