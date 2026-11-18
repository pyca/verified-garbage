module

import VerifiedGarbage.Proof.Argon2.References
import VerifiedGarbage.Proof.Argon2.IterationsIndices
public import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetupCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Argon2.AArch64.InitialLit
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Verified
import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetup
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Correct
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT
meta import VerifiedGarbage.Proof.Argon2.References
meta import VerifiedGarbage.Proof.Argon2.IterationsIndices
meta import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetupCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Argon2.AArch64.InitialLit
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Verified
meta import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetup
meta import VerifiedGarbage.Proof.Argon2.Dimensions
meta import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Correct
meta import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Argon2.AArch64.InitialBody
public import VerifiedGarbage.Proof.Argon2.AArch64.InitFill
import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetupPrepare
public import VerifiedGarbage.Impl.Argon2.AArch64.Initial
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Backend
public import VerifiedGarbage.Proof.Argon2.Initial
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Update
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Init
import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Lit
import VerifiedGarbage.Proof.Argon2.AArch64.Instructions
import VerifiedGarbage.Proof.Argon2.HPrime
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Impl.Argon2.AArch64.InitialBody
meta import VerifiedGarbage.Proof.Argon2.AArch64.InitFill
meta import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetupPrepare
meta import VerifiedGarbage.Impl.Argon2.AArch64.Initial
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Backend
meta import VerifiedGarbage.Proof.Argon2.Initial
meta import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Update
meta import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Init
meta import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Lit
meta import VerifiedGarbage.Proof.Argon2.AArch64.Instructions
meta import VerifiedGarbage.Proof.Argon2.HPrime
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Block

/-! ### `Argon2.AArch64.InitialBodyState`, which this module and modules that import it used -/

section

/-! ### `Argon2.AArch64.InitialBody`, which this module and modules that import it used -/

section

/-! ### `Argon2.AArch64.Initial`, which only this module used -/

section

/-! ### `Argon2.AArch64.InitialStart`, which only this module used -/

section

/-! ### `Argon2.AArch64.InitialArgs`, which only this module used -/

section

/-! Argument handling for the H₀ streaming hash. -/

@[expose] public section

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
    WP isa (.block (lengthArgs offset)) s (LengthArgs s offset) := by
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
    WP isa (.block (inputArgs offset)) s (fun t => InputArgs s t offset) := by
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

end


@[expose] public section

section

section

/-! # Writing and reading the six words of the H₀ header -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt)

def headerValue (s : State) (j : Nat) : BitVec 32 :=
  if j = 4 then 0x13 else (wordAt s (headerSource j)).setWidth 32

def headerMem (s : State) : Nat → Mem
  | 0 => s.mem
  | n + 1 => (headerMem s n).writeW (s.gpr .x24 + BitVec.ofNat 64 (768 + 4 * n))
    (headerValue s n)

theorem headerSource_slot (j : Nat) : headerSource j ∈ slots := by
  unfold headerSource
  split <;> (try split) <;> (try split) <;> (try split) <;> decide

theorem headerSource_bound (j : Nat) : headerSource j + 8 ≤ 272 := by
  unfold headerSource
  split <;> (try split) <;> (try split) <;> (try split) <;> decide

theorem headerValue_keeps {s t : State} (h : Space s) (k : Keeps s t) (j : Nat) :
    headerValue t j = headerValue s j := by
  unfold headerValue
  rw [h.word_keeps k _ (headerSource_bound j)]

theorem headerMem_frame (s : State) (n : Nat) (hn : n ≤ 6) :
    Frame [⟨s.gpr .x24 + 768, 24⟩] s.mem (headerMem s n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih =>
    exact (ih (by omega_arith)).writeW (List.mem_singleton_self _) _
      (by
        rw [show (768 : Addr) = BitVec.ofNat 64 768 from rfl, BitVec.ofNat_add,
          ← BitVec.add_assoc]
        exact Offset.contains_base _ (by omega_arith) (by omega_arith))

theorem headerMem_read (s : State) (n j : Nat) (hn : n ≤ 6) (hj : j < n) :
    (headerMem s n).readW (s.gpr .x24 + BitVec.ofNat 64 (768 + 4 * j)) 32 =
      headerValue s j := by
  induction n with
  | zero => omega_arith
  | succ n ih =>
    unfold headerMem
    by_cases he : j = n
    · subst j; exact Mem.readW_writeW_self32 ..
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith : 768 + 4 * j + 4 ≤ 768 + 4 * n ∨
        768 + 4 * n + 4 ≤ 768 + 4 * j) (by omega_arith) (by omega_arith)) (by decide)]
      exact ih (by omega_arith) (by omega_arith)

theorem headerMem_bytes (s : State) :
    bytesAt (headerMem s 6) (s.gpr .x24 + 768) 24 =
      (List.range 6).flatMap (fun j => Spec.Blake2.wordBytes (headerValue s j)) := by
  rw [show 24 = 32 / 8 * 6 from rfl, Proof.Blake2.bytesAt_words (w := 32)]
  simp only [List.flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j hj
  rw [← Proof.Blake2.wordBytes_readW _ _ (Or.inl rfl)]
  rw [show (768 : Addr) = BitVec.ofNat 64 768 from rfl, BitVec.add_assoc,
    ← BitVec.ofNat_add, headerMem_read s 6 j (by decide) (List.mem_range.mp hj)]

theorem headerSlot_ok (s : State) (j : Nat) (hj : j < 6) (h : Space s) :
    WP isa (.block (headerSlot j)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .x24 + BitVec.ofNat 64 (768 + 4 * j)) (headerValue s j) ∧
      Keeps s t := by
  obtain hw := h.write (768 + 4 * j) 4 (by omega_arith)
  have finish (t : State) (hm : t.mem = s.mem.writeW
      (s.gpr .x24 + BitVec.ofNat 64 (768 + 4 * j)) (headerValue s j))
      (regs : ∀ r, r ≠ .x8 → t.gpr r = s.gpr r)
      (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp) :
      t.mem = s.mem.writeW (s.gpr .x24 + BitVec.ofNat 64 (768 + 4 * j)) (headerValue s j) ∧
        Keeps s t := by
    refine ⟨hm, fun r hr _ _ => regs r ?_, sp, rd, wr, ?_⟩
    · simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rw [hm]
      exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
        (Offset.contains_base _ (by omega_arith) (by omega_arith))
  unfold headerSlot
  split
  · next he =>
    subst j
    have hwLiteral : InRegions s.wr (s.gpr .x24 + 784#64) 4 := hw
    apply WP.of_runBlock
    simp only [Impl.Argon2.AArch64.Instructions.imm,
      Impl.Argon2.AArch64.Instructions.store32, show 19 < 65536 from by decide,
      List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.store, addr,
      Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceAdd, Nat.reduceLT, Nat.reduceMod,
      BitVec.shiftLeft_zero, show (19#16).setWidth 64 = 19#64 from rfl,
      RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
      hwLiteral, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false, and_self,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, ?_⟩
    constructor
    · intro r hr _ _
      obtain hn : r ≠ .x8 := by
        simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [RegUpd.gpr_write, hn, ite_false]
    · simp only [RegUpd.sp_write]
    · rfl
    · rfl
    · change Frame [⟨s.gpr .x24, 832⟩, below s.sp 16] s.mem
        (s.mem.writeW (s.gpr .x24 + 784) (19#32))
      exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
        (Offset.contains_base _ (d := 784) (n := 4) (by decide : 784 + 4 ≤ 832) (by decide))
  · next he =>
    obtain align : headerSource j % 8 = 0 := by
      unfold headerSource
      split <;> (try split) <;> (try split) <;> (try split) <;> decide
    refine (headerWord_ok s _ _ align (by have := headerSource_bound j; omega_arith)
      (by omega_arith) (by omega_arith) (h.readable _ (headerSource_slot j)) hw).mono ?_
    rintro t ⟨hm, regs, rd, wr, sp⟩
    exact finish t (by simpa only [headerValue, he, ite_false, wordAt] using hm) regs rd wr sp

theorem headerWords_ok (s : State) (n : Nat) (hn : n ≤ 6) (h : Space s) :
    WP isa (.block ((List.range n).flatMap headerSlot)) s fun t =>
      t.mem = headerMem s n ∧ Keeps s t := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨rfl, fun _ _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine (ih (by omega_arith)).mono ?_
    rintro u ⟨hu, ku⟩
    refine (headerSlot_ok u n (by omega_arith) (h.keeps ku)).mono ?_
    rintro t ⟨ht, kt⟩
    refine ⟨?_, ku.trans kt⟩
    rw [ht, ku.x24, headerValue_keeps h ku, hu]
    rfl

end VG.Proof.Argon2.AArch64.Initial

end

/-! Merged from `Proof.Argon2.AArch64.InitialPrep`. -/
section
/-! # H₀: preserving the stack across input argument preparation -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt)

theorem LengthArgs.keeps {s t : State} {offset : Nat} (h : LengthArgs s offset t) :
    Keeps s t := by
  refine ⟨fun r hr _ h22 => h.other r ?_, h.sp, h.rd, h.wr, ?_⟩
  · simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, not_false_eq_true, ne_eq, not_true_eq_false]
  · rw [h.mem]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide) (by decide))

theorem InputArgs.keeps {s t : State} {offset : Nat} (h : InputArgs s t offset) :
    Keeps s t := by
  refine ⟨fun r hr h20 _ => h.other r ?_, h.sp, h.rd, h.wr, ?_⟩
  · simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, not_false_eq_true, ne_eq, not_true_eq_false]
  · rw [h.mem]; exact Frame.refl _ _

theorem LengthArgs.prefix {s t : State} {offset : Nat} (h : LengthArgs s offset t) :
    bytesAt t.mem (s.gpr .x24 + 792) 4 = Spec.Argon2.le32 (wordAt s offset).toNat := by
  rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (Or.inl rfl), h.mem,
    Mem.readW_writeW_self32]
  rfl

theorem LengthArgs.repr {s t : State} {offset : Nat} (h : LengthArgs s offset t)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Spec.Blake2.Repr Spec.Blake2.b h0 s.mem (s.gpr .x24) d) :
    Spec.Blake2.Repr Spec.Blake2.b h0 t.mem (t.gpr .x24) d := by
  rw [h.keeps.x24]
  apply Proof.Blake2.AArch64.Stream.repr_congr Proof.Blake2.AArch64.Stream.okB
    (mem := s.mem) (h := repr)
  intro i hi
  obtain f : Frame [⟨s.gpr .x24 + 792, 4⟩] s.mem t.mem := by
    rw [h.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  apply f.bytes (R := ⟨s.gpr .x24, 192⟩) _ (show (192 : Nat) ≤ 2 ^ 64 from by decide) hi
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact Offset.base_disjoint _ (by decide) (by decide)

theorem InputArgs.repr {s t : State} {offset : Nat} (h : InputArgs s t offset)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Spec.Blake2.Repr Spec.Blake2.b h0 s.mem (s.gpr .x24) d) :
    Spec.Blake2.Repr Spec.Blake2.b h0 t.mem (t.gpr .x24) d := by
  rw [h.keeps.x24, h.mem]; exact repr

theorem addCount_ok (s : State) :
    WP isa (.block (Impl.Argon2.AArch64.Instructions.add .x20 .x22)) s fun t =>
      t.gpr .x20 = s.gpr .x20 + s.gpr .x22 ∧ t.mem = s.mem ∧ Keeps s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.Instructions.add, Impl.Argon2.AArch64.Instructions.mark, Impl.Argon2.AArch64.Instructions.mov,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    BitVec.setWidth_eq, show 0 < 4096 from by decide, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, fun r hr h20 _ => ?_, rfl, rfl, rfl, Frame.refl _ _⟩
  obtain hn : r ≠ .x15 := by
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [RegUpd.gpr_write, h20, hn, ite_false]

end VG.Proof.Argon2.AArch64.Initial
end

/-! # H₀: absorb a length-prefixed byte-string input -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)
open VG.Proof.Argon2 (appendInput)

theorem slots_aligned (d : Nat) (hd : d ∈ slots) : d % 8 = 0 := by
  obtain all : ∀ d ∈ slots, d % 8 = 0 := by decide
  exact all d hd

structure InputReady (s : State) (po lo : Nat) : Prop where
  space : Space s
  pointerSlot : po ∈ slots
  lengthSlot : lo ∈ slots
  pointerBound : po + 8 ≤ 272
  lengthBound : lo + 8 ≤ 272
  length : (wordAt s lo).toNat < 2 ^ 32
  cover : Covers [inputRegion s po lo] (s.rd ++ s.wr)
  work : (inputRegion s po lo).Disjoint ⟨s.gpr .x24, 16384⟩
  stack : (inputRegion s po lo).Disjoint (below (s.sp) 16)

theorem InputReady.keeps {s t : State} {po lo : Nat} (h : InputReady s po lo)
    (k : Keeps s t) : InputReady t po lo := by
  obtain reg := h.space.input_keeps k po lo h.pointerBound h.lengthBound
  refine ⟨h.space.keeps k, h.pointerSlot, h.lengthSlot, h.pointerBound, h.lengthBound,
    ?_, ?_, ?_, ?_⟩
  · rw [h.space.word_keeps k lo h.lengthBound]; exact h.length
  · rw [reg, k.rd, k.wr]; exact h.cover
  · rw [reg, k.x24]; exact h.work
  · rw [reg, k.sp]; exact h.stack

def inputBytes (s : State) (po lo : Nat) : List Byte :=
  bytesAt s.mem (wordAt s po) (wordAt s lo).toNat

theorem inputBytes_length (s : State) (po lo : Nat) :
    (inputBytes s po lo).length = (wordAt s lo).toNat := by
  simp only [inputBytes, bytesAt, List.length_map, List.length_range]

theorem InputReady.bytes_keeps {s t : State} {po lo : Nat} (h : InputReady s po lo)
    (k : Keeps s t) : inputBytes t po lo = inputBytes s po lo := by
  unfold inputBytes
  rw [h.space.word_keeps k po h.pointerBound, h.space.word_keeps k lo h.lengthBound]
  exact k.bytes (inputRegion s po lo) h.work h.stack (by
    change (wordAt s lo).toNat ≤ 2 ^ 64
    exact Nat.le_of_lt (wordAt s lo).isLt)

theorem absorb_ok (v : HPrime.Backend) (s : State) (po lo : Nat)
    (h : InputReady s po lo) (d : List Byte)
    (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (s.gpr .x24) d)
    (count : s.gpr .x20 = BitVec.ofNat 64 d.length)
    (bound : d.length + 4 + (wordAt s lo).toNat < 2 ^ 64) :
    WP isa (absorb v.hash po lo) s fun t =>
      Repr b (Spec.Blake2.init b 64 0) t.mem (t.gpr .x24)
        (appendInput d (inputBytes s po lo)) ∧
      t.gpr .x20 = BitVec.ofNat 64 (appendInput d (inputBytes s po lo)).length ∧ Keeps s t := by
  unfold absorb
  refine WP.seq ((lengthArgs_ok s lo (slots_aligned lo h.lengthSlot) (by have := h.lengthBound; omega_arith) (h.space.readable lo h.lengthSlot)
    (by simpa using h.space.write 792 4 (by decide))).mono ?_)
  intro a ha
  have ka := ha.keeps
  obtain hA := h.keeps ka
  obtain lenA : (a.gpr .x3).toNat = 4 := by rw [ha.size]; rfl
  obtain dataA : Covers [⟨a.gpr .x2, (a.gpr .x3).toNat⟩] (a.rd ++ a.wr) := by
    rw [ha.pointer, lenA, ka.x24.symm]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨a.gpr .x24, 16384⟩, List.mem_append_right _ hA.space.work,
      792, rfl, by change 792 + 4 ≤ 16384; decide⟩
  obtain dsA : (⟨a.gpr .x2, (a.gpr .x3).toNat⟩ : Region).Disjoint ⟨a.gpr .x24, 192⟩ := by
    rw [ha.pointer, lenA, ka.x24]
    exact (Offset.base_disjoint _ (by decide) (by decide)).symm
  obtain dwA : (⟨a.gpr .x2, (a.gpr .x3).toNat⟩ : Region).Disjoint ⟨a.gpr .x24 + 192, 576⟩ := by
    rw [ha.pointer, lenA, ka.x24]
    exact Offset.disjoint _ (by decide) (by decide) (by decide)
  obtain sdA : (below (a.sp) 16).Disjoint ⟨a.gpr .x2, (a.gpr .x3).toNat⟩ := by
    rw [ha.pointer, lenA, ka.x24.symm]
    exact hA.space.stackWork.sub_right (Offset.sub_base _ (by decide))
  refine WP.seq ((HPrime.update_ok v a _ d (ha.repr _ _ repr)
    (ha.count.trans count) (by rw [lenA]; omega_arith) hA.space.stackMinimum hA.space.work dataA dsA dwA
    hA.space.stackWork sdA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, spU, frameU⟩
  obtain ku : Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, spU, HPrime.update_frame _ _ frameU⟩
  obtain ksu := ka.trans ku
  obtain hU := h.keeps ksu
  obtain prefixA : bytesAt a.mem (a.gpr .x2) (a.gpr .x3).toNat =
      Spec.Argon2.le32 (wordAt s lo).toNat := by rw [ha.pointer, lenA]; exact ha.prefix
  obtain r12U : u.gpr .x20 = s.gpr .x20 :=
    (regsU _ (by decide) (by decide)).trans (ha.other _ (by decide))
  obtain r14U : u.gpr .x22 = wordAt s lo := (regsU _ (by decide) (by decide)).trans ha.length
  refine WP.seq ((inputArgs_ok u po (slots_aligned po h.pointerSlot) (by have := h.pointerBound; omega_arith) (hU.space.readable po h.pointerSlot)).mono ?_)
  intro x hx
  have kux := hx.keeps
  obtain ksx := ksu.trans kux
  obtain hX := h.keeps ksx
  obtain srcX : x.gpr .x2 = wordAt s po :=
    hx.pointer.trans (h.space.word_keeps ksu po h.pointerBound)
  obtain lenX : x.gpr .x3 = wordAt s lo := hx.length.trans r14U
  obtain r14X : x.gpr .x22 = wordAt s lo :=
    (hx.other _ (by decide)).trans r14U
  obtain reprX : Repr b (Spec.Blake2.init b 64 0) x.mem (x.gpr .x24)
      (d ++ Spec.Argon2.le32 (wordAt s lo).toNat) := by
    apply hx.repr
    rw [ku.x24]
    simpa only [prefixA] using reprU
  obtain prefixLen : (d ++ Spec.Argon2.le32 (wordAt s lo).toNat).length = d.length + 4 := by
    rw [List.length_append, Proof.Argon2.le32_length]
  obtain countX : x.gpr .x1 = BitVec.ofNat 64 (d ++ Spec.Argon2.le32 (wordAt s lo).toNat).length := by
    rw [hx.count, r12U, count, prefixLen, BitVec.ofNat_add]; rfl
  obtain coverX : Covers [⟨x.gpr .x2, (x.gpr .x3).toNat⟩] (x.rd ++ x.wr) := by
    rw [srcX, lenX, ksx.rd, ksx.wr]
    exact h.cover
  obtain dsX : (⟨x.gpr .x2, (x.gpr .x3).toNat⟩ : Region).Disjoint ⟨x.gpr .x24, 192⟩ := by
    rw [srcX, lenX, ksx.x24]
    exact h.work.sub_right (Region.sub_prefix (by decide))
  obtain dwX : (⟨x.gpr .x2, (x.gpr .x3).toNat⟩ : Region).Disjoint ⟨x.gpr .x24 + 192, 576⟩ := by
    rw [srcX, lenX, ksx.x24]
    exact h.work.sub_right (Offset.sub_base _ (by decide))
  obtain sdX : (below (x.sp) 16).Disjoint ⟨x.gpr .x2, (x.gpr .x3).toNat⟩ := by
    rw [srcX, lenX, ksx.sp]; exact h.stack.symm
  refine WP.seq ((HPrime.update_ok v x _ _ reprX countX
    (by rw [prefixLen, lenX]; exact bound) hX.space.stackMinimum hX.space.work coverX dsX dwX hX.space.stackWork sdX).mono ?_)
  rintro y ⟨reprY, regsY, rdY, wrY, spY, frameY⟩
  obtain ky : Keeps x y := Keeps.of_hash ⟨regsY, rdY, wrY, spY, HPrime.update_frame _ _ frameY⟩
  obtain ksy := ksx.trans ky
  obtain r12Y : y.gpr .x20 = BitVec.ofNat 64 (d.length + 4) := by
    rw [regsY _ (by decide) (by decide), hx.total, r12U, count, BitVec.ofNat_add]; rfl
  obtain r14Y : y.gpr .x22 = wordAt s lo := (regsY _ (by decide) (by decide)).trans r14X
  obtain bytesX : bytesAt x.mem (x.gpr .x2) (x.gpr .x3).toNat = inputBytes s po lo := by
    rw [srcX, lenX]
    exact ksx.bytes (inputRegion s po lo) h.work h.stack (Nat.le_of_lt (wordAt s lo).isLt)
  refine (addCount_ok y).mono ?_
  rintro t ⟨ht12, hm, kt⟩
  refine ⟨?_, ?_, ksy.trans kt⟩
  · rw [kt.x24, hm, ky.x24]
    simpa only [appendInput, inputBytes_length, bytesX] using reprY
  · have hw : BitVec.ofNat 64 (wordAt s lo).toNat = wordAt s lo := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [ht12, r12Y, r14Y, ← hw, ← BitVec.ofNat_add,
      Proof.Argon2.appendInput_length, inputBytes_length]

end VG.Proof.Argon2.AArch64.Initial

end

/-! # H₀: initialize BLAKE2b and absorb the public parameter header -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)

def headerBytes (s : State) : List Byte :=
  (List.range 6).flatMap fun j => Spec.Blake2.wordBytes (headerValue s j)

theorem headerBytes_keeps {s t : State} (h : Space s) (k : Keeps s t) :
    headerBytes t = headerBytes s := by
  unfold headerBytes
  simp only [List.flatMap]
  apply congrArg List.flatten
  exact List.map_congr_left fun j _ => congrArg Spec.Blake2.wordBytes (headerValue_keeps h k j)

theorem headerBytes_length (s : State) : (headerBytes s).length = 24 := by
  simp only [headerBytes, List.length_flatMap, Spec.Blake2.wordBytes, List.length_map,
    List.length_range]
  decide

theorem digestLength_ok (s : State) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.imm .x1 64].flatten) s fun t =>
      t.gpr .x1 = 64 ∧ t.mem = s.mem ∧ HPrime.Keeps s t := by
  refine (SegmentSetup.register_ok s .x1 64 (by decide)).mono ?_
  rintro t ⟨value, keeps⟩
  refine ⟨value, keeps.mem, fun r hr h30 => keeps.regs r ?_, keeps.rd, keeps.wr, keeps.sp, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [keeps.mem]; exact Frame.refl _ _

theorem initialCount_ok (s : State) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.imm .x20 24].flatten) s fun t =>
      t.gpr .x20 = 24 ∧ t.mem = s.mem ∧ Keeps s t := by
  refine (SegmentSetup.register_ok s .x20 24 (by decide)).mono ?_
  rintro t ⟨value, keeps⟩
  refine ⟨value, keeps.mem, fun r _ h20 _ => keeps.regs r ?_, keeps.sp, keeps.rd, keeps.wr, ?_⟩
  · simpa only [List.mem_singleton] using h20
  · rw [keeps.mem]; exact Frame.refl _ _

theorem start_ok (v : HPrime.Backend) (s : State) (h : Space s) :
    WP isa (start v.hash) s fun t =>
      Repr b (Spec.Blake2.init b 64 0) t.mem (t.gpr .x24) (headerBytes s) ∧
      t.gpr .x20 = 24 ∧ Keeps s t := by
  unfold start headerCode
  refine WP.seq ((digestLength_ok s).mono ?_)
  rintro a ⟨lenA, memA, ka'⟩
  obtain ka := Keeps.of_hash ka'
  obtain hA := h.keeps ka
  refine WP.seq ((HPrime.init_ok v a (by rw [lenA]; exact ⟨by decide, by decide⟩)
    hA.work).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, spU, frameU⟩
  obtain ku : Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, spU, HPrime.init_frame _ _ frameU⟩
  obtain ksu := ka.trans ku
  obtain hU := h.keeps ksu
  refine WP.seq ((headerWords_ok u 6 (by decide) hU).mono ?_)
  rintro w ⟨memW, kw⟩
  obtain ksw := ksu.trans kw
  obtain hW := h.keeps ksw
  obtain reprW : Repr b (Spec.Blake2.init b 64 0) w.mem (w.gpr .x24) [] := by
    rw [kw.x24]
    apply Proof.Blake2.AArch64.Stream.repr_congr Proof.Blake2.AArch64.Stream.okB
      (mem := u.mem) (h := by simpa only [lenA, ku.x24, show (64 : BitVec 64).toNat = 64 from rfl] using reprU)
    intro i hi
    rw [memW]
    apply (headerMem_frame u 6 (by decide)).bytes (R := ⟨u.gpr .x24, 192⟩) _
      (show (192 : Nat) ≤ 2 ^ 64 from by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact Offset.base_disjoint _ (by decide) (by decide)
  obtain headW : bytesAt w.mem (w.gpr .x24 + 768) 24 = headerBytes s := by
    rw [kw.x24, memW, headerMem_bytes]
    exact headerBytes_keeps h ksu
  refine WP.seq ((HPrime.absorbFixed_ok v w _ 768 24 (by decide) hW.stackMinimum (by decide) (by decide)
    reprW hW.work hW.stackWork).mono ?_)
  rintro x ⟨reprX, kx'⟩
  obtain kx := Keeps.of_hash kx'
  obtain ksx := ksw.trans kx
  refine (initialCount_ok x).mono ?_
  rintro t ⟨countT, memT, kt⟩
  refine ⟨?_, countT, ksx.trans kt⟩
  rw [kt.x24, memT, kx.x24]
  simpa only [headW, show BitVec.ofNat 64 768 = (768 : Addr) from rfl] using reprX

end VG.Proof.Argon2.AArch64.Initial

end

end

/-! Merged from `Proof.Argon2.AArch64.InitialFinish`. -/

@[expose] public section

section
/-! # H₀: finalize BLAKE2b and copy the digest into the derivation frame -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)

structure Finished (s t : State) : Prop where
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x20 → r ≠ .x22 → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .x24, 832⟩, below (s.sp) 16, ⟨s.gpr .x19, 64⟩] s.mem t.mem

theorem finishCount_ok (s : State) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.mov .x1 .x20].flatten) s fun t =>
      t.gpr .x1 = s.gpr .x20 ∧ t.mem = s.mem ∧ HPrime.Keeps s t := by
  refine (Instructions.mov_ok s .x1 .x20).mono ?_
  rintro t ⟨value, keeps⟩
  refine ⟨value, keeps.mem, fun r hr _ => keeps.regs r ?_, keeps.rd, keeps.wr, keeps.sp, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [keeps.mem]; exact Frame.refl _ _

theorem finishOutput_ok (s : State) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.mov .x22 .x19,
      Impl.Argon2.AArch64.Instructions.imm .x8 64].flatten) s fun t =>
      t.gpr .x22 = s.gpr .x19 ∧ t.gpr .x8 = 64 ∧ t.mem = s.mem ∧ Keeps s t := by
  rw [List.flatten_cons, List.flatten_cons, List.flatten_nil,
    List.append_nil, WP.block_append_iff]
  refine (Instructions.mov_ok s .x22 .x19).mono ?_
  rintro a ⟨value, ka⟩
  obtain im := SegmentSetup.register_ok a .x8 64 (by decide)
  change WP isa (.block (Impl.Argon2.AArch64.Instructions.imm .x8 64)) a _ at im
  refine im.mono ?_
  rintro t ⟨count, kt⟩
  refine ⟨(kt.regs .x22 (by decide)).trans value, count, kt.mem.trans ka.mem,
    fun r hr _ h22 => ?_, kt.sp.trans ka.sp, kt.rd.trans ka.rd, kt.wr.trans ka.wr, ?_⟩
  · have h8 : r ≠ .x8 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (kt.regs r (by simpa only [List.mem_singleton] using h8)).trans
      (ka.regs r (by simpa only [List.mem_singleton] using h22))
  · rw [kt.mem, ka.mem]; exact Frame.refl _ _

theorem finish_ok (v : HPrime.Backend) (s : State) (h : Space s)
    (d : List Byte) (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (s.gpr .x24) d)
    (count : s.gpr .x20 = BitVec.ofNat 64 d.length) (bound : d.length < 2 ^ 64) :
    WP isa (finish v.hash) s fun t =>
      bytesAt t.mem (s.gpr .x19) 64 = Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) d ∧
      Finished s t := by
  unfold finish
  refine WP.seq ((finishCount_ok s).mono ?_)
  rintro a ⟨countA, memA, ka'⟩
  obtain ka := Keeps.of_hash ka'
  obtain hA := h.keeps ka
  obtain reprA : Repr b (Spec.Blake2.init b 64 0) a.mem (a.gpr .x24) d := by
    rw [memA, ka.x24]; exact repr
  refine WP.seq ((HPrime.finalize_ok v a _ d reprA (countA.trans count) bound
    hA.stackMinimum hA.work hA.stackWork).mono ?_)
  rintro u ⟨digestU, regsU, rdU, wrU, spU, frameU⟩
  obtain ku : Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, spU, HPrime.finalize_frame _ _ frameU⟩
  obtain ksu := ka.trans ku
  refine WP.seq ((finishOutput_ok u).mono ?_)
  rintro w ⟨dstW, countW, memW, kw⟩
  obtain ksw := ksu.trans kw
  obtain hW := h.keeps ksw
  obtain outW : ∀ i < 64, InRegions w.wr (w.gpr .x22 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [dstW, ← kw.x19]
    rcases hW.output with ⟨r, hr, hc⟩
    exact ⟨r, hr, hc.byte (by rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi] : i < 2 ^ 64)]; exact hi)⟩
  obtain sepW : (⟨w.gpr .x24 + 768, 64⟩ : Region).Disjoint ⟨w.gpr .x22, 64⟩ := by
    rw [dstW, ← kw.x19]
    exact (hW.frameWork.sub_left (Region.sub_prefix (by decide : 64 ≤ 272))).symm.sub_left
      (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))
  refine (HPrime.copy_ok w 64 (by decide) (by decide) countW hW.work outW sepW).mono ?_
  intro t ht
  obtain sourceLength : (bytesAt w.mem (w.gpr .x24 + 768) 64).length = 64 := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨?_, fun r hr h12 h14 => ?_, ht.sp.trans ksw.sp, ht.rd.trans ksw.rd, ht.wr.trans ksw.wr, ?_⟩
  · have dst : w.gpr .x22 = s.gpr .x19 := dstW.trans ksu.x19
    rw [ht.mem]
    conv => lhs; arg 2; rw [← dst]
    obtain copied := HPrime.bytesAt_writeBytes w.mem (w.gpr .x22)
      (bytesAt w.mem (w.gpr .x24 + 768) 64) (by rw [sourceLength]; decide)
    rw [sourceLength] at copied
    rw [copied, memW, kw.x24, ku.x24]
    exact digestU
  · have hrax : r ≠ .x8 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain hrcx : r ≠ .x3 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain hrdx : r ≠ .x2 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (ht.other r hrax hrcx hrdx h14).trans (ksw.regs r hr h12 h14)
  · apply Frame.trans (ksw.frame.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr.elim Or.inl (fun h => Or.inr (Or.inl h))))
    apply ht.frame.mono
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    rw [dstW, ksu.x19]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))

end VG.Proof.Argon2.AArch64.Initial
end

/-! # Correctness of H₀ for every verified BLAKE2b backend -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)
open VG.Proof.Argon2 (appendInput)

abbrev inputs : List (Nat × Nat) :=
  [(passwordOffset, passwordLenOffset), (saltOffset, saltLenOffset),
   (secretOffset, secretLenOffset), (adOffset, adLenOffset)]

def message (s : State) (ps : List (Nat × Nat)) (d : List Byte) : List Byte :=
  ps.foldl (fun m p => appendInput m (inputBytes s p.1 p.2)) d

def inputSize (s : State) (ps : List (Nat × Nat)) : Nat :=
  (ps.map fun p => 4 + (wordAt s p.2).toNat).sum

def remaining (h : VG.Impl.Argon2.AArch64.HPrime.Hash) : List (Nat × Nat) → Prog isa
  | [] => finish h
  | p :: ps => .seq (absorb h p.1 p.2) (remaining h ps)

theorem message_keeps {s t : State} (ps : List (Nat × Nat)) (d : List Byte)
    (ready : ∀ p ∈ ps, InputReady s p.1 p.2) (k : Keeps s t) :
    message t ps d = message s ps d := by
  induction ps generalizing d with
  | nil => rfl
  | cons p ps ih =>
    simp only [message, List.foldl_cons]
    rw [(ready p (by simp only [List.mem_cons, true_or])).bytes_keeps k]
    exact ih _ (fun q hq => ready q (List.mem_cons_of_mem p hq))

theorem inputSize_keeps {s t : State} (ps : List (Nat × Nat))
    (ready : ∀ p ∈ ps, InputReady s p.1 p.2) (k : Keeps s t) :
    inputSize t ps = inputSize s ps := by
  unfold inputSize
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [(ready p hp).space.word_keeps k p.2 (ready p hp).lengthBound]

theorem Finished.before {s u t : State} (k : Keeps s u) (f : Finished u t) : Finished s t := by
  refine ⟨fun r hr h12 h14 => (f.regs r hr h12 h14).trans (k.regs r hr h12 h14),
    f.sp.trans k.sp, f.rd.trans k.rd, f.wr.trans k.wr, ?_⟩
  apply (k.frame.mono ?_).trans
  · simpa only [k.x24, k.sp, k.x19] using f.frame
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    exact hr.elim Or.inl (fun h => Or.inr (Or.inl h))

theorem remaining_ok (v : HPrime.Backend) (ps : List (Nat × Nat))
    (s : State) (space : Space s) (ready : ∀ p ∈ ps, InputReady s p.1 p.2)
    (d : List Byte) (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (s.gpr .x24) d)
    (count : s.gpr .x20 = BitVec.ofNat 64 d.length)
    (bound : d.length + inputSize s ps < 2 ^ 64) :
    WP isa (remaining v.hash ps) s fun t =>
      bytesAt t.mem (s.gpr .x19) 64 =
        Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) (message s ps d) ∧ Finished s t := by
  induction ps generalizing s d with
  | nil =>
    exact finish_ok v s space d repr count (by simpa only [inputSize, List.map_nil,
      List.sum_nil, Nat.add_zero] using bound)
  | cons p ps ih =>
    obtain hp := ready p (by simp only [List.mem_cons, true_or])
    obtain tailReady : ∀ q ∈ ps, InputReady s q.1 q.2 := fun q hq =>
      ready q (List.mem_cons_of_mem p hq)
    have size : inputSize s (p :: ps) = 4 + (wordAt s p.2).toNat + inputSize s ps := rfl
    refine WP.seq ((absorb_ok v s p.1 p.2 hp d repr count (by rw [size] at bound; omega_using [bound])).mono ?_)
    rintro u ⟨reprU, countU, ku⟩
    refine (ih u (space.keeps ku) (fun q hq => (tailReady q hq).keeps ku)
      _ reprU countU ?_).mono ?_
    · rw [inputSize_keeps ps tailReady ku, Proof.Argon2.appendInput_length, inputBytes_length]
      rw [size] at bound; omega_using [bound]
    · rintro t ⟨digestT, ft⟩
      refine ⟨?_, ft.before ku⟩
      rw [ku.x19] at digestT
      rw [message_keeps ps _ tailReady ku] at digestT
      exact digestT

theorem code_ok (v : HPrime.Backend) (s : State) (space : Space s)
    (ready : ∀ p ∈ inputs, InputReady s p.1 p.2) :
    WP isa (code v.hash) s fun t =>
      bytesAt t.mem (s.gpr .x19) 64 =
        Spec.Argon2.H 64 (message s inputs (headerBytes s)) ∧ Finished s t := by
  change WP isa (.seq (start v.hash) (remaining v.hash inputs)) s _
  refine WP.seq ((start_ok v s space).mono ?_)
  rintro u ⟨reprU, countU, ku⟩
  obtain count : u.gpr .x20 = BitVec.ofNat 64 (headerBytes s).length := by
    rw [headerBytes_length]; exact countU
  obtain bound : (headerBytes s).length + inputSize s inputs < 2 ^ 64 := by
    obtain hp := (ready (passwordOffset, passwordLenOffset) (by decide)).length
    obtain hs := (ready (saltOffset, saltLenOffset) (by decide)).length
    obtain hk := (ready (secretOffset, secretLenOffset) (by decide)).length
    obtain ha := (ready (adOffset, adLenOffset) (by decide)).length
    simp only at hp hs hk ha
    rw [headerBytes_length]
    change 24 + (4 + (wordAt s passwordLenOffset).toNat +
      (4 + (wordAt s saltLenOffset).toNat + (4 + (wordAt s secretLenOffset).toNat +
      (4 + (wordAt s adLenOffset).toNat + 0)))) < 2 ^ 64
    omega_using [hp, hs, hk, ha]
  refine (remaining_ok v inputs u (space.keeps ku) (fun p hp => (ready p hp).keeps ku)
    _ reprU count (by rw [inputSize_keeps inputs ready ku]; exact bound)).mono ?_
  rintro t ⟨digestT, ft⟩
  refine ⟨?_, ft.before ku⟩
  rw [ku.x19, message_keeps inputs _ ready ku] at digestT
  rw [Proof.Argon2.H_stream, ← digestT]
  exact (List.take_of_length_le (by simp only [bytesAt, List.length_map, List.length_range,
    Nat.le_refl])).symm

/-- The public header is supplied by the enclosing argument-validation proof.
The byte-string contents remain unrestricted. -/
theorem initialHash_ok (v : HPrime.Backend) (s : State) (space : Space s)
    (ready : ∀ p ∈ inputs, InputReady s p.1 p.2) (p : Spec.Argon2.Params)
    (header : headerBytes s = Proof.Argon2.initialHeader p) :
    WP isa (code v.hash) s fun t =>
      bytesAt t.mem (s.gpr .x19) 64 = Spec.Argon2.initialHash p
        (inputBytes s passwordOffset passwordLenOffset) (inputBytes s saltOffset saltLenOffset)
        (inputBytes s secretOffset secretLenOffset) (inputBytes s adOffset adLenOffset) ∧
      Finished s t := by
  refine (code_ok v s space ready).mono ?_
  rintro t ⟨digest, frame⟩
  refine ⟨?_, frame⟩
  rw [header] at digest
  exact digest

end VG.Proof.Argon2.AArch64.Initial

end

end


/-! Merged from `Proof.Argon2.AArch64.InitialMetadata`. -/

@[expose] public section

section
/-! H₀ writes its digest into the frame while retaining all enclosing arguments. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64

theorem Finished.x19 {s t : State} (h : Finished s t) : t.gpr .x19 = s.gpr .x19 :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Finished.x24 {s t : State} (h : Finished s t) : t.gpr .x24 = s.gpr .x24 :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Finished.frame_word {s t : State} (h : Finished s t) (space : Space s)
    (d : Nat) (bound : d + 8 ≤ 272) (afterDigest : 64 ≤ d) : wordAt t d = wordAt s d := by
  unfold wordAt
  rw [h.x19]
  apply h.frame.readW (r := ⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩)
    (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact space.frameWork.sub_left (Offset.sub_base _ bound) |>.sub_right
      (Region.sub_prefix (by decide))
  · exact space.frameStack.sub_left (Offset.sub_base _ bound)
  · simpa only [BitVec.add_zero] using
      Offset.disjoint (s.gpr .x19) (d := d) (n := 8) (e := 0) (k := 64)
        (Or.inr afterDigest) (by omega_using [bound]) (by decide)

end VG.Proof.Argon2.AArch64.Initial
end

/-! Merged from `Proof.Argon2.AArch64.InitialBodyReady`. -/
section
/-! H₀ retains the allocation and parameter environment of complete derivation. -/

namespace VG.Proof.Argon2.AArch64.InitialBody

open VG VG.AArch64 VG.Spec.Argon2

theorem hashed_environment {s t : State} {p : Params} (h : InitFill.Ready p s) (space : Initial.Space s) (done : Initial.Finished s t) : FillSetup.Environment p t := by
  obtain base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word space 232 (by decide) (by decide)
  obtain work : AddressCalls.work t = AddressCalls.work s := done.frame_word space 248 (by decide) (by decide)
  have e := h.environment
  refine ⟨e.parameters, e.passesBound, e.layout.of_preserved done.x19 done.sp base work done.rd done.wr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [done.rd, done.wr, done.x19]; exact e.addressLayout.frameRead
    · rw [done.wr, work]; exact e.addressLayout.workWrite
    · rw [done.x19, work]; exact e.addressLayout.frameWork
    · rw [done.x19, done.sp]; exact e.addressLayout.frameStack
    · rw [done.sp, work]; exact e.addressLayout.stackWork
  · rw [done.rd, done.wr, done.x19]; exact e.reads
  · rw [done.wr, done.x19]; exact e.counterWrite
  · rw [done.wr, done.x19]; exact e.passWrite
  · rw [base, work]; exact e.matrixWork
  · exact (done.frame_word space 240 (by decide) (by decide)).trans e.blocksWord
  · exact (done.frame_word space 72 (by decide) (by decide)).trans e.passesWord
  · exact (done.frame_word space 112 (by decide) (by decide)).trans e.variantWord
  · exact (done.frame_word space 184 (by decide) (by decide)).trans e.lanesWord

theorem hashed_output {s t : State} {p : Params} (h : InitFill.Ready p s) (space : Initial.Space s) (done : Initial.Finished s t) : FinalOutput.Ready p t := by
  obtain base : ReductionState.matrix t = ReductionState.matrix s := done.frame_word space 232 (by decide) (by decide)
  obtain output : FinalOutput.output t = FinalOutput.output s := done.frame_word space 256 (by decide) (by decide)
  obtain work : FinalOutput.work t = FinalOutput.work s := done.frame_word space 248 (by decide) (by decide)
  refine ⟨(by rw [done.sp]; exact h.output.stackMinimum), h.output.positive, h.output.bound, ?_,
    (done.frame_word space 264 (by decide) (by decide)).trans h.output.tagWord,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [done.rd, done.wr, done.x19]; exact h.output.reads
  · rw [base, done.rd, done.wr]; exact h.output.input
  · rw [output, done.wr]; exact h.output.outputWrite
  · rw [work, done.wr]; exact h.output.workWrite
  · rw [base, work]; exact h.output.inputWork
  · rw [output, work]; exact h.output.outputWork
  · rw [done.sp, base]; exact h.output.stackInput
  · rw [done.sp, output]; exact h.output.stackOutput
  · rw [done.sp, work]; exact h.output.stackWork

theorem hashed_ready {s t : State} {p : Params} (h : InitFill.Ready p s)
    (space : Initial.Space s) (done : Initial.Finished s t) : InitFill.Ready p t := by
  obtain base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word space 232 (by decide) (by decide)
  obtain work : FinalOutput.work t = FinalOutput.work s := done.frame_word space 248 (by decide) (by decide)
  refine ⟨?_, hashed_environment h space done, hashed_output h space done, h.positive, ?_⟩
  · constructor
    · rw [base]
      exact h.initializing.space.same done.wr done.x19 done.x24 done.sp
    · rw [done.rd, done.wr, done.x19]; exact h.initializing.memoryRead
    · rw [done.rd, done.wr, done.x19]; exact h.initializing.lanesRead
    · rw [done.rd, done.wr, done.x19]; exact h.initializing.blocksRead
    · exact (done.frame_word space 232 (by decide) (by decide)).trans h.initializing.memoryWord |>.trans base.symm
    · exact (done.frame_word space 184 (by decide) (by decide)).trans h.initializing.lanesWord
    · exact (done.frame_word space 240 (by decide) (by decide)).trans h.initializing.blocksWord
    · exact (done.regs .x21 (by decide) (by decide) (by decide)).trans h.initializing.laneLength
  · rw [done.x24, work]; exact h.scratch

end VG.Proof.Argon2.AArch64.InitialBody
end

/-! H₀, initialization, every filling pass, and finalization agree with derive. -/

namespace VG.Proof.Argon2.AArch64.InitialBody

open VG VG.AArch64 VG.Spec.Argon2
open VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt)

structure Ready (p : Params) (s : State) : Prop where
  hashSpace : Initial.Space s
  inputs : ∀ input ∈ Initial.inputs, Initial.InputReady s input.1 input.2
  header : Initial.headerBytes s = Proof.Argon2.initialHeader p
  filling : InitFill.Ready p s

structure Done (s t : State) (p : Params) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen = derive p
    (Initial.inputBytes s passwordOffset passwordLenOffset)
    (Initial.inputBytes s saltOffset saltLenOffset)
    (Initial.inputBytes s secretOffset secretLenOffset)
    (Initial.inputBytes s adOffset adLenOffset)
  bp : t.gpr .x19 = s.gpr .x19
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (InitFill.writes s p) s.mem t.mem
  unused : ∀ r ∈ [Reg.x25, .x26, .x27, .x28], t.gpr r = s.gpr r

theorem hash_frame {s t : State} {p : Params} (h : InitFill.Ready p s) (done : Initial.Finished s t) :
    Frame (InitFill.writes s p) s.mem t.mem := by
  apply done.frame.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨FinalOutput.work s, 16384⟩, by simp [InitFill.writes], by
      rw [h.scratch]; exact Region.sub_prefix (by decide)⟩
  · exact ⟨below (s.sp) 16, by simp [InitFill.writes], below_sub (by decide) (by decide)⟩
  · exact ⟨⟨s.gpr .x19, 72⟩, by simp [InitFill.writes], Region.sub_prefix (by decide)⟩

theorem code_ok (v : HPrime.Backend) (name : String) (s : State) (p : Params) (h : Ready p s) :
    WP isa (Impl.Argon2.AArch64.InitialBody.code name v.hash) s (Done s · p) := by
  unfold Impl.Argon2.AArch64.InitialBody.code
  refine WP.seq ((Initial.initialHash_ok v s h.hashSpace h.inputs p h.header).mono ?_)
  rintro a ⟨digest, hashed⟩
  refine (InitFill.code_ok v name a p (hashed_ready h.filling h.hashSpace hashed)).mono ?_
  intro t filled
  obtain base : FillKernel.matrix a = FillKernel.matrix s := hashed.frame_word h.hashSpace 232 (by decide) (by decide)
  obtain work : FinalOutput.work a = FinalOutput.work s := hashed.frame_word h.hashSpace 248 (by decide) (by decide)
  obtain output : FinalOutput.output a = FinalOutput.output s := hashed.frame_word h.hashSpace 256 (by decide) (by decide)
  refine ⟨?_, filled.bp.trans hashed.x19, filled.sp.trans hashed.sp,
    filled.rd.trans hashed.rd, filled.wr.trans hashed.wr, ?_, ?_⟩
  · have result := filled.digest
    rw [output, hashed.x19, digest, InitFill.result_derive] at result
    exact result
  · have frame := filled.frame
    rw [InitFill.writes_eq s a p hashed.x19 hashed.sp base work output] at frame
    exact (hash_frame h.filling hashed).trans frame
  · intro r hr
    obtain facts : ∀ r ∈ [Reg.x25, .x26, .x27, .x28],
        r ∈ FillCompress.loopRegs ∧ r ≠ .x20 ∧ r ≠ .x22 := by decide
    obtain ⟨member, h20, h22⟩ := facts r hr
    exact (filled.unused r hr).trans (hashed.regs r member h20 h22)

end VG.Proof.Argon2.AArch64.InitialBody

end

end

/-! The complete body depends on the frame, allocation, and computed lane length. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.InitialBody

open VG VG.AArch64 VG.Spec.Argon2

structure SameFrame (s t : State) : Prop where
  bp : t.gpr .x19 = s.gpr .x19
  bx : t.gpr .x24 = s.gpr .x24
  sp : t.sp = s.sp
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem SameFrame.word {s t : State} (k : SameFrame s t) (d : Nat) :
    Initial.wordAt t d = Initial.wordAt s d := by
  unfold Initial.wordAt; rw [k.mem, k.bp]

theorem SameFrame.inputBytes {s t : State} (k : SameFrame s t) (po lo : Nat) :
    Initial.inputBytes t po lo = Initial.inputBytes s po lo := by
  unfold Initial.inputBytes; rw [k.word po, k.word lo, k.mem]

theorem SameFrame.hashSpace {s t : State} (k : SameFrame s t)
    (h : Initial.Space s) : Initial.Space t := by
  constructor
  · rw [k.sp]; exact h.stackMinimum
  · rw [k.bx, k.wr]; exact h.work
  · rw [k.sp, k.bx]; exact h.stackWork
  · rw [k.bp, k.bx]; exact h.frameWork
  · rw [k.bp, k.sp]; exact h.frameStack
  · rw [k.rd, k.wr, k.bp]; exact h.readable
  · rw [k.wr, k.bp]; exact h.output

theorem SameFrame.input {s t : State} (k : SameFrame s t) {po lo : Nat}
    (h : Initial.InputReady s po lo) : Initial.InputReady t po lo := by
  have word : ∀ d, Initial.wordAt t d = Initial.wordAt s d := by
    intro d; unfold Initial.wordAt; rw [k.mem, k.bp]
  have region : Initial.inputRegion t po lo = Initial.inputRegion s po lo := by
    unfold Initial.inputRegion; rw [word po, word lo]
  refine ⟨k.hashSpace h.space, h.pointerSlot, h.lengthSlot, h.pointerBound,
    h.lengthBound, ?_, ?_, ?_, ?_⟩
  · rw [word lo]; exact h.length
  · rw [region, k.rd, k.wr]; exact h.cover
  · rw [region, k.bx]; exact h.work
  · rw [region, k.sp]; exact h.stack

theorem SameFrame.output {s t : State} (k : SameFrame s t) {p : Params}
    (h : FinalOutput.Ready p s) : FinalOutput.Ready p t := by
  have base : ReductionState.matrix t = ReductionState.matrix s := by
    unfold ReductionState.matrix; rw [k.mem, k.bp]
  have work : FinalOutput.work t = FinalOutput.work s := by
    unfold FinalOutput.work; rw [k.mem, k.bp]
  have output : FinalOutput.output t = FinalOutput.output s := by
    unfold FinalOutput.output; rw [k.mem, k.bp]
  refine ⟨by rw [k.sp]; exact h.stackMinimum, h.positive, h.bound, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k.rd, k.wr, k.bp]; exact h.reads
  · rw [k.mem, k.bp]; exact h.tagWord
  · rw [base, k.rd, k.wr]; exact h.input
  · rw [output, k.wr]; exact h.outputWrite
  · rw [work, k.wr]; exact h.workWrite
  · rw [base, work]; exact h.inputWork
  · rw [output, work]; exact h.outputWork
  · rw [k.sp, base]; exact h.stackInput
  · rw [k.sp, output]; exact h.stackOutput
  · rw [k.sp, work]; exact h.stackWork

theorem SameFrame.filling {s t : State} (k : SameFrame s t) {p : Params}
    (h : InitFill.Ready p s) (laneLength : t.gpr .x21 = BitVec.ofNat 64 p.laneLen) :
    InitFill.Ready p t := by
  have base : FillKernel.matrix t = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [k.mem, k.bp]
  have work : FinalOutput.work t = FinalOutput.work s := by
    unfold FinalOutput.work; rw [k.mem, k.bp]
  refine ⟨?_, h.environment.of_state k.bp k.sp k.mem k.rd k.wr,
    k.output h.output, h.positive, ?_⟩
  · constructor
    · rw [base]; exact h.initializing.space.same k.wr k.bp k.bx k.sp
    · rw [k.rd, k.wr, k.bp]; exact h.initializing.memoryRead
    · rw [k.rd, k.wr, k.bp]; exact h.initializing.lanesRead
    · rw [k.rd, k.wr, k.bp]; exact h.initializing.blocksRead
    · unfold Initial.wordAt; rw [k.mem, k.bp, base]; exact h.initializing.memoryWord
    · unfold Initial.wordAt; rw [k.mem, k.bp]; exact h.initializing.lanesWord
    · unfold Initial.wordAt; rw [k.mem, k.bp]; exact h.initializing.blocksWord
    · exact laneLength
  · rw [k.bx, work]; exact h.scratch

theorem Ready.of_state {s t : State} {p : Params} (h : Ready p s)
    (k : SameFrame s t) (laneLength : t.gpr .x21 = BitVec.ofNat 64 p.laneLen) : Ready p t := by
  refine ⟨k.hashSpace h.hashSpace, fun input hi => k.input (h.inputs input hi), ?_,
    k.filling h.filling laneLength⟩
  have header : Initial.headerBytes t = Initial.headerBytes s := by
    unfold Initial.headerBytes
    simp only [Initial.headerValue, Initial.wordAt, k.mem, k.bp]
  exact header.trans h.header

end VG.Proof.Argon2.AArch64.InitialBody

end

end

/-! Merged from `Proof.Argon2.AArch64.InitialCTState`. -/

@[expose] public section

section
/-! Merged from `Proof.Argon2.AArch64.InitialBlocksCT`. -/
section
/-! # Constant time of H₀ header and input argument preparation

Only frame and scratch addresses affect these blocks' execution traces.
The relational proof of the complete derivation additionally tracks public
lengths and pointers across its BLAKE2b calls.
-/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial

def AgreeBases (s t : State) : Prop := s.sp = t.sp ∧ s.gpr .x19 = t.gpr .x19 ∧ s.gpr .x24 = t.gpr .x24

theorem agreeBases_taint {s t : State} (h : AgreeBases s t) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x19, .x24]) s t := by
  refine ⟨h.1, ?_⟩
  intro r hr
  simp only [Taint.ofRegs, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.2.1
  · exact h.2.2

theorem header_rel : RelCT isa AgreeBases headerCode (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.x19, .x24])
    (fun _ _ h => agreeBases_taint h) (by taint_decide)

theorem lengthArgs_rel (offset : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs [.x19, .x24])
      (.block (lengthArgs offset)) hint).isSome = true) :
    RelCT isa AgreeBases (.block (lengthArgs offset)) (fun _ _ => True) := by
  obtain ⟨_, check⟩ := ct
  exact RelCT.taint (A := taint) (Taint.ofRegs [.x19, .x24])
    (fun _ _ h => agreeBases_taint h) check

theorem inputArgs_rel (offset : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs [.x19])
      (.block (inputArgs offset)) hint).isSome = true) :
    RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x19 = t.gpr .x19)
      (.block (inputArgs offset)) (fun _ _ => True) := by
  obtain ⟨_, check⟩ := ct
  exact RelCT.taint (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.1, by
      intro r hr; simp only [Taint.ofRegs, RegSet.mem_ofList, List.mem_singleton] at hr; subst r; exact h.2⟩) check

end VG.Proof.Argon2.AArch64.Initial
end

/-! Public input metadata survives every hash call without relating input bytes. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64

structure Ready (s : State) : Prop where
  space : Space s
  inputs : ∀ input ∈ inputs, InputReady s input.1 input.2

theorem Ready.keeps {s t : State} (h : Ready s) (k : Keeps s t) : Ready t :=
  ⟨h.space.keeps k, fun p hp => (h.inputs p hp).keeps k⟩

structure Related (s t : State) : Prop where
  left : Ready s
  right : Ready t
  bp : s.gpr .x19 = t.gpr .x19
  bx : s.gpr .x24 = t.gpr .x24
  sp : s.sp = t.sp
  words : ∀ d ∈ slots, wordAt s d = wordAt t d

theorem Related.keeps {s₁ s₂ t₁ t₂ : State} (h : Related s₁ s₂)
    (k₁ : Keeps s₁ t₁) (k₂ : Keeps s₂ t₂) : Related t₁ t₂ := by
  refine ⟨h.left.keeps k₁, h.right.keeps k₂, ?_, ?_, ?_, ?_⟩
  · rw [k₁.x19, k₂.x19, h.bp]
  · rw [k₁.x24, k₂.x24, h.bx]
  · rw [k₁.sp, k₂.sp, h.sp]
  · intro d hd
    obtain bound : ∀ d ∈ slots, d + 8 ≤ 272 := by decide
    rw [h.left.space.word_keeps k₁ d (bound d hd), h.right.space.word_keeps k₂ d (bound d hd)]
    exact h.words d hd

def RelatedRegs (rs : List Reg) (s t : State) : Prop :=
  Related s t ∧ ∀ r ∈ rs, s.gpr r = t.gpr r

theorem hash_keeps_rel {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (saved : ∀ r ∈ rs, r ∈ preserved ∧ r ≠ .x30)
    (ct : RelCT isa P c (fun _ _ => True))
    (pre : ∀ s t, P s t → RelatedRegs rs s t)
    (wp : ∀ s t, P s t → WP isa c s (HPrime.Keeps s) ∧ WP isa c t (HPrime.Keeps t)) :
    RelCT isa P c (RelatedRegs rs) := by
  apply (ct.wpDep wp).mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ha, hb⟩
  obtain h := pre s t hp
  refine ⟨h.1.keeps (Keeps.of_hash ha) (Keeps.of_hash hb), ?_⟩
  intro r hr
  rw [ha.regs r (saved r hr).1 (saved r hr).2, hb.regs r (saved r hr).1 (saved r hr).2]
  exact h.2 r hr

theorem finalize_ready {s : State} (h : Ready s) : HPrime.FinalizeReady s :=
  ⟨h.space.stackMinimum, h.space.work, h.space.stackWork⟩

end VG.Proof.Argon2.AArch64.Initial
end

/-! Merged from `Proof.Argon2.AArch64.InitialUpdateReady`. -/
section
/-! Permissions for the two updates of each length-prefixed H₀ input. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64

theorem prefix_update_ready {s t : State} {lo : Nat} (h : Space s) (args : LengthArgs s lo t) :
    HPrime.UpdateReady t := by
  have k := args.keeps
  obtain ht := h.keeps k
  obtain len : (t.gpr .x3).toNat = 4 := by rw [args.size]; rfl
  refine ⟨ht.stackMinimum, ht.work, ?_, ?_, ?_, ht.stackWork, ?_⟩
  · rw [args.pointer, len, ← k.x24]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨t.gpr .x24, 16384⟩, List.mem_append_right _ ht.work, 792, rfl, by change 792 + 4 ≤ 16384; decide⟩
  · rw [args.pointer, len, k.x24]
    exact (Offset.base_disjoint _ (by decide) (by decide)).symm
  · rw [args.pointer, len, k.x24]
    exact Offset.disjoint _ (d := 792) (n := 4) (e := 192) (k := 576) (by decide) (by decide) (by decide)
  · rw [args.pointer, len, ← k.x24]
    exact ht.stackWork.sub_right (Offset.sub_base _ (by decide))

theorem input_update_ready {s t : State} {po lo : Nat} (h : InputReady s po lo)
    (length : s.gpr .x22 = wordAt s lo) (args : InputArgs s t po) : HPrime.UpdateReady t := by
  have k := args.keeps
  have ptr : t.gpr .x2 = wordAt s po := args.pointer
  obtain len : t.gpr .x3 = wordAt s lo := args.length.trans length
  refine ⟨(h.space.keeps k).stackMinimum, (h.space.keeps k).work, ?_, ?_, ?_, (h.space.keeps k).stackWork, ?_⟩
  · rw [ptr, len, k.rd, k.wr]; exact h.cover
  · rw [ptr, len, k.x24]; exact h.work.sub_right (Region.sub_prefix (by decide))
  · rw [ptr, len, k.x24]; exact h.work.sub_right (Offset.sub_base _ (by decide))
  · rw [ptr, len, k.sp]; exact h.stack.symm

structure LengthRelated (lo : Nat) (s t : State) : Prop where
  related : RelatedRegs [.x20, .x22] s t
  leftLength : s.gpr .x22 = wordAt s lo
  rightLength : t.gpr .x22 = wordAt t lo

theorem LengthRelated.hash_keeps {lo : Nat} {s t a b : State} (h : LengthRelated lo s t)
    (bound : lo + 8 ≤ 272) (ka : HPrime.Keeps s a) (kb : HPrime.Keeps t b) : LengthRelated lo a b := by
  refine ⟨⟨h.related.1.keeps (Keeps.of_hash ka) (Keeps.of_hash kb), ?_⟩, ?_, ?_⟩
  · intro r hr
    obtain saved : ∀ r ∈ ([.x20, .x22] : List Reg), r ∈ preserved ∧ r ≠ .x30 := by decide
    rw [ka.regs r ((saved r hr).1) ((saved r hr).2), kb.regs r ((saved r hr).1) ((saved r hr).2)]
    exact h.related.2 r hr
  · rw [ka.regs .x22 (by decide) (by decide), h.related.1.left.space.word_keeps (Keeps.of_hash ka) lo bound]
    exact h.leftLength
  · rw [kb.regs .x22 (by decide) (by decide), h.related.1.right.space.word_keeps (Keeps.of_hash kb) lo bound]
    exact h.rightLength

end VG.Proof.Argon2.AArch64.Initial
end

/-! Merged from `Proof.Argon2.AArch64.InitialStartCT`. -/
section
/-! H₀ initialization and its fixed parameter header have input-independent traces. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial

theorem digestLength_rel : RelCT isa Related (.block ([Impl.Argon2.AArch64.Instructions.imm .x1 64].flatten))
    (fun s t => Related s t ∧ s.gpr .x1 = 64 ∧ t.gpr .x1 = 64) := by
  obtain ct := (RelCT.taint (A := taint) (P := Related) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.sp, by simp [Taint.ofRegs]⟩)
    (c := .block ([Impl.Argon2.AArch64.Instructions.imm .x1 64].flatten)) (by taint_decide)).wpDep
    (fun s t _ => ⟨digestLength_ok s, digestLength_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨la, _, ka⟩, ⟨lb, _, kb⟩⟩
  exact ⟨hp.keeps (Keeps.of_hash ka) (Keeps.of_hash kb), la, lb⟩

theorem init_hash_rel (v : HPrime.Backend) :
    RelCT isa (fun s t => Related s t ∧ s.gpr .x1 = 64 ∧ t.gpr .x1 = 64)
      (Impl.Argon2.AArch64.HPrime.init v.hash) Related := by
  have ready (s : State) (h : Ready s) (len : s.gpr .x1 = 64) : HPrime.InitReady s :=
    ⟨by rw [len]; decide, h.space.work,
      (h.space.stackWork.sub_left (below_sub (by decide) (by decide))).sub_right (Region.sub_prefix (by decide))⟩
  obtain ct := HPrime.init_rel v (P := fun s t => Related s t ∧ s.gpr .x1 = 64 ∧ t.gpr .x1 = 64)
    (fun s t ⟨h, ls, lt⟩ => ⟨ready s h.left ls, ready t h.right lt,
      h.bx, ls.trans lt.symm, h.sp⟩)
  obtain result := hash_keeps_rel [] (by simp) ct (fun _ _ h => ⟨h.1, by simp⟩)
    (fun s t ⟨h, ls, lt⟩ => ⟨HPrime.init_keeps v s (ready s h.left ls), HPrime.init_keeps v t (ready t h.right lt)⟩)
  exact result.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem header_state_rel : RelCT isa Related headerCode Related := by
  obtain ct := (header_rel.mono (P' := Related) (fun _ _ h => ⟨h.sp, h.bp, h.bx⟩)
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨headerWords_ok s 6 (by decide) h.left.space, headerWords_ok t 6 (by decide) h.right.space⟩)
  exact ct.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, hp, ⟨_, ka⟩, ⟨_, kb⟩⟩ => hp.keeps ka kb)

theorem fixed_header_rel (v : HPrime.Backend) :
    RelCT isa Related (Impl.Argon2.AArch64.HPrime.absorbFixed v.hash 768 24) Related := by
  obtain args := (RelCT.taint (A := taint) (P := Related) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.sp, by simp [Taint.ofRegs]⟩)
    (c := .block (Impl.Argon2.AArch64.HPrime.fixedArgs 768 24)) (by taint_decide)).wpDep
    (fun s t _ => ⟨HPrime.fixedArgs_ok s 768 24 (by decide) (by decide),
      HPrime.fixedArgs_ok t 768 24 (by decide) (by decide)⟩)
  obtain call := HPrime.update_rel v (P := fun a b => True ∧ ∃ s t, Related s t ∧
      HPrime.FixedArgs s a 768 24 ∧ HPrime.FixedArgs t b 768 24)
    (fun a b ⟨_, s, t, hp, ha, hb⟩ => ⟨HPrime.fixed_ready (finalize_ready hp.left) ha (by decide) (by decide),
      HPrime.fixed_ready (finalize_ready hp.right) hb (by decide) (by decide),
      by rw [ha.keeps.x24, hb.keeps.x24, hp.bx], by rw [ha.count, hb.count],
      by rw [ha.data, hb.data, hp.bx], by rw [ha.size, hb.size], by rw [ha.keeps.sp, hb.keeps.sp, hp.sp]⟩)
  obtain ct := args.seq call
  obtain result := hash_keeps_rel [] (by simp) ct (fun _ _ h => ⟨h, by simp⟩)
    (fun s t h => ⟨HPrime.absorbFixed_keeps v s 768 24 (finalize_ready h.left) (by decide) (by decide) (by decide),
      HPrime.absorbFixed_keeps v t 768 24 (finalize_ready h.right) (by decide) (by decide) (by decide)⟩)
  exact result.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem initialCount_rel : RelCT isa Related (.block ([Impl.Argon2.AArch64.Instructions.imm .x20 24].flatten)) (RelatedRegs [.x20]) := by
  obtain ct := (RelCT.taint (A := taint) (P := Related) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.sp, by simp [Taint.ofRegs]⟩)
    (c := .block ([Impl.Argon2.AArch64.Instructions.imm .x20 24].flatten)) (by taint_decide)).wpDep
    (fun s t _ => ⟨initialCount_ok s, initialCount_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨la, _, ka⟩, ⟨lb, _, kb⟩⟩
  refine ⟨hp.keeps ka kb, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact la.trans lb.symm

theorem start_rel (v : HPrime.Backend) :
    RelCT isa Related (start v.hash) (RelatedRegs [.x20]) :=
  digestLength_rel.seq ((init_hash_rel v).seq (header_state_rel.seq
    ((fixed_header_rel v).seq initialCount_rel)))

end VG.Proof.Argon2.AArch64.Initial
end

/-! Merged from `Proof.Argon2.AArch64.InitialFinishCT`. -/
section
/-! H₀ finalization and its fixed-size digest copy reveal no input contents. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial

theorem finishCount_rel : RelCT isa (RelatedRegs [.x20]) (.block ([Impl.Argon2.AArch64.Instructions.mov .x1 .x20].flatten))
    (fun s t => RelatedRegs [.x20] s t ∧ s.gpr .x1 = t.gpr .x1) := by
  obtain ct := (RelCT.taint (A := taint) (P := RelatedRegs [.x20]) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.1.sp, by simp [Taint.ofRegs]⟩)
    (c := .block ([Impl.Argon2.AArch64.Instructions.mov .x1 .x20].flatten)) (by taint_decide)).wpDep
    (fun s t _ => ⟨finishCount_ok s, finishCount_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨ca, _, ka⟩, ⟨cb, _, kb⟩⟩
  refine ⟨⟨hp.1.keeps (Keeps.of_hash ka) (Keeps.of_hash kb), ?_⟩, ?_⟩
  · intro r hr
    simp only [List.mem_singleton] at hr; subst r
    rw [ka.regs .x20 (by decide) (by decide), kb.regs .x20 (by decide) (by decide)]
    exact hp.2 _ (by simp)
  · rw [ca, cb]; exact hp.2 _ (by simp)

theorem finalize_hash_rel (v : HPrime.Backend) :
    RelCT isa (fun s t => RelatedRegs [.x20] s t ∧ s.gpr .x1 = t.gpr .x1)
      (Impl.Argon2.AArch64.HPrime.finalize v.hash) Related := by
  obtain ct := HPrime.finalize_rel v (P := fun s t => RelatedRegs [.x20] s t ∧ s.gpr .x1 = t.gpr .x1)
    (fun s t h => ⟨finalize_ready h.1.1.left, finalize_ready h.1.1.right, h.1.1.bx, h.2, h.1.1.sp⟩)
  obtain result := hash_keeps_rel [] (by simp) ct (fun _ _ h => ⟨h.1.1, by simp⟩)
    (fun s t h => ⟨HPrime.finalize_keeps v s (finalize_ready h.1.1.left),
      HPrime.finalize_keeps v t (finalize_ready h.1.1.right)⟩)
  exact result.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem finishOutput_rel : RelCT isa Related
    (.block ([Impl.Argon2.AArch64.Instructions.mov .x22 .x19, Impl.Argon2.AArch64.Instructions.imm .x8 64].flatten))
      (HPrime.AgreeRegs [.x24, .x22, .x8]) := by
  obtain ct := (RelCT.taint (A := taint) (P := Related) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.sp, by simp [Taint.ofRegs]⟩)
    (c := .block ([Impl.Argon2.AArch64.Instructions.mov .x22 .x19, Impl.Argon2.AArch64.Instructions.imm .x8 64].flatten)) (by taint_decide)).wpDep
    (fun s t _ => ⟨finishOutput_ok s, finishOutput_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨da, la, _, ka⟩, ⟨db, lb, _, kb⟩⟩
  refine ⟨by rw [ka.sp, kb.sp, hp.sp], ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [ka.x24, kb.x24, hp.bx]
  · rw [da, db, hp.bp]
  · rw [la, lb]

theorem copy_digest_rel : RelCT isa (HPrime.AgreeRegs [.x24, .x22, .x8])
    Impl.Argon2.AArch64.HPrime.copy (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.x24, .x22, .x8])
    (fun _ _ h => h.taint) (by taint_decide)

theorem finish_rel (v : HPrime.Backend) :
    RelCT isa (RelatedRegs [.x20]) (finish v.hash) (fun _ _ => True) :=
  finishCount_rel.seq ((finalize_hash_rel v).seq (finishOutput_rel.seq copy_digest_rel))

end VG.Proof.Argon2.AArch64.Initial
end

/-! Merged from `Proof.Argon2.AArch64.InitialCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.InitialAbsorbCT`. -/
section
/-! H₀ updates depend on public lengths and pointers, never on input contents. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial

def PrefixRelated (lo : Nat) (a b : State) : Prop :=
  True ∧ ∃ s t, RelatedRegs [.x20] s t ∧ LengthArgs s lo a ∧ LengthArgs t lo b

theorem prefix_rel (v : HPrime.Backend) (lo : Nat) (slot : lo ∈ slots)
    (bound : lo + 8 ≤ 272)
    (check : ∃ hint, (taint.check (Taint.ofRegs [.x19, .x24]) (.block (lengthArgs lo)) hint).isSome = true) :
    RelCT isa (RelatedRegs [.x20])
      (.seq (.block (lengthArgs lo)) (Impl.Argon2.AArch64.HPrime.update v.hash)) (LengthRelated lo) := by
  obtain args := ((lengthArgs_rel lo check).mono (P' := RelatedRegs [.x20])
    (fun _ _ h => ⟨h.1.sp, h.1.bp, h.1.bx⟩) (fun _ _ h => h)).wpDep
    (fun s t h => ⟨lengthArgs_ok s lo (slots_aligned lo slot) (by omega_using [bound]) (h.1.left.space.readable lo slot)
      (by simpa using h.1.left.space.write 792 4 (by decide)),
      lengthArgs_ok t lo (slots_aligned lo slot) (by omega_using [bound]) (h.1.right.space.readable lo slot)
      (by simpa using h.1.right.space.write 792 4 (by decide))⟩)
  obtain call := HPrime.update_rel v (P := PrefixRelated lo) (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨prefix_update_ready hp.1.left.space ha, prefix_update_ready hp.1.right.space hb,
      by rw [ha.keeps.x24, hb.keeps.x24, hp.1.bx], by rw [ha.count, hb.count]; exact hp.2 _ (by simp),
      by rw [ha.pointer, hb.pointer, hp.1.bx], by rw [ha.size, hb.size],
      by rw [ha.keeps.sp, hb.keeps.sp, hp.1.sp]⟩)
  obtain called := call.wpDep (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨HPrime.update_keeps v a (prefix_update_ready hp.1.left.space ha),
      HPrime.update_keeps v b (prefix_update_ready hp.1.right.space hb)⟩)
  obtain finished := called.mono (fun _ _ h => h) (fun a b h => by
    obtain ⟨_, x, y, ⟨_, s, t, hp, ha, hb⟩, ka, kb⟩ := h
    obtain rel := hp.1.keeps ha.keeps hb.keeps
    obtain prepared : LengthRelated lo x y := by
      refine ⟨⟨rel, ?_⟩, ?_, ?_⟩
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [ha.other _ (by decide),
            hb.other _ (by decide)]
          exact hp.2 _ (by simp)
        · rw [ha.length, hb.length]; exact hp.1.words lo slot
      · rw [hp.1.left.space.word_keeps ha.keeps lo bound]; exact ha.length
      · rw [hp.1.right.space.word_keeps hb.keeps lo bound]; exact hb.length
    exact prepared.hash_keeps bound ka kb)
  exact args.seq finished

def InputRelated (lo po : Nat) (a b : State) : Prop :=
  True ∧ ∃ s t, LengthRelated lo s t ∧ InputArgs s a po ∧ InputArgs t b po

theorem input_rel (v : HPrime.Backend) (po lo : Nat) (input : (po, lo) ∈ inputs)
    (check : ∃ hint, (taint.check (Taint.ofRegs [.x19]) (.block (inputArgs po)) hint).isSome = true) :
    RelCT isa (LengthRelated lo)
      (.seq (.block (inputArgs po)) (Impl.Argon2.AArch64.HPrime.update v.hash)) (LengthRelated lo) := by
  obtain args := ((inputArgs_rel po check).mono (P' := LengthRelated lo)
    (fun _ _ h => ⟨h.related.1.sp, h.related.1.bp⟩) (fun _ _ h => h)).wpDep
    (fun s t h => ⟨inputArgs_ok s po (slots_aligned po (h.related.1.left.inputs _ input).pointerSlot) (by have := (h.related.1.left.inputs _ input).pointerBound; omega) (h.related.1.left.space.readable po (h.related.1.left.inputs _ input).pointerSlot),
      inputArgs_ok t po (slots_aligned po (h.related.1.right.inputs _ input).pointerSlot) (by have := (h.related.1.right.inputs _ input).pointerBound; omega) (h.related.1.right.space.readable po (h.related.1.right.inputs _ input).pointerSlot)⟩)
  obtain call := HPrime.update_rel v (P := InputRelated lo po) (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨input_update_ready (hp.related.1.left.inputs _ input) hp.leftLength ha,
      input_update_ready (hp.related.1.right.inputs _ input) hp.rightLength hb,
      by rw [ha.keeps.x24, hb.keeps.x24, hp.related.1.bx],
      by rw [ha.count, hb.count, hp.related.2 .x20 (by simp)],
      by rw [ha.pointer, hb.pointer]; exact hp.related.1.words po (hp.related.1.left.inputs _ input).pointerSlot,
      by rw [ha.length, hb.length]; exact hp.related.2 .x22 (by simp),
      by rw [ha.keeps.sp, hb.keeps.sp, hp.related.1.sp]⟩)
  obtain called := call.wpDep (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨HPrime.update_keeps v a (input_update_ready (hp.related.1.left.inputs _ input) hp.leftLength ha),
      HPrime.update_keeps v b (input_update_ready (hp.related.1.right.inputs _ input) hp.rightLength hb)⟩)
  obtain finished := called.mono (fun _ _ h => h) (fun a b h => by
    obtain ⟨_, x, y, ⟨_, s, t, hp, ha, hb⟩, ka, kb⟩ := h
    obtain left := hp.related.1.left.inputs _ input
    obtain right := hp.related.1.right.inputs _ input
    obtain prepared : LengthRelated lo x y := by
      refine ⟨⟨hp.related.1.keeps ha.keeps hb.keeps, ?_⟩, ?_, ?_⟩
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [ha.total, hb.total, hp.related.2 .x20 (by simp)]
        · rw [ha.other _ (by decide),
            hb.other _ (by decide)]
          exact hp.related.2 .x22 (by simp)
      · rw [left.space.word_keeps ha.keeps lo left.lengthBound,
          ha.other _ (by decide)]
        exact hp.leftLength
      · rw [right.space.word_keeps hb.keeps lo right.lengthBound,
          hb.other _ (by decide)]
        exact hp.rightLength
    exact prepared.hash_keeps left.lengthBound ka kb)
  exact args.seq finished

theorem addCount_rel (lo : Nat) :
    RelCT isa (LengthRelated lo) (.block (Impl.Argon2.AArch64.Instructions.add .x20 .x22)) (RelatedRegs [.x20]) := by
  obtain ct := (RelCT.taint (A := taint) (P := LengthRelated lo) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.related.1.sp, by simp [Taint.ofRegs]⟩)
    (c := .block (Impl.Argon2.AArch64.Instructions.add .x20 .x22)) (by taint_decide)).wpDep
    (fun s t _ => ⟨addCount_ok s, addCount_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨ca, _, ka⟩, ⟨cb, _, kb⟩⟩
  refine ⟨hp.related.1.keeps ka kb, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  rw [ca, cb, hp.related.2 .x20 (by simp), hp.related.2 .x22 (by simp)]

theorem absorb_rel (v : HPrime.Backend) (po lo : Nat) (input : (po, lo) ∈ inputs)
    (lengthCheck : ∃ hint, (taint.check (Taint.ofRegs [.x19, .x24]) (.block (lengthArgs lo)) hint).isSome = true)
    (pointerCheck : ∃ hint, (taint.check (Taint.ofRegs [.x19]) (.block (inputArgs po)) hint).isSome = true) :
    RelCT isa (RelatedRegs [.x20]) (absorb v.hash po lo) (RelatedRegs [.x20]) := by
  obtain slot : lo ∈ slots := by
    obtain all : ∀ p ∈ inputs, p.2 ∈ slots := by decide
    exact all _ input
  obtain bound : lo + 8 ≤ 272 := by
    obtain all : ∀ d ∈ slots, d + 8 ≤ 272 := by decide
    exact all lo slot
  exact ((prefix_rel v lo slot bound lengthCheck).seq
    (((input_rel v po lo input pointerCheck).seq (addCount_rel lo)).assoc)).assoc

end VG.Proof.Argon2.AArch64.Initial
end

/-! Complete H₀ is constant time for every verified BLAKE2b backend. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial

theorem code_rel (v : HPrime.Backend) :
    RelCT isa Related (code v.hash) (fun _ _ => True) :=
  (start_rel v).seq
    ((absorb_rel v passwordOffset passwordLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    ((absorb_rel v saltOffset saltLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    ((absorb_rel v secretOffset secretLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    ((absorb_rel v adOffset adLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
      (finish_rel v)))))

end VG.Proof.Argon2.AArch64.Initial
end

/-! Merged from `Proof.Argon2.AArch64.InitialBodyReviewedCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.InitialBodyCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.InitFillCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FinishStageCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FinalOutputCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FinalCallCT`. -/
section
/-! # The final H′ call leak only their public argument registers -/

namespace VG.Proof.Argon2.AArch64.FinalCall

open VG VG.AArch64
open VG.Impl.Argon2.AArch64.HPrime (code)

theorem hPrime_call_rel (v : HPrime.Backend) (name : String) (len : Nat)
    {P : State → State → Prop}
    (pre : ∀ s t, P s t → CallReady len s ∧ CallReady len t ∧
      s.gpr .x1 = 1024 ∧ t.gpr .x1 = 1024 ∧ s.gpr .x3 = BitVec.ofNat 64 len ∧ t.gpr .x3 = BitVec.ofNat 64 len ∧
      s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x2 = t.gpr .x2 ∧
      s.gpr .x4 = t.gpr .x4 ∧ s.sp = t.sp) :
    RelCT isa P (.call name (code v.hash)) (fun _ _ => True) := by
  apply RelCT.callEx (k := HPrime.localContract) (HPrime.code_correct v) (HPrime.code_ct v)
  intro s t hp
  obtain ⟨hs, ht, ls, lt, os, ot, di, dx, x4, sp⟩ := pre s t hp
  obtain ⟨ps, cs, ws⟩ := hPrime_call_hyps len s hs ls os
  obtain ⟨pt, ct, wt⟩ := hPrime_call_hyps len t ht lt ot
  refine ⟨_, _, _, _, ps, pt, ?_, cs, ws, ct, wt⟩
  change s.callEntry.gpr .x0 = t.callEntry.gpr .x0 ∧
    s.callEntry.gpr .x1 = t.callEntry.gpr .x1 ∧
    s.callEntry.gpr .x2 = t.callEntry.gpr .x2 ∧
    s.callEntry.gpr .x3 = t.callEntry.gpr .x3 ∧
    s.callEntry.gpr .x4 = t.callEntry.gpr .x4 ∧
    s.callEntry.sp = t.callEntry.sp
  simp only [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), State.callEntry_sp]
  exact ⟨di, ls.trans lt.symm, dx, os.trans ot.symm, x4, sp⟩

end VG.Proof.Argon2.AArch64.FinalCall
end

/-! Final hashing exposes only the public tag length and pointers, for any hash backend. -/

namespace VG.Proof.Argon2.AArch64.FinalOutput

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : ReductionState.matrix s = ReductionState.matrix t
  outputs : output s = output t
  works : work s = work t

structure NextRelated (p : Params) (s t : State) : Prop where
  left : FinalCall.CallReady p.tagLen s
  right : FinalCall.CallReady p.tagLen t
  leftInputLength : s.gpr .x1 = 1024
  rightInputLength : t.gpr .x1 = 1024
  leftOutputLength : s.gpr .x3 = BitVec.ofNat 64 p.tagLen
  rightOutputLength : t.gpr .x3 = BitVec.ofNat 64 p.tagLen
  inputs : s.gpr .x0 = t.gpr .x0
  outputs : s.gpr .x2 = t.gpr .x2
  works : s.gpr .x4 = t.gpr .x4
  stacks : s.sp = t.sp

theorem args_trace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block Impl.Argon2.AArch64.FinalOutput.args) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem args_rel (p : Params) : RelCT isa (Related p)
    (.block Impl.Argon2.AArch64.FinalOutput.args) (NextRelated p) := by
  obtain trace := args_trace.mono (P' := Related p) (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  obtain full := trace.wpDep (fun s t h => ⟨args_ok s h.left.reads, args_ok t h.right.reads⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.ready hp.left, hb.ready hp.right, ha.inputLength, hb.inputLength,
    ha.outputLength.trans hp.left.tagWord, hb.outputLength.trans hp.right.tagWord,
    ha.input.trans (hp.matrices.trans hb.input.symm), ha.output.trans (hp.outputs.trans hb.output.symm),
    ha.work.trans (hp.works.trans hb.work.symm),
    (ha.keeps.sp).trans (hp.stacks.trans (hb.keeps.sp).symm)⟩

theorem code_rel (v : HPrime.Backend) (name : String) (p : Params) :
    RelCT isa (Related p) (Impl.Argon2.AArch64.FinalOutput.code name v.hash) (fun _ _ => True) :=
  (args_rel p).seq (FinalCall.hPrime_call_rel v name p.tagLen (fun _ _ h =>
    ⟨h.left, h.right, h.leftInputLength, h.rightInputLength, h.leftOutputLength, h.rightOutputLength,
      h.inputs, h.outputs, h.works, h.stacks⟩))

end VG.Proof.Argon2.AArch64.FinalOutput
end

/-! Complete finalization has a public trace for every BLAKE2b backend. -/

namespace VG.Proof.Argon2.AArch64.Finish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (leftMemory rightMemory : Array Block) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : matrix s = matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  leftMatrix : Proof.Argon2.Represents s.mem (matrix s) p.blocks leftMemory
  rightMatrix : Proof.Argon2.Represents t.mem (matrix t) p.blocks rightMemory

theorem code_rel (v : HPrime.Backend) (name : String) (p : Params)
    (leftMemory rightMemory : Array Block) :
    RelCT isa (Related p leftMemory rightMemory) (Impl.Argon2.AArch64.Finish.code name v.hash)
      (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq reduceA outputA =>
    cases eb with
    | seq reduceB outputB =>
      obtain related : ReductionInit.Related p leftMemory rightMemory s t :=
        ⟨hp.left.reduction, hp.right.reduction, hp.bases, hp.stacks, hp.matrices, hp.leftMatrix, hp.rightMatrix⟩
      obtain ⟨reduceTrace, _⟩ := FinalReduction.code_rel p hp.left.reduction.allocation.positive
        leftMemory rightMemory _ _ _ _ _ _ related reduceA reduceB
      obtain ⟨_, sa, runA, doneA⟩ := FinalReduction.code_ok s p hp.left.reduction leftMemory hp.leftMatrix
      obtain ⟨_, sb, runB, doneB⟩ := FinalReduction.code_ok t p hp.right.reduction rightMemory hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det reduceA runA
      obtain ⟨_, rfl⟩ := Exec.det reduceB runB
      obtain finalRelated : FinalOutput.Related p _ _ :=
        ⟨output_ready hp.left doneA, output_ready hp.right doneB,
          (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).trans
            (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).symm),
          (doneA.sp).trans
            (hp.stacks.trans (doneB.sp).symm),
          doneA.base.trans (hp.matrices.trans doneB.base.symm),
          (frame_word hp.left.reduction doneA 256 (by decide)).trans
            (hp.outputs.trans (frame_word hp.right.reduction doneB 256 (by decide)).symm),
          (frame_word hp.left.reduction doneA 248 (by decide)).trans
            (hp.works.trans (frame_word hp.right.reduction doneB 248 (by decide)).symm)⟩
      obtain ⟨outputTrace, _⟩ := FinalOutput.code_rel v name p _ _ _ _ _ _ finalRelated outputA outputB
      exact ⟨by rw [reduceTrace, outputTrace], trivial⟩

end VG.Proof.Argon2.AArch64.Finish
end

/-! Merged from `Proof.Argon2.AArch64.FillSlicesCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillSlicesBodyCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillSliceCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillLanesCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillLanesBodyCT`. -/
section
/-! Lane iteration preserves public allocations and loops on the public lane count. -/

namespace VG.Proof.Argon2.AArch64.FillLanes

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillLanes

theorem advance_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block advance) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

structure NextRelated (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  ready : SegmentSetup.RelatedReady p pass lane slice s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (SegmentSetup.Related p pass lane slice leftState rightState) body
      (fun s t => eval (.nonzero .x .x14) s = eval (.nonzero .x .x14) t ∧ (lane + 1 < p.lanes → NextRelated p pass (lane + 1) slice
        (Proof.Argon2.segment p pass lane slice 0 p.segmentLen leftState)
        (Proof.Argon2.segment p pass lane slice 0 p.segmentLen rightState) s t)) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq segmentA advanceA =>
    cases eb with
    | seq segmentB advanceB =>
      obtain ⟨segmentTrace, _⟩ := SegmentSetup.code_rel p pass lane slice leftState rightState
        _ _ _ _ _ _ hp segmentA segmentB
      obtain ⟨_, sa, runA, filledA⟩ := SegmentSetup.code_ok s p pass lane slice hp.ready.left leftState hp.leftMatrix
      obtain ⟨_, sb, runB, filledB⟩ := SegmentSetup.code_ok t p pass lane slice hp.ready.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det segmentA runA
      obtain ⟨_, rfl⟩ := Exec.det segmentB runB
      obtain bases := (filledA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).trans
        (hp.ready.bases.trans (filledB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).symm)
      obtain stacks := filledA.sp.trans (hp.ready.stacks.trans filledB.sp.symm)
      obtain ⟨advancedTrace, _⟩ := advance_rel _ _ _ _ _ _ ⟨bases, stacks⟩ advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := body_ok s p pass lane slice hp.ready.left leftState hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := body_ok t p pass lane slice hp.ready.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentB advanceB) runB
      refine ⟨by rw [segmentTrace, advancedTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨⟨doneA.next active, doneB.next active, ?_, ?_,
        doneA.matrix.trans (hp.ready.matrices.trans doneB.matrix.symm),
        doneA.work.trans (hp.ready.work.trans doneB.work.symm)⟩, doneA.represented, doneB.represented⟩
      · exact (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide)).trans
          (hp.ready.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide)).symm)
      · exact (doneA.sp).trans
          (hp.ready.stacks.trans (doneB.sp).symm)

end VG.Proof.Argon2.AArch64.FillLanes
end

/-! The lane loop exposes only the slice's specified reference log. -/

namespace VG.Proof.Argon2.AArch64.FillLanes

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass lane slice count : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  ready : SegmentSetup.RelatedReady p pass lane slice s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.lanes p pass slice lane count leftState).indices =
    (Proof.Argon2.lanes p pass slice lane count rightState).indices

theorem loop_rel (p : Params) (pass lane slice count : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    RelCT isa (Related p pass lane slice count leftState rightState) Impl.Argon2.AArch64.FillLanes.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (lane : Nat) (leftState rightState : FillState),
    lane + n = p.lanes ∧ 0 < n ∧ Related p pass lane slice n leftState rightState s t
  obtain steps : ∀ n, RelCT isa (I n) Impl.Argon2.AArch64.FillLanes.body fun s t =>
      isa.eval (.nonzero .x .x14) s = isa.eval (.nonzero .x .x14) t ∧ (isa.eval (.nonzero .x .x14) s = some false → True) ∧
        (isa.eval (.nonzero .x .x14) s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, ls, rs, endLane, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      obtain segmentRelated : SegmentSetup.Related p pass j slice ls rs s t :=
        ⟨hp.ready, hp.leftMatrix, hp.rightMatrix, Proof.Argon2.lanes_first_segment p pass slice j n ls rs
          hp.ready.left.parameters.segment_bound.1 hp.indices⟩
      obtain ⟨trace, flags, next⟩ := body_rel p pass j slice ls rs _ _ _ _ _ _ segmentRelated ea eb
      obtain ⟨_, a', runA, done⟩ := body_ok s p pass j slice hp.ready.left ls hp.leftMatrix
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · exact flags
      · intro taken
        obtain active : j + 1 < p.lanes := by
          simp only [done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        obtain ⟨ready, matrixA, matrixB⟩ := next active
        have indices := hp.indices
        rw [Proof.Argon2.lanes_succ, Proof.Argon2.lanes_succ] at indices
        exact ⟨n, by omega_using [], j + 1, Proof.Argon2.segment p pass j slice 0 p.segmentLen ls,
          Proof.Argon2.segment p pass j slice 0 p.segmentLen rs, by omega_using [endLane], by omega_using [endLane, active], ready, matrixA, matrixB, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨lane, leftState, rightState, endLane, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.FillLanes
end

/-! A complete slice exposes only its specified reference log. -/

namespace VG.Proof.Argon2.AArch64.FillSlice

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass slice : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : Ready p pass slice s
  right : Ready p pass slice t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.lanes p pass slice 0 p.lanes leftState).indices =
    (Proof.Argon2.lanes p pass slice 0 p.lanes rightState).indices

theorem setup_trace : RelCT isa (fun s t : State => s.sp = t.sp) (.block Impl.Argon2.AArch64.FillSlice.setup) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem setup_public_rel (p : Params) (pass slice : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass slice leftState rightState) (.block Impl.Argon2.AArch64.FillSlice.setup)
      (FillLanes.Related p pass 0 slice p.lanes leftState rightState) := by
  obtain trace := setup_trace.mono (P' := Related p pass slice leftState rightState)
    (fun _ _ h => h.stacks) (fun _ _ h => h)
  obtain full := trace.wpDep (fun s t h => ⟨setup_ok s p pass slice h.left, setup_ok t p pass slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨⟨ha.ready, hb.ready, ?_, ?_, ?_, ?_⟩, ?_, ?_, hp.indices⟩
  · rw [ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]; exact hp.bases
  · rw [ha.keeps.sp, hb.keeps.sp]; exact hp.stacks
  · unfold FillKernel.matrix
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]
    exact hp.matrices
  · unfold AddressCalls.work
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]
    exact hp.work
  · unfold FillKernel.matrix; rw [ha.keeps.mem, ha.keeps.regs .x19 (by decide)]; exact hp.leftMatrix
  · unfold FillKernel.matrix; rw [hb.keeps.mem, hb.keeps.regs .x19 (by decide)]; exact hp.rightMatrix

theorem code_rel (p : Params) (pass slice : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass slice leftState rightState) Impl.Argon2.AArch64.FillSlice.code (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq setupA lanesA =>
    cases eb with
    | seq setupB lanesB =>
      obtain ⟨setupTrace, related⟩ := setup_public_rel p pass slice leftState rightState _ _ _ _ _ _ hp setupA setupB
      obtain ⟨lanesTrace, _⟩ := FillLanes.loop_rel p pass 0 slice p.lanes leftState rightState
        hp.left.parameters.lanesPositive (by omega_using []) _ _ _ _ _ _ related lanesA lanesB
      exact ⟨by rw [setupTrace, lanesTrace], trivial⟩

end VG.Proof.Argon2.AArch64.FillSlice
end

/-! A slice iteration preserves public allocations and its public continuation guard. -/

namespace VG.Proof.Argon2.AArch64.FillSlices

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillSlices

theorem advance_rel : RelCT isa (fun s t : State => s.sp = t.sp)
    (.block advance) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

structure NextRelated (p : Params) (pass slice : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : FillSlice.Ready p pass slice s
  right : FillSlice.Ready p pass slice t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel (p : Params) (pass slice : Nat) (leftState rightState : FillState) :
    RelCT isa (FillSlice.Related p pass slice leftState rightState) body
      (fun s t => eval (.nonzero .x .x14) s = eval (.nonzero .x .x14) t ∧ (slice + 1 < 4 → NextRelated p pass (slice + 1)
        (Proof.Argon2.lanes p pass slice 0 p.lanes leftState) (Proof.Argon2.lanes p pass slice 0 p.lanes rightState) s t)) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq sliceA advanceA =>
    cases eb with
    | seq sliceB advanceB =>
      obtain ⟨sliceTrace, _⟩ := FillSlice.code_rel p pass slice leftState rightState _ _ _ _ _ _ hp sliceA sliceB
      obtain ⟨_, sa, fillRunA, filledA⟩ := FillSlice.code_ok s p pass slice hp.left leftState hp.leftMatrix
      obtain ⟨_, sb, fillRunB, filledB⟩ := FillSlice.code_ok t p pass slice hp.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det sliceA fillRunA
      obtain ⟨_, rfl⟩ := Exec.det sliceB fillRunB
      obtain stacks := filledA.sp.trans (hp.stacks.trans filledB.sp.symm)
      obtain ⟨advanceTrace, _⟩ := advance_rel _ _ _ _ _ _ stacks advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := body_ok s p pass slice hp.left leftState hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := body_ok t p pass slice hp.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq sliceA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq sliceB advanceB) runB
      refine ⟨by rw [sliceTrace, advanceTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨doneA.next active, doneB.next active, ?_, ?_,
        doneA.matrix.trans (hp.matrices.trans doneB.matrix.symm),
        doneA.work.trans (hp.work.trans doneB.work.symm), doneA.represented, doneB.represented⟩
      · exact (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).trans
          (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).symm)
      · exact (doneA.sp).trans
          (hp.stacks.trans (doneB.sp).symm)

end VG.Proof.Argon2.AArch64.FillSlices
end

/-! The complete pass leaks only its reviewed reference log, including Argon2id's mode change. -/

namespace VG.Proof.Argon2.AArch64.FillSlices

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass slice count : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  states : NextRelated p pass slice leftState rightState s t
  indices : (Proof.Argon2.slices p pass slice count leftState).indices =
    (Proof.Argon2.slices p pass slice count rightState).indices

theorem loop_rel (p : Params) (pass slice count : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endSlice : slice + count = 4) :
    RelCT isa (Related p pass slice count leftState rightState) Impl.Argon2.AArch64.FillSlices.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (slice : Nat) (leftState rightState : FillState),
    slice + n = 4 ∧ 0 < n ∧ Related p pass slice n leftState rightState s t
  obtain steps : ∀ n, RelCT isa (I n) Impl.Argon2.AArch64.FillSlices.body fun s t =>
      isa.eval (.nonzero .x .x14) s = isa.eval (.nonzero .x .x14) t ∧ (isa.eval (.nonzero .x .x14) s = some false → True) ∧
        (isa.eval (.nonzero .x .x14) s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, ls, rs, endSlice, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      obtain sliceRelated : FillSlice.Related p pass j ls rs s t :=
        ⟨hp.states.left, hp.states.right, hp.states.bases, hp.states.stacks, hp.states.matrices, hp.states.work,
          hp.states.leftMatrix, hp.states.rightMatrix, Proof.Argon2.slices_first_lane_fold p pass j n ls rs
            hp.states.left.parameters.segment_bound.1 hp.indices⟩
      obtain ⟨trace, flags, next⟩ := body_rel p pass j ls rs _ _ _ _ _ _ sliceRelated ea eb
      obtain ⟨_, a', runA, done⟩ := body_ok s p pass j hp.states.left ls hp.states.leftMatrix
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · exact flags
      · intro taken
        obtain active : j + 1 < 4 := by
          simp only [done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        have indices := hp.indices
        rw [Proof.Argon2.slices_succ, Proof.Argon2.slices_succ] at indices
        exact ⟨n, by omega_using [], j + 1, Proof.Argon2.lanes p pass j 0 p.lanes ls,
          Proof.Argon2.lanes p pass j 0 p.lanes rs, by omega_using [endSlice], by omega_using [endSlice, active], next active, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨slice, leftState, rightState, endSlice, positive, h⟩) (fun _ _ h => h)

theorem pass_rel (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (fun s t => NextRelated p pass 0 leftState rightState s t ∧
      (fillPass p leftState pass).indices = (fillPass p rightState pass).indices)
      Impl.Argon2.AArch64.FillSlices.loop (fun _ _ => True) := by
  refine (loop_rel p pass 0 4 leftState rightState (by decide) (by decide)).mono ?_ (fun _ _ h => h)
  intro s t h
  refine ⟨h.1, ?_⟩
  rw [Proof.Argon2.slices_pass p pass leftState, Proof.Argon2.slices_pass p pass rightState]
  exact h.2

end VG.Proof.Argon2.AArch64.FillSlices
end

/-! Merged from `Proof.Argon2.AArch64.FillIterationsCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillIterationsBodyCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillIterationCT`. -/
section
/-! Pass setup retains public pointers and exposes only the reviewed pass log. -/

namespace VG.Proof.Argon2.AArch64.FillIteration

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : Ready p pass s
  right : Ready p pass t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (fillPass p leftState pass).indices = (fillPass p rightState pass).indices

theorem setup_trace : RelCT isa (fun s t : State => s.sp = t.sp) (.block Impl.Argon2.AArch64.FillIteration.setup) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem setup_public_rel (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass leftState rightState) (.block Impl.Argon2.AArch64.FillIteration.setup)
      (fun s t => FillSlices.NextRelated p pass 0 leftState rightState s t ∧
        (fillPass p leftState pass).indices = (fillPass p rightState pass).indices) := by
  obtain trace := setup_trace.mono (P' := Related p pass leftState rightState)
    (fun _ _ h => h.stacks) (fun _ _ h => h)
  obtain full := trace.wpDep (fun s t h => ⟨setup_ok s p pass h.left, setup_ok t p pass h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨⟨ha.ready, hb.ready, ?_, ?_, ?_, ?_, ?_, ?_⟩, hp.indices⟩
  · rw [ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]; exact hp.bases
  · rw [ha.keeps.sp, hb.keeps.sp]; exact hp.stacks
  · unfold FillKernel.matrix
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]; exact hp.matrices
  · unfold AddressCalls.work
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]; exact hp.work
  · unfold FillKernel.matrix; rw [ha.keeps.mem, ha.keeps.regs .x19 (by decide)]; exact hp.leftMatrix
  · unfold FillKernel.matrix; rw [hb.keeps.mem, hb.keeps.regs .x19 (by decide)]; exact hp.rightMatrix

theorem code_rel (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass leftState rightState) Impl.Argon2.AArch64.FillIteration.code (fun _ _ => True) :=
  (setup_public_rel p pass leftState rightState).seq (FillSlices.pass_rel p pass leftState rightState)

end VG.Proof.Argon2.AArch64.FillIteration
end

/-! Iteration advances its public pass counter and retains the reviewed filling log. -/

namespace VG.Proof.Argon2.AArch64.FillIterations

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillIterations

theorem advance_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    advance (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

structure NextRelated (p : Params) (pass : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : Ready p pass s
  right : Ready p pass t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (fun s t => NextRelated p pass leftState rightState s t ∧
      (fillPass p leftState pass).indices = (fillPass p rightState pass).indices) body
      (fun s t => eval (.nonzero .x .x14) s = eval (.nonzero .x .x14) t ∧ (pass + 1 < p.passes → NextRelated p (pass + 1)
        (fillPass p leftState pass)
        (fillPass p rightState pass) s t)) := by
  intro s t ts tt a b hp ea eb
  obtain ⟨hp, indices⟩ := hp
  obtain related : FillIteration.Related p pass leftState rightState s t :=
    ⟨hp.left.filling, hp.right.filling, hp.bases, hp.stacks, hp.matrices, hp.work, hp.leftMatrix, hp.rightMatrix, indices⟩
  cases ea with
  | seq segmentA advanceA =>
    cases eb with
    | seq segmentB advanceB =>
      obtain ⟨segmentTrace, _⟩ := FillIteration.code_rel p pass leftState rightState
        _ _ _ _ _ _ related segmentA segmentB
      obtain ⟨_, sa, runA, filledA⟩ := FillIteration.code_ok s p pass hp.left.filling leftState hp.leftMatrix
      obtain ⟨_, sb, runB, filledB⟩ := FillIteration.code_ok t p pass hp.right.filling rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det segmentA runA
      obtain ⟨_, rfl⟩ := Exec.det segmentB runB
      obtain bases := (filledA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).trans
        (hp.bases.trans (filledB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).symm)
      obtain stacks := filledA.sp.trans (hp.stacks.trans filledB.sp.symm)
      obtain ⟨advancedTrace, _⟩ := advance_rel _ _ _ _ _ _ ⟨bases, stacks⟩ advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := body_ok s p pass hp.left leftState hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := body_ok t p pass hp.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentB advanceB) runB
      refine ⟨by rw [segmentTrace, advancedTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨doneA.next active, doneB.next active, ?_, ?_,
        doneA.matrix.trans (hp.matrices.trans doneB.matrix.symm),
        doneA.work.trans (hp.work.trans doneB.work.symm), doneA.represented, doneB.represented⟩
      · exact (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).trans
          (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).symm)
      · exact (doneA.sp).trans
          (hp.stacks.trans (doneB.sp).symm)

end VG.Proof.Argon2.AArch64.FillIterations
end

/-! The pass loop exposes only the complete filling reference log. -/

namespace VG.Proof.Argon2.AArch64.FillIterations

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass count : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  ready : NextRelated p pass leftState rightState s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.iterations p pass count leftState).indices =
    (Proof.Argon2.iterations p pass count rightState).indices

theorem loop_rel (p : Params) (pass count : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endPass : pass + count = p.passes) :
    RelCT isa (Related p pass count leftState rightState) Impl.Argon2.AArch64.FillIterations.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (pass : Nat) (leftState rightState : FillState),
    pass + n = p.passes ∧ 0 < n ∧ Related p pass n leftState rightState s t
  obtain steps : ∀ n, RelCT isa (I n) Impl.Argon2.AArch64.FillIterations.body fun s t =>
      isa.eval (.nonzero .x .x14) s = isa.eval (.nonzero .x .x14) t ∧ (isa.eval (.nonzero .x .x14) s = some false → True) ∧
        (isa.eval (.nonzero .x .x14) s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, ls, rs, endPass, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      obtain passIndices := Proof.Argon2.iterations_first_pass p j n ls rs
        hp.ready.left.filling.parameters.segment_bound.1 hp.indices
      obtain ⟨trace, flags, next⟩ := body_rel p j ls rs _ _ _ _ _ _ ⟨hp.ready, passIndices⟩ ea eb
      obtain ⟨_, a', runA, done⟩ := body_ok s p j hp.ready.left ls hp.leftMatrix
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · exact flags
      · intro taken
        obtain active : j + 1 < p.passes := by
          simp only [done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        obtain ready := next active
        have indices := hp.indices
        rw [Proof.Argon2.iterations_succ, Proof.Argon2.iterations_succ] at indices
        exact ⟨n, by omega_using [], j + 1, fillPass p ls j,
          fillPass p rs j, by omega_using [endPass], by omega_using [endPass, active], ready, ready.leftMatrix, ready.rightMatrix, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨pass, leftState, rightState, endPass, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.FillIterations
end

/-! Merged from `Proof.Argon2.AArch64.FillFinishCT`. -/
section
/-! Filling and finalization expose only the reviewed filling reference log. -/

namespace VG.Proof.Argon2.AArch64.FillFinish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (leftState rightState : FillState) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : matrix s = matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  leftMatrix : Proof.Argon2.Represents s.mem (matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.iterations p 0 p.passes leftState).indices =
    (Proof.Argon2.iterations p 0 p.passes rightState).indices

theorem code_rel (v : HPrime.Backend) (name : String) (p : Params)
    (leftState rightState : FillState) :
    RelCT isa (Related p leftState rightState) (Impl.Argon2.AArch64.FillFinish.code name v.hash)
      (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq fillA finishA =>
    cases eb with
    | seq fillB finishB =>
      obtain related : FillIterations.Related p 0 p.passes leftState rightState s t :=
        ⟨⟨hp.left.filling, hp.right.filling, hp.bases, hp.stacks, hp.matrices, hp.works, hp.leftMatrix, hp.rightMatrix⟩,
          hp.leftMatrix, hp.rightMatrix, hp.indices⟩
      obtain ⟨fillTrace, _⟩ := FillIterations.loop_rel p 0 p.passes leftState rightState hp.left.positive
        (Nat.zero_add _) _ _ _ _ _ _ related fillA fillB
      obtain ⟨_, sa, runA, doneA⟩ := FillIterations.loop_ok p.passes s p 0 hp.left.filling leftState
        hp.leftMatrix hp.left.positive (Nat.zero_add _)
      obtain ⟨_, sb, runB, doneB⟩ := FillIterations.loop_ok p.passes t p 0 hp.right.filling rightState
        hp.rightMatrix hp.right.positive (Nat.zero_add _)
      obtain ⟨_, rfl⟩ := Exec.det fillA runA
      obtain ⟨_, rfl⟩ := Exec.det fillB runB
      obtain finalRelated : Finish.Related p (Proof.Argon2.iterations p 0 p.passes leftState).memory
          (Proof.Argon2.iterations p 0 p.passes rightState).memory _ _ :=
        ⟨finish_ready hp.left.filling hp.left.finish doneA, finish_ready hp.right.filling hp.right.finish doneB,
          (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).trans
            (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).symm),
          (doneA.sp).trans
            (hp.stacks.trans (doneB.sp).symm),
          doneA.matrix.trans (hp.matrices.trans doneB.matrix.symm),
          (doneA.frame_word hp.left.filling 256 (by decide) (by decide)).trans
            (hp.outputs.trans (doneB.frame_word hp.right.filling 256 (by decide) (by decide)).symm),
          (doneA.frame_word hp.left.filling 248 (by decide) (by decide)).trans
            (hp.works.trans (doneB.frame_word hp.right.filling 248 (by decide) (by decide)).symm),
          doneA.represented, doneB.represented⟩
      obtain ⟨finishTrace, _⟩ := Finish.code_rel v name p _ _ _ _ _ _ _ _ finalRelated finishA finishB
      exact ⟨by rw [fillTrace, finishTrace], trivial⟩

end VG.Proof.Argon2.AArch64.FillFinish
end

/-! The entire post-H₀ pipeline leaks only the reviewed complete filling reference log. -/

namespace VG.Proof.Argon2.AArch64.InitFill

open VG VG.AArch64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

def initial (p : Params) (s : State) : FillState := initMemory p (bytesAt s.mem (s.gpr .x19) 64)

structure Related (p : Params) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  indices : (Proof.Argon2.iterations p 0 p.passes (initial p s)).indices =
    (Proof.Argon2.iterations p 0 p.passes (initial p t)).indices

theorem code_rel (v : HPrime.Backend) (name : String) (p : Params) :
    RelCT isa (Related p) (Impl.Argon2.AArch64.InitFill.code name v.hash) (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  have params := hp.left.environment.parameters
  obtain q : 2 ≤ p.laneLen := by
    obtain segments := Proof.Argon2.laneLen_segments p params.lanesPositive
    have minimum := params.segment_bound.1
    omega_using [segments, minimum]
  obtain lanesBound : p.lanes < 2 ^ 64 := Nat.lt_trans params.lanesBound (by decide)
  obtain pub : MemoryInit.AgreeBases s t := by
    refine ⟨hp.stacks, ?_⟩
    intro r hr
    simp only [MemoryInit.publicBases, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.bases
    · exact hp.left.scratch.trans (hp.works.trans hp.right.scratch.symm)
    · exact hp.left.initializing.laneLength.trans hp.right.initializing.laneLength.symm
  obtain rightReady : MemoryInit.Ready (FillKernel.matrix s) p.lanes p.laneLen t := by
    rw [hp.matrices]; exact hp.right.initializing
  cases ea with
  | seq initA restA =>
    cases eb with
    | seq initB restB =>
      obtain initTrace := MemoryInit.code_ct v name (FillKernel.matrix s) p.lanes p.laneLen
        params.lanesPositive lanesBound q _ _ _ _ _ _ hp.left.initializing rightReady pub initA initB
      obtain ⟨_, sa, runA, doneA⟩ := MemoryInit.complete_ok v name s (FillKernel.matrix s) p.lanes p.laneLen
        hp.left.initializing params.lanesPositive lanesBound q
      obtain ⟨_, sb, runB, doneB⟩ := MemoryInit.complete_ok v name t (FillKernel.matrix t) p.lanes p.laneLen
        hp.right.initializing params.lanesPositive lanesBound q
      obtain ⟨_, rfl⟩ := Exec.det initA runA
      obtain ⟨_, rfl⟩ := Exec.det initB runB
      cases restA with
      | seq setupA fillA =>
        cases restB with
        | seq setupB fillB =>
          obtain bases := doneA.bp.trans (hp.bases.trans doneB.bp.symm)
          obtain ⟨setupTrace, _⟩ := FillSetup.code_rel _ _ _ _ _ _ ⟨bases, doneA.sp.trans (hp.stacks.trans doneB.sp.symm)⟩ setupA setupB
          obtain ⟨_, ca, runA, preparedA⟩ := FillSetup.code_ok _ p (initialized_setup hp.left doneA)
          obtain ⟨_, cb, runB, preparedB⟩ := FillSetup.code_ok _ p (initialized_setup hp.right doneB)
          obtain ⟨_, rfl⟩ := Exec.det setupA runA
          obtain ⟨_, rfl⟩ := Exec.det setupB runB
          obtain preparedBases := (preparedA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide) (by decide)).trans
            (bases.trans (preparedB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide) (by decide)).symm)
          have preparedStacks := preparedA.sp.trans
            ((doneA.sp.trans (hp.stacks.trans doneB.sp.symm)).trans
              preparedB.sp.symm)
          obtain initMatrices := (doneA.frame_word hp.left.initializing.space 232 (by decide) (Or.inr (by decide))).trans
            (hp.matrices.trans (doneB.frame_word hp.right.initializing.space 232 (by decide) (Or.inr (by decide))).symm)
          obtain matrices := preparedA.matrix.trans (initMatrices.trans preparedB.matrix.symm)
          obtain initOutputs := (doneA.frame_word hp.left.initializing.space 256 (by decide) (Or.inr (by decide))).trans
            (hp.outputs.trans (doneB.frame_word hp.right.initializing.space 256 (by decide) (Or.inr (by decide))).symm)
          obtain outputs := (preparedA.words 256 (by decide) (by decide)).trans
            (initOutputs.trans (preparedB.words 256 (by decide) (by decide)).symm)
          obtain initWorks := (doneA.frame_word hp.left.initializing.space 248 (by decide) (Or.inr (by decide))).trans
            (hp.works.trans (doneB.frame_word hp.right.initializing.space 248 (by decide) (Or.inr (by decide))).symm)
          obtain works := (preparedA.words 248 (by decide) (by decide)).trans
            (initWorks.trans (preparedB.words 248 (by decide) (by decide)).symm)
          obtain related : FillFinish.Related p (initial p s) (initial p t) _ _ :=
            ⟨preparedA.finish_ready (initialized_setup hp.left doneA) (initialized_output hp.left doneA) hp.left.positive,
              preparedB.finish_ready (initialized_setup hp.right doneB) (initialized_output hp.right doneB) hp.right.positive,
              preparedBases, preparedStacks, matrices, outputs, works,
              preparedA.represents (initialized_setup hp.left doneA) _ (initialized_represents hp.left doneA),
              preparedB.represents (initialized_setup hp.right doneB) _ (initialized_represents hp.right doneB), hp.indices⟩
          obtain ⟨fillTrace, _⟩ := FillFinish.code_rel v name p (initial p s) (initial p t) _ _ _ _ _ _ related fillA fillB
          exact ⟨by rw [initTrace, setupTrace, fillTrace], trivial⟩

end VG.Proof.Argon2.AArch64.InitFill
end

/-! Complete derivation reveals only its reviewed filling reference sequence. -/

namespace VG.Proof.Argon2.AArch64.InitialBody

open VG VG.AArch64 VG.Spec.Argon2
open VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt)

def initial (p : Params) (s : State) : FillState := initMemory p (initialHash p
  (Initial.inputBytes s passwordOffset passwordLenOffset)
  (Initial.inputBytes s saltOffset saltLenOffset)
  (Initial.inputBytes s secretOffset secretLenOffset)
  (Initial.inputBytes s adOffset adLenOffset))

structure Related (p : Params) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  hashing : Initial.Related s t
  matrices : FillKernel.matrix s = FillKernel.matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  indices : (Proof.Argon2.iterations p 0 p.passes (initial p s)).indices =
    (Proof.Argon2.iterations p 0 p.passes (initial p t)).indices

theorem code_rel (v : HPrime.Backend) (name : String) (p : Params) :
    RelCT isa (Related p) (Impl.Argon2.AArch64.InitialBody.code name v.hash) (fun _ _ => True) := by
  obtain hashed := ((Initial.code_rel v).mono (P' := Related p) (fun _ _ h => h.hashing)
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨Initial.initialHash_ok v s h.left.hashSpace h.left.inputs p h.left.header,
        Initial.initialHash_ok v t h.right.hashSpace h.right.inputs p h.right.header⟩)
  refine hashed.seq ((InitFill.code_rel v name p).mono ?_ (fun _ _ h => h))
  rintro a b ⟨_, s, t, hp, ⟨da, ha⟩, ⟨db, hb⟩⟩
  obtain baseA : FillKernel.matrix a = FillKernel.matrix s := ha.frame_word hp.left.hashSpace 232 (by decide) (by decide)
  obtain baseB : FillKernel.matrix b = FillKernel.matrix t := hb.frame_word hp.right.hashSpace 232 (by decide) (by decide)
  obtain outputA : FinalOutput.output a = FinalOutput.output s := ha.frame_word hp.left.hashSpace 256 (by decide) (by decide)
  obtain outputB : FinalOutput.output b = FinalOutput.output t := hb.frame_word hp.right.hashSpace 256 (by decide) (by decide)
  obtain workA : FinalOutput.work a = FinalOutput.work s := ha.frame_word hp.left.hashSpace 248 (by decide) (by decide)
  obtain workB : FinalOutput.work b = FinalOutput.work t := hb.frame_word hp.right.hashSpace 248 (by decide) (by decide)
  refine ⟨hashed_ready hp.left.filling hp.left.hashSpace ha, hashed_ready hp.right.filling hp.right.hashSpace hb,
    ha.x19.trans (hp.hashing.bp.trans hb.x19.symm), ha.sp.trans (hp.hashing.sp.trans hb.sp.symm),
    baseA.trans (hp.matrices.trans baseB.symm), outputA.trans (hp.outputs.trans outputB.symm),
    workA.trans (hp.works.trans workB.symm), ?_⟩
  unfold InitFill.initial
  rw [ha.x19, hb.x19, da, db]
  exact hp.indices

end VG.Proof.Argon2.AArch64.InitialBody
end

/-! Use exactly the flattened leakage allowance of the shared derive contract. -/

namespace VG.Proof.Argon2.AArch64.InitialBody

open VG VG.AArch64 VG.Spec.Argon2
open VG.Impl.Argon2.AArch64.Initial

def references (p : Params) (s : State) : List Nat := Spec.Argon2.references p
  (Initial.inputBytes s passwordOffset passwordLenOffset)
  (Initial.inputBytes s saltOffset saltLenOffset)
  (Initial.inputBytes s secretOffset secretLenOffset)
  (Initial.inputBytes s adOffset adLenOffset)

structure ReviewedRelated (p : Params) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  hashing : Initial.Related s t
  matrices : FillKernel.matrix s = FillKernel.matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  references : references p s = references p t

theorem ReviewedRelated.related {p : Params} {s t : State} (h : ReviewedRelated p s t) : Related p s t := by
  refine ⟨h.left, h.right, h.hashing, h.matrices, h.outputs, h.works, ?_⟩
  have parameters := h.left.filling.environment.parameters
  obtain positive : 0 < p.laneLen := by
    obtain segments := Proof.Argon2.laneLen_segments p parameters.lanesPositive
    have minimum := parameters.segment_bound.1
    omega_using [segments, minimum]
  obtain indices := Proof.Argon2.references_injective p positive _ _ _ _ _ _ _ _ h.references
  unfold initial
  rw [Proof.Argon2.iterations_fill, Proof.Argon2.iterations_fill]
  exact indices

theorem reviewed_rel (v : HPrime.Backend) (name : String) (p : Params) :
    RelCT isa (ReviewedRelated p) (Impl.Argon2.AArch64.InitialBody.code name v.hash) (fun _ _ => True) :=
  (code_rel v name p).mono (fun _ _ h => h.related) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.InitialBody
end

/-! Preserve precisely the reviewed leakage relation across parameter computation. -/

namespace VG.Proof.Argon2.AArch64.InitialBody

open VG VG.AArch64 VG.Spec.Argon2
open VG.Impl.Argon2.AArch64.Initial

theorem ReviewedRelated.of_state {s₁ s₂ t₁ t₂ : State} {p : Params}
    (h : ReviewedRelated p s₁ s₂) (k₁ : SameFrame s₁ t₁) (k₂ : SameFrame s₂ t₂)
    (length₁ : t₁.gpr .x21 = BitVec.ofNat 64 p.laneLen)
    (length₂ : t₂.gpr .x21 = BitVec.ofNat 64 p.laneLen) : ReviewedRelated p t₁ t₂ := by
  refine ⟨h.left.of_state k₁ length₁, h.right.of_state k₂ length₂, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨k₁.hashSpace h.hashing.left.space,
      fun input hi => k₁.input (h.hashing.left.inputs input hi)⟩,
      ⟨k₂.hashSpace h.hashing.right.space,
      fun input hi => k₂.input (h.hashing.right.inputs input hi)⟩, ?_, ?_, ?_, ?_⟩
    · rw [k₁.bp, k₂.bp]; exact h.hashing.bp
    · rw [k₁.bx, k₂.bx]; exact h.hashing.bx
    · rw [k₁.sp, k₂.sp]; exact h.hashing.sp
    · intro d hd; rw [k₁.word d, k₂.word d]; exact h.hashing.words d hd
  · unfold FillKernel.matrix; rw [k₁.mem, k₂.mem, k₁.bp, k₂.bp]; exact h.matrices
  · unfold FinalOutput.output; rw [k₁.mem, k₂.mem, k₁.bp, k₂.bp]; exact h.outputs
  · unfold FinalOutput.work; rw [k₁.mem, k₂.mem, k₁.bp, k₂.bp]; exact h.works
  · unfold VG.Proof.Argon2.AArch64.InitialBody.references
    rw [k₁.inputBytes passwordOffset passwordLenOffset, k₂.inputBytes passwordOffset passwordLenOffset,
      k₁.inputBytes saltOffset saltLenOffset, k₂.inputBytes saltOffset saltLenOffset,
      k₁.inputBytes secretOffset secretLenOffset, k₂.inputBytes secretOffset secretLenOffset,
      k₁.inputBytes adOffset adLenOffset, k₂.inputBytes adOffset adLenOffset]
    exact h.references

end VG.Proof.Argon2.AArch64.InitialBody
