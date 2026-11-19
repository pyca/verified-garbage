module

import VerifiedGarbage.Proof.Argon2.IterationsIndices
public import VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetupCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Verified
import VerifiedGarbage.Proof.Argon2.X86_64.InitialLit
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetup
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Correct
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Argon2.IterationsIndices
meta import VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetupCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Verified
meta import VerifiedGarbage.Proof.Argon2.X86_64.InitialLit
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetup
meta import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Correct
meta import VerifiedGarbage.Proof.Argon2.Dimensions
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Argon2.X86_64.InitialBody
public import VerifiedGarbage.Proof.Argon2.X86_64.InitFill
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Absorb
public import VerifiedGarbage.Impl.Argon2.X86_64.Initial
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
public import VerifiedGarbage.Proof.Argon2.Initial
public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Init
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Update
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Update
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Finalize
import VerifiedGarbage.Proof.Argon2.HPrime
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Impl.Argon2.X86_64.InitialBody
meta import VerifiedGarbage.Proof.Argon2.X86_64.InitFill
meta import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Absorb
meta import VerifiedGarbage.Impl.Argon2.X86_64.Initial
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Reduce
meta import VerifiedGarbage.Proof.Argon2.Initial
meta import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Init
meta import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
meta import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Update
meta import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Update
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Finalize
meta import VerifiedGarbage.Proof.Argon2.HPrime
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Argon2.X86_64.InitialBodyState`, which this module and modules that import it used -/

section

/-! ### `Argon2.X86_64.InitialBody`, which this module and modules that import it used -/

section

/-! ### `Argon2.X86_64.Initial`, which only this module used -/

section

/-! ### `Argon2.X86_64.InitialStart`, which only this module used -/

section

/-! ### `Argon2.X86_64.InitialArgs`, which only this module used -/

section

/-! # Argument handling for Argon2 H₀ -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
open VG.Impl.Argon2.X86_64.HPrime (at_)

theorem ea_at (s : State) (r : Reg) (d : Nat) :
    s.ea (at_ r d) = s.gpr r + BitVec.ofNat 64 d := by
  simp only [State.ea, at_, BitVec.ofInt_natCast]

theorem headerWord_ok (s : State) (source destination : Nat)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rbp + BitVec.ofNat 64 source) 8)
    (hw : InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 destination) 4) :
    WP isa (.block (headerWord source destination)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .rbx + BitVec.ofNat 64 destination)
        ((s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 source) 64).setWidth 32) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [headerWord, runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc,
    State.load64, State.store32, ea_at, RegUpd.gpr_setReg, RegUpd.wr_setReg,
    RegUpd.rd_setReg, RegUpd.mem_setReg, hr, hw, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, trivial, trivial⟩
  intro r hr
  simp only [hr, ite_false]

structure LengthArgs (s : State) (offset : Nat) (t : State) : Prop where
  length : t.gpr .r14 = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 offset) 64
  count : t.gpr .rsi = s.gpr .r12
  pointer : t.gpr .rdx = s.gpr .rbx + 792
  size : t.gpr .rcx = 4
  other : ∀ r, r ≠ .r14 → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = s.mem.writeW (s.gpr .rbx + 792)
    ((s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 offset) 64).setWidth 32)
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem lengthArgs_ok (s : State) (offset : Nat)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rbp + BitVec.ofNat 64 offset) 8)
    (hw : InRegions s.wr (s.gpr .rbx + 792) 4) :
    WP isa (.block (lengthArgs offset)) s (LengthArgs s offset) := by
  apply WP.of_runBlock
  simp only [lengthArgs, runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc,
    readSrc32, State.setReg32, State.load64, State.store32, execAlu, ea_at,
    RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.rd_setReg,
    RegUpd.mem_setReg, hr, hw, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    show BitVec.ofNat 64 792 = (792 : Addr) from rfl]
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
  intro r h1 h2 h3 h4
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h1, h2, h3, h4, ite_false]

structure InputArgs (s t : State) (offset : Nat) : Prop where
  total : t.gpr .r12 = s.gpr .r12 + 4
  count : t.gpr .rsi = s.gpr .r12 + 4
  pointer : t.gpr .rdx = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 offset) 64
  length : t.gpr .rcx = s.gpr .r14
  other : ∀ r, r ≠ .r12 → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem inputArgs_ok (s : State) (offset : Nat)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rbp + BitVec.ofNat 64 offset) 8) :
    WP isa (.block (inputArgs offset)) s (fun t => InputArgs s t offset) := by
  apply WP.of_runBlock
  simp only [inputArgs, runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc,
    State.load64, execAlu, ea_at, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_arithFlags, hr, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
  intro r h1 h2 h3 h4
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h1, h2, h3, h4, ite_false]

end VG.Proof.Argon2.X86_64.Initial

end

end


@[expose] public section

section

/-! Merged from `Proof.Argon2.X86_64.InitialPrep`. -/
section
/-! Merged from `Proof.Argon2.X86_64.InitialHeader`. -/
section
/-! # Writing and reading the six words of the H₀ header -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
open VG.Impl.Argon2.X86_64.HPrime (at_)
open VG.Spec.Blake2 (bytesAt)

def headerValue (s : State) (j : Nat) : BitVec 32 :=
  if j = 4 then 0x13 else (wordAt s (headerSource j)).setWidth 32

def headerMem (s : State) : Nat → Mem
  | 0 => s.mem
  | n + 1 => (headerMem s n).writeW (s.gpr .rbx + BitVec.ofNat 64 (768 + 4 * n))
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
    Frame [⟨s.gpr .rbx + 768, 24⟩] s.mem (headerMem s n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih =>
    exact (ih (by omega_using [hn])).writeW (List.mem_singleton_self _) _
      (by
        rw [show (768 : Addr) = BitVec.ofNat 64 768 from rfl, BitVec.ofNat_add,
          ← BitVec.add_assoc]
        exact Offset.contains_base _ (by omega_using [hn]) (by omega_using [hn]))

theorem headerMem_read (s : State) (n j : Nat) (hn : n ≤ 6) (hj : j < n) :
    (headerMem s n).readW (s.gpr .rbx + BitVec.ofNat 64 (768 + 4 * j)) 32 =
      headerValue s j := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold headerMem
    by_cases he : j = n
    · subst j; exact Mem.readW_writeW_self32 ..
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [he] : 768 + 4 * j + 4 ≤ 768 + 4 * n ∨
        768 + 4 * n + 4 ≤ 768 + 4 * j) (by omega_using [hn, hj]) (by omega_using [hn])) (by decide)]
      exact ih (by omega_using [hn]) (by omega_using [hj, he])

theorem headerMem_bytes (s : State) :
    bytesAt (headerMem s 6) (s.gpr .rbx + 768) 24 =
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
      t.mem = s.mem.writeW (s.gpr .rbx + BitVec.ofNat 64 (768 + 4 * j)) (headerValue s j) ∧
      Keeps s t := by
  obtain hw := h.write (768 + 4 * j) 4 (by omega_using [hj])
  have finish (t : State) (hm : t.mem = s.mem.writeW
      (s.gpr .rbx + BitVec.ofNat 64 (768 + 4 * j)) (headerValue s j))
      (regs : ∀ r, r ≠ .rax → t.gpr r = s.gpr r) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
      t.mem = s.mem.writeW (s.gpr .rbx + BitVec.ofNat 64 (768 + 4 * j)) (headerValue s j) ∧
        Keeps s t := by
    refine ⟨hm, fun r hr _ _ => regs r ?_, rd, wr, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rw [hm]
      exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
        (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
  unfold headerSlot
  split
  · next he =>
    subst j
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
      State.store32, ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.wr_setReg,
      hw, reduceCtorEq, ite_true, ite_false, Option.map_some,
      Option.some.injEq, exists_eq_left', BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
      BitVec.setWidth_eq]
    refine ⟨rfl, fun r hr _ _ => ?_, rfl, rfl, ?_⟩
    · have hn : r ≠ .rax := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [RegUpd.gpr_setReg, hn, ite_false]
    · exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
        (Offset.contains_base _ (by decide) (by decide))
  · next he =>
    refine (headerWord_ok s _ _ (h.readable _ (headerSource_slot j)) hw).mono ?_
    rintro t ⟨hm, regs, rd, wr⟩
    exact finish t (by simpa only [headerValue, he, ite_false, wordAt] using hm) regs rd wr

theorem headerWords_ok (s : State) (n : Nat) (hn : n ≤ 6) (h : Space s) :
    WP isa (.block ((List.range n).flatMap headerSlot)) s fun t =>
      t.mem = headerMem s n ∧ Keeps s t := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨rfl, fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine (ih (by omega_using [hn])).mono ?_
    rintro u ⟨hu, ku⟩
    refine (headerSlot_ok u n (by omega_using [hn]) (h.keeps ku)).mono ?_
    rintro t ⟨ht, kt⟩
    refine ⟨?_, ku.trans kt⟩
    rw [ht, ku.rbx, headerValue_keeps h ku, hu]
    rfl

end VG.Proof.Argon2.X86_64.Initial
end

/-! # H₀: preserving the stack across input argument preparation -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
open VG.Spec.Blake2 (bytesAt)

theorem LengthArgs.keeps {s t : State} {offset : Nat} (h : LengthArgs s offset t) :
    Keeps s t := by
  refine ⟨fun r hr _ h14 => ?_, h.rd, h.wr, ?_⟩
  · have hn : r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r h14 hn.1 hn.2.1 hn.2.2
  · rw [h.mem]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide) (by decide))

theorem InputArgs.keeps {s t : State} {offset : Nat} (h : InputArgs s t offset) :
    Keeps s t := by
  refine ⟨fun r hr h12 _ => ?_, h.rd, h.wr, ?_⟩
  · have hn : r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r h12 hn.1 hn.2.1 hn.2.2
  · rw [h.mem]; exact Frame.refl _ _

theorem LengthArgs.prefix {s t : State} {offset : Nat} (h : LengthArgs s offset t) :
    bytesAt t.mem (s.gpr .rbx + 792) 4 = Spec.Argon2.le32 (wordAt s offset).toNat := by
  rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (Or.inl rfl), h.mem,
    Mem.readW_writeW_self32]
  rfl

theorem LengthArgs.repr {s t : State} {offset : Nat} (h : LengthArgs s offset t)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Spec.Blake2.Repr Spec.Blake2.b h0 s.mem (s.gpr .rbx) d) :
    Spec.Blake2.Repr Spec.Blake2.b h0 t.mem (t.gpr .rbx) d := by
  rw [h.keeps.rbx]
  apply Proof.Blake2.X86_64.Stream.Update.repr_congr Proof.Blake2.X86_64.Stream.okB
    (mem := s.mem) _ repr
  intro i hi
  obtain f : Frame [⟨s.gpr .rbx + 792, 4⟩] s.mem t.mem := by
    rw [h.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  apply f.bytes (R := ⟨s.gpr .rbx, 192⟩) _ (show (192 : Nat) ≤ 2 ^ 64 from by decide) hi
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact Offset.base_disjoint _ (by decide) (by decide)

theorem InputArgs.repr {s t : State} {offset : Nat} (h : InputArgs s t offset)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Spec.Blake2.Repr Spec.Blake2.b h0 s.mem (s.gpr .rbx) d) :
    Spec.Blake2.Repr Spec.Blake2.b h0 t.mem (t.gpr .rbx) d := by
  rw [h.keeps.rbx, h.mem]; exact repr

theorem addCount_ok (s : State) :
    WP isa (.block [.alu .add .r12 (.reg .r14)]) s fun t =>
      t.gpr .r12 = s.gpr .r12 + s.gpr .r14 ∧ t.mem = s.mem ∧ Keeps s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r hr h12 _ => ?_, rfl, rfl, Frame.refl _ _⟩
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h12, ite_false]

end VG.Proof.Argon2.X86_64.Initial
end

/-! # H₀: absorb a length-prefixed byte-string input -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)
open VG.Proof.Argon2 (appendInput)

structure InputReady (s : State) (po lo : Nat) : Prop where
  space : Space s
  pointerSlot : po ∈ slots
  lengthSlot : lo ∈ slots
  pointerBound : po + 8 ≤ 272
  lengthBound : lo + 8 ≤ 272
  length : (wordAt s lo).toNat < 2 ^ 32
  cover : Covers [inputRegion s po lo] (s.rd ++ s.wr)
  work : (inputRegion s po lo).Disjoint ⟨s.gpr .rbx, 16384⟩
  stack : (inputRegion s po lo).Disjoint (below (s.gpr .rsp) 16)

theorem InputReady.keeps {s t : State} {po lo : Nat} (h : InputReady s po lo)
    (k : Keeps s t) : InputReady t po lo := by
  obtain reg := h.space.input_keeps k po lo h.pointerBound h.lengthBound
  refine ⟨h.space.keeps k, h.pointerSlot, h.lengthSlot, h.pointerBound, h.lengthBound,
    ?_, ?_, ?_, ?_⟩
  · rw [h.space.word_keeps k lo h.lengthBound]; exact h.length
  · rw [reg, k.rd, k.wr]; exact h.cover
  · rw [reg, k.rbx]; exact h.work
  · rw [reg, k.rsp]; exact h.stack

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

theorem absorb_ok (v : Proof.Blake2.X86_64.Backend) (s : State) (po lo : Nat)
    (h : InputReady s po lo) (d : List Byte)
    (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (s.gpr .rbx) d)
    (count : s.gpr .r12 = BitVec.ofNat 64 d.length)
    (bound : d.length + 4 + (wordAt s lo).toNat < 2 ^ 64) :
    WP isa (absorb (HPrime.hash v) po lo) s fun t =>
      Repr b (Spec.Blake2.init b 64 0) t.mem (t.gpr .rbx)
        (appendInput d (inputBytes s po lo)) ∧
      t.gpr .r12 = BitVec.ofNat 64 (appendInput d (inputBytes s po lo)).length ∧ Keeps s t := by
  unfold absorb
  refine WP.seq ((lengthArgs_ok s lo (h.space.readable lo h.lengthSlot)
    (by simpa using h.space.write 792 4 (by decide))).mono ?_)
  intro a ha
  have ka := ha.keeps
  obtain hA := h.keeps ka
  obtain lenA : (a.gpr .rcx).toNat = 4 := by rw [ha.size]; rfl
  obtain dataA : Covers [⟨a.gpr .rdx, (a.gpr .rcx).toNat⟩] (a.rd ++ a.wr) := by
    rw [ha.pointer, lenA, ka.rbx.symm]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨a.gpr .rbx, 16384⟩, List.mem_append_right _ hA.space.work,
      792, rfl, by change 792 + 4 ≤ 16384; decide⟩
  obtain dsA : (⟨a.gpr .rdx, (a.gpr .rcx).toNat⟩ : Region).Disjoint ⟨a.gpr .rbx, 192⟩ := by
    rw [ha.pointer, lenA, ka.rbx]
    exact (Offset.base_disjoint _ (by decide) (by decide)).symm
  obtain dwA : (⟨a.gpr .rdx, (a.gpr .rcx).toNat⟩ : Region).Disjoint ⟨a.gpr .rbx + 192, 576⟩ := by
    rw [ha.pointer, lenA, ka.rbx]
    exact Offset.disjoint _ (by decide) (by decide) (by decide)
  obtain sdA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .rdx, (a.gpr .rcx).toNat⟩ := by
    rw [ha.pointer, lenA, ka.rbx.symm]
    exact hA.space.stackWork.sub_right (Offset.sub_base _ (by decide))
  refine WP.seq ((HPrime.update_ok v a _ d (ha.repr _ _ repr)
    (ha.count.trans count) (by rw [lenA]; omega_using [bound]) hA.space.work dataA dsA dwA
    hA.space.stackWork sdA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, frameU⟩
  obtain ku : Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, HPrime.update_frame _ _ frameU⟩
  obtain ksu := ka.trans ku
  obtain hU := h.keeps ksu
  obtain prefixA : bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat =
      Spec.Argon2.le32 (wordAt s lo).toNat := by rw [ha.pointer, lenA]; exact ha.prefix
  obtain r12U : u.gpr .r12 = s.gpr .r12 :=
    (regsU _ (by decide)).trans (ha.other _ (by decide) (by decide) (by decide) (by decide))
  obtain r14U : u.gpr .r14 = wordAt s lo := (regsU _ (by decide)).trans ha.length
  refine WP.seq ((inputArgs_ok u po (hU.space.readable po h.pointerSlot)).mono ?_)
  intro x hx
  have kux := hx.keeps
  obtain ksx := ksu.trans kux
  obtain hX := h.keeps ksx
  obtain srcX : x.gpr .rdx = wordAt s po :=
    hx.pointer.trans (h.space.word_keeps ksu po h.pointerBound)
  obtain lenX : x.gpr .rcx = wordAt s lo := hx.length.trans r14U
  obtain r14X : x.gpr .r14 = wordAt s lo :=
    (hx.other _ (by decide) (by decide) (by decide) (by decide)).trans r14U
  obtain reprX : Repr b (Spec.Blake2.init b 64 0) x.mem (x.gpr .rbx)
      (d ++ Spec.Argon2.le32 (wordAt s lo).toNat) := by
    apply hx.repr
    rw [ku.rbx]
    simpa only [prefixA] using reprU
  obtain prefixLen : (d ++ Spec.Argon2.le32 (wordAt s lo).toNat).length = d.length + 4 := by
    rw [List.length_append, Proof.Argon2.le32_length]
  obtain countX : x.gpr .rsi = BitVec.ofNat 64 (d ++ Spec.Argon2.le32 (wordAt s lo).toNat).length := by
    rw [hx.count, r12U, count, prefixLen, BitVec.ofNat_add]; rfl
  obtain coverX : Covers [⟨x.gpr .rdx, (x.gpr .rcx).toNat⟩] (x.rd ++ x.wr) := by
    rw [srcX, lenX, ksx.rd, ksx.wr]
    exact h.cover
  obtain dsX : (⟨x.gpr .rdx, (x.gpr .rcx).toNat⟩ : Region).Disjoint ⟨x.gpr .rbx, 192⟩ := by
    rw [srcX, lenX, ksx.rbx]
    exact h.work.sub_right (Region.sub_prefix (by decide))
  obtain dwX : (⟨x.gpr .rdx, (x.gpr .rcx).toNat⟩ : Region).Disjoint ⟨x.gpr .rbx + 192, 576⟩ := by
    rw [srcX, lenX, ksx.rbx]
    exact h.work.sub_right (Offset.sub_base _ (by decide))
  obtain sdX : (below (x.gpr .rsp) 16).Disjoint ⟨x.gpr .rdx, (x.gpr .rcx).toNat⟩ := by
    rw [srcX, lenX, ksx.rsp]; exact h.stack.symm
  refine WP.seq ((HPrime.update_ok v x _ _ reprX countX
    (by rw [prefixLen, lenX]; exact bound) hX.space.work coverX dsX dwX hX.space.stackWork sdX).mono ?_)
  rintro y ⟨reprY, regsY, rdY, wrY, frameY⟩
  obtain ky : Keeps x y := Keeps.of_hash ⟨regsY, rdY, wrY, HPrime.update_frame _ _ frameY⟩
  obtain ksy := ksx.trans ky
  obtain r12Y : y.gpr .r12 = BitVec.ofNat 64 (d.length + 4) := by
    rw [regsY _ (by decide), hx.total, r12U, count, BitVec.ofNat_add]; rfl
  obtain r14Y : y.gpr .r14 = wordAt s lo := (regsY _ (by decide)).trans r14X
  obtain bytesX : bytesAt x.mem (x.gpr .rdx) (x.gpr .rcx).toNat = inputBytes s po lo := by
    rw [srcX, lenX]
    exact ksx.bytes (inputRegion s po lo) h.work h.stack (Nat.le_of_lt (wordAt s lo).isLt)
  refine (addCount_ok y).mono ?_
  rintro t ⟨ht12, hm, kt⟩
  refine ⟨?_, ?_, ksy.trans kt⟩
  · rw [kt.rbx, hm, ky.rbx]
    simpa only [appendInput, inputBytes_length, bytesX] using reprY
  · have hw : BitVec.ofNat 64 (wordAt s lo).toNat = wordAt s lo := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [ht12, r12Y, r14Y, ← hw, ← BitVec.ofNat_add,
      Proof.Argon2.appendInput_length, inputBytes_length]

end VG.Proof.Argon2.X86_64.Initial

end

/-! # H₀: initialize BLAKE2b and absorb the public parameter header -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
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
    WP isa (.block [.mov32 .rsi (.imm 64)]) s fun t =>
      t.gpr .rsi = 64 ∧ t.mem = s.mem ∧ HPrime.Keeps s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, Frame.refl _ _⟩
  obtain hn : r ≠ .rsi := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [RegUpd.gpr_setReg, hn, ite_false]

theorem initialCount_ok (s : State) :
    WP isa (.block [.mov32 .r12 (.imm 24)]) s fun t =>
      t.gpr .r12 = 24 ∧ t.mem = s.mem ∧ Keeps s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r _ h12 _ => ?_, rfl, rfl, Frame.refl _ _⟩
  simp only [RegUpd.gpr_setReg, h12, ite_false]

theorem start_ok (v : Proof.Blake2.X86_64.Backend) (s : State) (h : Space s) :
    WP isa (start (HPrime.hash v)) s fun t =>
      Repr b (Spec.Blake2.init b 64 0) t.mem (t.gpr .rbx) (headerBytes s) ∧
      t.gpr .r12 = 24 ∧ Keeps s t := by
  unfold start headerCode
  refine WP.seq ((digestLength_ok s).mono ?_)
  rintro a ⟨lenA, memA, ka'⟩
  obtain ka := Keeps.of_hash ka'
  obtain hA := h.keeps ka
  obtain retA : (below (a.gpr .rsp) 8).Disjoint ⟨a.gpr .rbx, 192⟩ := (hA.stackWork.sub_left (below_sub (by decide) (by decide))).sub_right
    (Region.sub_prefix (by decide : 192 ≤ 16384))
  refine WP.seq ((HPrime.init_ok v a (by rw [lenA]; exact ⟨by decide, by decide⟩)
    hA.work retA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, frameU⟩
  obtain ku : Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, HPrime.init_frame _ _ frameU⟩
  obtain ksu := ka.trans ku
  obtain hU := h.keeps ksu
  refine WP.seq ((headerWords_ok u 6 (by decide) hU).mono ?_)
  rintro w ⟨memW, kw⟩
  obtain ksw := ksu.trans kw
  obtain hW := h.keeps ksw
  obtain reprW : Repr b (Spec.Blake2.init b 64 0) w.mem (w.gpr .rbx) [] := by
    rw [kw.rbx]
    apply Proof.Blake2.X86_64.Stream.Update.repr_congr Proof.Blake2.X86_64.Stream.okB
      (mem := u.mem) _ (by simpa only [lenA, ku.rbx, show (64 : BitVec 64).toNat = 64 from rfl] using reprU)
    intro i hi
    rw [memW]
    apply (headerMem_frame u 6 (by decide)).bytes (R := ⟨u.gpr .rbx, 192⟩) _
      (show (192 : Nat) ≤ 2 ^ 64 from by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact Offset.base_disjoint _ (by decide) (by decide)
  obtain headW : bytesAt w.mem (w.gpr .rbx + 768) 24 = headerBytes s := by
    rw [kw.rbx, memW, headerMem_bytes]
    exact headerBytes_keeps h ksu
  refine WP.seq ((HPrime.absorbFixed_ok v w _ 768 24 (by decide) (by decide)
    reprW hW.work hW.stackWork).mono ?_)
  rintro x ⟨reprX, kx'⟩
  obtain kx := Keeps.of_hash kx'
  obtain ksx := ksw.trans kx
  refine (initialCount_ok x).mono ?_
  rintro t ⟨countT, memT, kt⟩
  refine ⟨?_, countT, ksx.trans kt⟩
  rw [kt.rbx, memT, kx.rbx]
  simpa only [headW, show BitVec.ofNat 64 768 = (768 : Addr) from rfl] using reprX

end VG.Proof.Argon2.X86_64.Initial

end

end


/-! Merged from `Proof.Argon2.X86_64.InitialFinish`. -/

@[expose] public section

section
/-! # H₀: finalize BLAKE2b and copy the digest into the derivation frame -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)

structure Finished (s t : State) : Prop where
  regs : ∀ r ∈ calleeSaved, r ≠ .r12 → r ≠ .r14 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16, ⟨s.gpr .rbp, 64⟩] s.mem t.mem

theorem finishCount_ok (s : State) :
    WP isa (.block [.mov .rsi (.reg .r12)]) s fun t =>
      t.gpr .rsi = s.gpr .r12 ∧ t.mem = s.mem ∧ HPrime.Keeps s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, Frame.refl _ _⟩
  obtain hn : r ≠ .rsi := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [RegUpd.gpr_setReg, hn, ite_false]

theorem finishOutput_ok (s : State) :
    WP isa (.block [.mov .r14 (.reg .rbp), .mov32 .rax (.imm 64)]) s fun t =>
      t.gpr .r14 = s.gpr .rbp ∧ t.gpr .rax = 64 ∧ t.mem = s.mem ∧ Keeps s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    State.setReg32, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg,
    RegUpd.mem_setReg]
  refine ⟨rfl, rfl, trivial, fun r hr h12 h14 => ?_, rfl, rfl, Frame.refl _ _⟩
  obtain hn : r ≠ .rax := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [RegUpd.gpr_setReg, hn, h14, ite_false]

theorem finish_ok (v : Proof.Blake2.X86_64.Backend) (s : State) (h : Space s)
    (d : List Byte) (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (s.gpr .rbx) d)
    (count : s.gpr .r12 = BitVec.ofNat 64 d.length) (bound : d.length < 2 ^ 64) :
    WP isa (finish (HPrime.hash v)) s fun t =>
      bytesAt t.mem (s.gpr .rbp) 64 = Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) d ∧
      Finished s t := by
  unfold finish
  refine WP.seq ((finishCount_ok s).mono ?_)
  rintro a ⟨countA, memA, ka'⟩
  obtain ka := Keeps.of_hash ka'
  obtain hA := h.keeps ka
  obtain reprA : Repr b (Spec.Blake2.init b 64 0) a.mem (a.gpr .rbx) d := by
    rw [memA, ka.rbx]; exact repr
  refine WP.seq ((HPrime.finalize_ok v a _ d reprA (countA.trans count) bound
    hA.work hA.stackWork).mono ?_)
  rintro u ⟨digestU, regsU, rdU, wrU, frameU⟩
  obtain ku : Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, HPrime.finalize_frame _ _ frameU⟩
  obtain ksu := ka.trans ku
  refine WP.seq ((finishOutput_ok u).mono ?_)
  rintro w ⟨dstW, countW, memW, kw⟩
  obtain ksw := ksu.trans kw
  obtain hW := h.keeps ksw
  obtain outW : ∀ i < 64, InRegions w.wr (w.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [dstW, ← kw.rbp]
    rcases hW.output with ⟨r, hr, hc⟩
    exact ⟨r, hr, hc.byte (by rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi] : i < 2 ^ 64)]; exact hi)⟩
  obtain sepW : (⟨w.gpr .rbx + 768, 64⟩ : Region).Disjoint ⟨w.gpr .r14, 64⟩ := by
    rw [dstW, ← kw.rbp]
    exact (hW.frameWork.sub_left (Region.sub_prefix (by decide : 64 ≤ 272))).symm.sub_left
      (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))
  refine (HPrime.copy_ok w 64 (by decide) (by decide) countW hW.work outW sepW).mono ?_
  intro t ht
  obtain sourceLength : (bytesAt w.mem (w.gpr .rbx + 768) 64).length = 64 := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨?_, fun r hr h12 h14 => ?_, ht.rd.trans ksw.rd, ht.wr.trans ksw.wr, ?_⟩
  · have dst : w.gpr .r14 = s.gpr .rbp := dstW.trans ksu.rbp
    rw [ht.mem]
    conv => lhs; arg 2; rw [← dst]
    obtain copied := HPrime.bytesAt_writeBytes w.mem (w.gpr .r14)
      (bytesAt w.mem (w.gpr .rbx + 768) 64) (by rw [sourceLength]; decide)
    rw [sourceLength] at copied
    rw [copied, memW, kw.rbx, ku.rbx]
    exact digestU
  · have hrax : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain hrcx : r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain hrdx : r ≠ .rdx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (ht.other r hrax hrcx hrdx h14).trans (ksw.regs r hr h12 h14)
  · apply Frame.trans (ksw.frame.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr.elim Or.inl (fun h => Or.inr (Or.inl h))))
    apply ht.frame.mono
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    rw [dstW, ksu.rbp]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))

end VG.Proof.Argon2.X86_64.Initial
end

/-! # Correctness of H₀ for every verified BLAKE2b backend -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)
open VG.Proof.Argon2 (appendInput)

abbrev inputs : List (Nat × Nat) :=
  [(passwordOffset, passwordLenOffset), (saltOffset, saltLenOffset),
   (secretOffset, secretLenOffset), (adOffset, adLenOffset)]

def message (s : State) (ps : List (Nat × Nat)) (d : List Byte) : List Byte :=
  ps.foldl (fun m p => appendInput m (inputBytes s p.1 p.2)) d

def inputSize (s : State) (ps : List (Nat × Nat)) : Nat :=
  (ps.map fun p => 4 + (wordAt s p.2).toNat).sum

def remaining (h : VG.Impl.Argon2.X86_64.HPrime.Hash) : List (Nat × Nat) → Prog isa
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
    f.rd.trans k.rd, f.wr.trans k.wr, ?_⟩
  apply (k.frame.mono ?_).trans
  · simpa only [k.rbx, k.rsp, k.rbp] using f.frame
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    exact hr.elim Or.inl (fun h => Or.inr (Or.inl h))

theorem remaining_ok (v : Proof.Blake2.X86_64.Backend) (ps : List (Nat × Nat))
    (s : State) (space : Space s) (ready : ∀ p ∈ ps, InputReady s p.1 p.2)
    (d : List Byte) (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (s.gpr .rbx) d)
    (count : s.gpr .r12 = BitVec.ofNat 64 d.length)
    (bound : d.length + inputSize s ps < 2 ^ 64) :
    WP isa (remaining (HPrime.hash v) ps) s fun t =>
      bytesAt t.mem (s.gpr .rbp) 64 =
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
      rw [ku.rbp] at digestT
      rw [message_keeps ps _ tailReady ku] at digestT
      exact digestT

theorem code_ok (v : Proof.Blake2.X86_64.Backend) (s : State) (space : Space s)
    (ready : ∀ p ∈ inputs, InputReady s p.1 p.2) :
    WP isa (code (HPrime.hash v)) s fun t =>
      bytesAt t.mem (s.gpr .rbp) 64 =
        Spec.Argon2.H 64 (message s inputs (headerBytes s)) ∧ Finished s t := by
  change WP isa (.seq (start (HPrime.hash v)) (remaining (HPrime.hash v) inputs)) s _
  refine WP.seq ((start_ok v s space).mono ?_)
  rintro u ⟨reprU, countU, ku⟩
  obtain count : u.gpr .r12 = BitVec.ofNat 64 (headerBytes s).length := by
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
  rw [ku.rbp, message_keeps inputs _ ready ku] at digestT
  rw [Proof.Argon2.H_stream, ← digestT]
  exact (List.take_of_length_le (by simp only [bytesAt, List.length_map, List.length_range,
    Nat.le_refl])).symm

/-- The public header is supplied by the enclosing argument-validation proof.
The byte-string contents remain unrestricted. -/
theorem initialHash_ok (v : Proof.Blake2.X86_64.Backend) (s : State) (space : Space s)
    (ready : ∀ p ∈ inputs, InputReady s p.1 p.2) (p : Spec.Argon2.Params)
    (header : headerBytes s = Proof.Argon2.initialHeader p) :
    WP isa (code (HPrime.hash v)) s fun t =>
      bytesAt t.mem (s.gpr .rbp) 64 = Spec.Argon2.initialHash p
        (inputBytes s passwordOffset passwordLenOffset) (inputBytes s saltOffset saltLenOffset)
        (inputBytes s secretOffset secretLenOffset) (inputBytes s adOffset adLenOffset) ∧
      Finished s t := by
  refine (code_ok v s space ready).mono ?_
  rintro t ⟨digest, frame⟩
  refine ⟨?_, frame⟩
  rw [header] at digest
  exact digest

end VG.Proof.Argon2.X86_64.Initial

end

end


/-! Merged from `Proof.Argon2.X86_64.InitialMetadata`. -/

@[expose] public section

section
/-! H₀ writes its digest into the frame while retaining all enclosing arguments. -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64

theorem Finished.rbp {s t : State} (h : Finished s t) : t.gpr .rbp = s.gpr .rbp :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Finished.rbx {s t : State} (h : Finished s t) : t.gpr .rbx = s.gpr .rbx :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Finished.rsp {s t : State} (h : Finished s t) : t.gpr .rsp = s.gpr .rsp :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Finished.frame_word {s t : State} (h : Finished s t) (space : Space s)
    (d : Nat) (bound : d + 8 ≤ 272) (afterDigest : 64 ≤ d) : wordAt t d = wordAt s d := by
  unfold wordAt
  rw [h.rbp]
  apply h.frame.readW (r := ⟨s.gpr .rbp + BitVec.ofNat 64 d, 8⟩)
    (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact space.frameWork.sub_left (Offset.sub_base _ bound) |>.sub_right
      (Region.sub_prefix (by decide))
  · exact space.frameStack.sub_left (Offset.sub_base _ bound)
  · simpa only [BitVec.add_zero] using
      Offset.disjoint (s.gpr .rbp) (d := d) (n := 8) (e := 0) (k := 64)
        (Or.inr afterDigest) (by omega_using [bound]) (by decide)

end VG.Proof.Argon2.X86_64.Initial
end

/-! Merged from `Proof.Argon2.X86_64.InitialBodyReady`. -/
section
/-! H₀ retains the allocation and parameter environment of complete derivation. -/

namespace VG.Proof.Argon2.X86_64.InitialBody

open VG VG.X86_64 VG.Spec.Argon2

theorem hashed_environment {s t : State} {p : Params} (h : InitFill.Ready p s) (space : Initial.Space s) (done : Initial.Finished s t) : FillSetup.Environment p t := by
  obtain base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word space 232 (by decide) (by decide)
  obtain work : AddressCalls.work t = AddressCalls.work s := done.frame_word space 248 (by decide) (by decide)
  have e := h.environment
  refine ⟨e.parameters, e.passesBound, e.layout.of_preserved done.rbp done.rsp base work done.rd done.wr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [done.rd, done.wr, done.rbp]; exact e.addressLayout.frameRead
    · rw [done.wr, work]; exact e.addressLayout.workWrite
    · rw [done.rbp, work]; exact e.addressLayout.frameWork
    · rw [done.rbp, done.rsp]; exact e.addressLayout.frameStack
    · rw [done.rsp, work]; exact e.addressLayout.stackWork
  · rw [done.rd, done.wr, done.rbp]; exact e.reads
  · rw [done.wr, done.rbp]; exact e.counterWrite
  · rw [done.wr, done.rbp]; exact e.passWrite
  · rw [base, work]; exact e.matrixWork
  · exact (done.frame_word space 240 (by decide) (by decide)).trans e.blocksWord
  · exact (done.frame_word space 72 (by decide) (by decide)).trans e.passesWord
  · exact (done.frame_word space 112 (by decide) (by decide)).trans e.variantWord
  · exact (done.frame_word space 184 (by decide) (by decide)).trans e.lanesWord

theorem hashed_output {s t : State} {p : Params} (h : InitFill.Ready p s) (space : Initial.Space s) (done : Initial.Finished s t) : FinalOutput.Ready p t := by
  obtain base : ReductionState.matrix t = ReductionState.matrix s := done.frame_word space 232 (by decide) (by decide)
  obtain output : FinalOutput.output t = FinalOutput.output s := done.frame_word space 256 (by decide) (by decide)
  obtain work : FinalOutput.work t = FinalOutput.work s := done.frame_word space 248 (by decide) (by decide)
  refine ⟨h.output.positive, h.output.bound, ?_,
    (done.frame_word space 264 (by decide) (by decide)).trans h.output.tagWord,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [done.rd, done.wr, done.rbp]; exact h.output.reads
  · rw [base, done.rd, done.wr]; exact h.output.input
  · rw [output, done.wr]; exact h.output.outputWrite
  · rw [work, done.wr]; exact h.output.workWrite
  · rw [base, work]; exact h.output.inputWork
  · rw [output, work]; exact h.output.outputWork
  · rw [done.rsp, base]; exact h.output.stackInput
  · rw [done.rsp, output]; exact h.output.stackOutput
  · rw [done.rsp, work]; exact h.output.stackWork

theorem hashed_ready {s t : State} {p : Params} (h : InitFill.Ready p s)
    (space : Initial.Space s) (done : Initial.Finished s t) : InitFill.Ready p t := by
  obtain base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word space 232 (by decide) (by decide)
  obtain work : FinalOutput.work t = FinalOutput.work s := done.frame_word space 248 (by decide) (by decide)
  refine ⟨?_, hashed_environment h space done, hashed_output h space done, h.positive, ?_⟩
  · constructor
    · rw [base]
      exact h.initializing.space.same done.wr done.rbp done.rbx done.rsp
    · rw [done.rd, done.wr, done.rbp]; exact h.initializing.memoryRead
    · rw [done.rd, done.wr, done.rbp]; exact h.initializing.lanesRead
    · rw [done.rd, done.wr, done.rbp]; exact h.initializing.blocksRead
    · exact (done.frame_word space 232 (by decide) (by decide)).trans h.initializing.memoryWord |>.trans base.symm
    · exact (done.frame_word space 184 (by decide) (by decide)).trans h.initializing.lanesWord
    · exact (done.frame_word space 240 (by decide) (by decide)).trans h.initializing.blocksWord
    · exact (done.regs .r13 (by decide) (by decide) (by decide)).trans h.initializing.laneLength
  · rw [done.rbx, work]; exact h.scratch

end VG.Proof.Argon2.X86_64.InitialBody
end

/-! H₀, initialization, every filling pass, and finalization agree with derive. -/

namespace VG.Proof.Argon2.X86_64.InitialBody

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64.Initial
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
  bp : t.gpr .rbp = s.gpr .rbp
  sp : t.gpr .rsp = s.gpr .rsp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (InitFill.writes s p) s.mem t.mem

theorem hash_frame {s t : State} {p : Params} (h : InitFill.Ready p s) (done : Initial.Finished s t) :
    Frame (InitFill.writes s p) s.mem t.mem := by
  apply done.frame.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨FinalOutput.work s, 16384⟩, by simp [InitFill.writes], by
      rw [h.scratch]; exact Region.sub_prefix (by decide)⟩
  · exact ⟨below (s.gpr .rsp) 24, by simp [InitFill.writes], below_sub (by decide) (by decide)⟩
  · exact ⟨⟨s.gpr .rbp, 72⟩, by simp [InitFill.writes], Region.sub_prefix (by decide)⟩

theorem code_ok [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State) (p : Params) (h : Ready p s) :
    WP isa (Impl.Argon2.X86_64.InitialBody.code name (HPrime.hash v)) s (Done s · p) := by
  unfold Impl.Argon2.X86_64.InitialBody.code
  refine WP.seq ((Initial.initialHash_ok v s h.hashSpace h.inputs p h.header).mono ?_)
  rintro a ⟨digest, hashed⟩
  refine (InitFill.code_ok v name a p (hashed_ready h.filling h.hashSpace hashed)).mono ?_
  intro t filled
  obtain base : FillKernel.matrix a = FillKernel.matrix s := hashed.frame_word h.hashSpace 232 (by decide) (by decide)
  obtain work : FinalOutput.work a = FinalOutput.work s := hashed.frame_word h.hashSpace 248 (by decide) (by decide)
  obtain output : FinalOutput.output a = FinalOutput.output s := hashed.frame_word h.hashSpace 256 (by decide) (by decide)
  refine ⟨?_, filled.bp.trans hashed.rbp, filled.sp.trans hashed.rsp,
    filled.rd.trans hashed.rd, filled.wr.trans hashed.wr, ?_⟩
  · have result := filled.digest
    rw [output, hashed.rbp, digest, InitFill.result_derive] at result
    exact result
  · have frame := filled.frame
    rw [InitFill.writes_eq s a p hashed.rbp hashed.rsp base work output] at frame
    exact (hash_frame h.filling hashed).trans frame

end VG.Proof.Argon2.X86_64.InitialBody

end

end

/-! The complete body depends on the frame, allocation, and computed lane length. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.InitialBody

open VG VG.X86_64 VG.Spec.Argon2

structure SameFrame (s t : State) : Prop where
  bp : t.gpr .rbp = s.gpr .rbp
  bx : t.gpr .rbx = s.gpr .rbx
  sp : t.gpr .rsp = s.gpr .rsp
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
  refine ⟨h.positive, h.bound, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    (h : InitFill.Ready p s) (laneLength : t.gpr .r13 = BitVec.ofNat 64 p.laneLen) :
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
    (k : SameFrame s t) (laneLength : t.gpr .r13 = BitVec.ofNat 64 p.laneLen) : Ready p t := by
  refine ⟨k.hashSpace h.hashSpace, fun input hi => k.input (h.inputs input hi), ?_,
    k.filling h.filling laneLength⟩
  have header : Initial.headerBytes t = Initial.headerBytes s := by
    unfold Initial.headerBytes
    simp only [Initial.headerValue, Initial.wordAt, k.mem, k.bp]
  exact header.trans h.header

end VG.Proof.Argon2.X86_64.InitialBody

end

end

/-! Merged from `Proof.Argon2.X86_64.InitialCTState`. -/

@[expose] public section

section
/-! Merged from `Proof.Argon2.X86_64.InitialBlocksCT`. -/
section
/-! # Constant time of H₀ header and input argument preparation

Only frame and scratch addresses affect these blocks' execution traces.
The relational proof of the complete derivation additionally tracks public
lengths and pointers across its BLAKE2b calls.
-/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial

def AgreeBases (s t : State) : Prop := s.gpr .rbp = t.gpr .rbp ∧ s.gpr .rbx = t.gpr .rbx

theorem agreeBases_taint {s t : State} (h : AgreeBases s t) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rbp, .rbx]) s t := by
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

theorem header_rel : RelCT isa AgreeBases headerCode (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp, .rbx])
    (fun _ _ h => agreeBases_taint h) (by taint_decide)

theorem lengthArgs_rel (offset : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs [.rbp, .rbx])
      (.block (lengthArgs offset)) hint).isSome = true) :
    RelCT isa AgreeBases (.block (lengthArgs offset)) (fun _ _ => True) := by
  obtain ⟨_, check⟩ := ct
  exact RelCT.taint (A := taint) (Taint.ofRegs [.rbp, .rbx])
    (fun _ _ h => agreeBases_taint h) check

theorem inputArgs_rel (offset : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs [.rbp])
      (.block (inputArgs offset)) hint).isSome = true) :
    RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (inputArgs offset)) (fun _ _ => True) := by
  obtain ⟨_, check⟩ := ct
  exact RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h)) check

end VG.Proof.Argon2.X86_64.Initial
end

/-! Public input metadata survives every hash call without relating input bytes. -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64

structure Ready (s : State) : Prop where
  space : Space s
  inputs : ∀ input ∈ inputs, InputReady s input.1 input.2

theorem Ready.keeps {s t : State} (h : Ready s) (k : Keeps s t) : Ready t :=
  ⟨h.space.keeps k, fun p hp => (h.inputs p hp).keeps k⟩

structure Related (s t : State) : Prop where
  left : Ready s
  right : Ready t
  bp : s.gpr .rbp = t.gpr .rbp
  bx : s.gpr .rbx = t.gpr .rbx
  sp : s.gpr .rsp = t.gpr .rsp
  words : ∀ d ∈ slots, wordAt s d = wordAt t d

theorem Related.keeps {s₁ s₂ t₁ t₂ : State} (h : Related s₁ s₂)
    (k₁ : Keeps s₁ t₁) (k₂ : Keeps s₂ t₂) : Related t₁ t₂ := by
  refine ⟨h.left.keeps k₁, h.right.keeps k₂, ?_, ?_, ?_, ?_⟩
  · rw [k₁.rbp, k₂.rbp, h.bp]
  · rw [k₁.rbx, k₂.rbx, h.bx]
  · rw [k₁.rsp, k₂.rsp, h.sp]
  · intro d hd
    obtain bound : ∀ d ∈ slots, d + 8 ≤ 272 := by decide
    rw [h.left.space.word_keeps k₁ d (bound d hd), h.right.space.word_keeps k₂ d (bound d hd)]
    exact h.words d hd

def RelatedRegs (rs : List Reg) (s t : State) : Prop :=
  Related s t ∧ HPrime.AgreeRegs rs s t

theorem hash_keeps_rel {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (saved : ∀ r ∈ rs, r ∈ calleeSaved)
    (ct : RelCT isa P c (fun _ _ => True))
    (pre : ∀ s t, P s t → RelatedRegs rs s t)
    (wp : ∀ s t, P s t → WP isa c s (HPrime.Keeps s) ∧ WP isa c t (HPrime.Keeps t)) :
    RelCT isa P c (RelatedRegs rs) := by
  apply (ct.wpDep wp).mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ha, hb⟩
  obtain h := pre s t hp
  refine ⟨h.1.keeps (Keeps.of_hash ha) (Keeps.of_hash hb), ?_⟩
  intro r hr
  rw [ha.regs r (saved r hr), hb.regs r (saved r hr)]
  exact h.2 r hr

theorem finalize_ready {s : State} (h : Ready s) : HPrime.FinalizeReady s :=
  ⟨h.space.work, h.space.stackWork⟩

end VG.Proof.Argon2.X86_64.Initial
end

/-! Merged from `Proof.Argon2.X86_64.InitialUpdateReady`. -/
section
/-! Permissions for the two updates of each length-prefixed H₀ input. -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64

theorem prefix_update_ready {s t : State} {lo : Nat} (h : Space s) (args : LengthArgs s lo t) :
    HPrime.UpdateReady t := by
  have k := args.keeps
  obtain ht := h.keeps k
  obtain len : (t.gpr .rcx).toNat = 4 := by rw [args.size]; rfl
  refine ⟨ht.work, ?_, ?_, ?_, ht.stackWork, ?_⟩
  · rw [args.pointer, len, ← k.rbx]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨t.gpr .rbx, 16384⟩, List.mem_append_right _ ht.work, 792, rfl, by change 792 + 4 ≤ 16384; decide⟩
  · rw [args.pointer, len, k.rbx]
    exact (Offset.base_disjoint _ (by decide) (by decide)).symm
  · rw [args.pointer, len, k.rbx]
    exact Offset.disjoint _ (d := 792) (n := 4) (e := 192) (k := 576) (by decide) (by decide) (by decide)
  · rw [args.pointer, len, ← k.rbx]
    exact ht.stackWork.sub_right (Offset.sub_base _ (by decide))

theorem input_update_ready {s t : State} {po lo : Nat} (h : InputReady s po lo)
    (length : s.gpr .r14 = wordAt s lo) (args : InputArgs s t po) : HPrime.UpdateReady t := by
  have k := args.keeps
  have ptr : t.gpr .rdx = wordAt s po := args.pointer
  obtain len : t.gpr .rcx = wordAt s lo := args.length.trans length
  refine ⟨(h.space.keeps k).work, ?_, ?_, ?_, (h.space.keeps k).stackWork, ?_⟩
  · rw [ptr, len, k.rd, k.wr]; exact h.cover
  · rw [ptr, len, k.rbx]; exact h.work.sub_right (Region.sub_prefix (by decide))
  · rw [ptr, len, k.rbx]; exact h.work.sub_right (Offset.sub_base _ (by decide))
  · rw [ptr, len, k.rsp]; exact h.stack.symm

structure LengthRelated (lo : Nat) (s t : State) : Prop where
  related : RelatedRegs [.r12, .r14] s t
  leftLength : s.gpr .r14 = wordAt s lo
  rightLength : t.gpr .r14 = wordAt t lo

theorem LengthRelated.hash_keeps {lo : Nat} {s t a b : State} (h : LengthRelated lo s t)
    (bound : lo + 8 ≤ 272) (ka : HPrime.Keeps s a) (kb : HPrime.Keeps t b) : LengthRelated lo a b := by
  refine ⟨⟨h.related.1.keeps (Keeps.of_hash ka) (Keeps.of_hash kb), ?_⟩, ?_, ?_⟩
  · intro r hr
    obtain saved : ∀ r ∈ ([.r12, .r14] : List Reg), r ∈ calleeSaved := by decide
    rw [ka.regs r (saved r hr), kb.regs r (saved r hr)]
    exact h.related.2 r hr
  · rw [ka.regs .r14 (by decide), h.related.1.left.space.word_keeps (Keeps.of_hash ka) lo bound]
    exact h.leftLength
  · rw [kb.regs .r14 (by decide), h.related.1.right.space.word_keeps (Keeps.of_hash kb) lo bound]
    exact h.rightLength

end VG.Proof.Argon2.X86_64.Initial
end

/-! Merged from `Proof.Argon2.X86_64.InitialStartCT`. -/
section
/-! H₀ initialization and its fixed parameter header have input-independent traces. -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial

theorem digestLength_rel : RelCT isa Related (.block [.mov32 .rsi (.imm 64)])
    (fun s t => Related s t ∧ s.gpr .rsi = 64 ∧ t.gpr .rsi = 64) := by
  obtain ct := (RelCT.taint (A := taint) (P := Related) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.mov32 .rsi (.imm 64)]) (by taint_decide)).wpDep
    (fun s t _ => ⟨digestLength_ok s, digestLength_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨la, _, ka⟩, ⟨lb, _, kb⟩⟩
  exact ⟨hp.keeps (Keeps.of_hash ka) (Keeps.of_hash kb), la, lb⟩

theorem init_hash_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (fun s t => Related s t ∧ s.gpr .rsi = 64 ∧ t.gpr .rsi = 64)
      (Impl.Argon2.X86_64.HPrime.init (HPrime.hash v)) Related := by
  have ready (s : State) (h : Ready s) (len : s.gpr .rsi = 64) : HPrime.InitReady s :=
    ⟨by rw [len]; decide, h.space.work,
      (h.space.stackWork.sub_left (below_sub (by decide) (by decide))).sub_right (Region.sub_prefix (by decide))⟩
  obtain ct := HPrime.init_rel v (P := fun s t => Related s t ∧ s.gpr .rsi = 64 ∧ t.gpr .rsi = 64)
    (fun s t ⟨h, ls, lt⟩ => ⟨ready s h.left ls, ready t h.right lt,
      h.bx, ls.trans lt.symm, h.sp⟩)
  obtain result := hash_keeps_rel [] (by simp) ct (fun _ _ h => ⟨h.1, by simp [HPrime.AgreeRegs]⟩)
    (fun s t ⟨h, ls, lt⟩ => ⟨HPrime.init_keeps v s (ready s h.left ls), HPrime.init_keeps v t (ready t h.right lt)⟩)
  exact result.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem header_state_rel : RelCT isa Related headerCode Related := by
  obtain ct := (header_rel.mono (P' := Related) (fun _ _ h => ⟨h.bp, h.bx⟩)
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨headerWords_ok s 6 (by decide) h.left.space, headerWords_ok t 6 (by decide) h.right.space⟩)
  exact ct.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, hp, ⟨_, ka⟩, ⟨_, kb⟩⟩ => hp.keeps ka kb)

theorem fixed_header_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa Related (Impl.Argon2.X86_64.HPrime.absorbFixed (HPrime.hash v) 768 24) Related := by
  obtain args := (RelCT.taint (A := taint) (P := Related) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block (Impl.Argon2.X86_64.HPrime.fixedArgs 768 24)) (by taint_decide)).wpDep
    (fun s t _ => ⟨HPrime.fixedArgs_ok s 768 24 (by decide) (by decide),
      HPrime.fixedArgs_ok t 768 24 (by decide) (by decide)⟩)
  obtain call := HPrime.update_rel v (P := fun a b => True ∧ ∃ s t, Related s t ∧
      HPrime.FixedArgs s a 768 24 ∧ HPrime.FixedArgs t b 768 24)
    (fun a b ⟨_, s, t, hp, ha, hb⟩ => ⟨HPrime.fixed_ready (finalize_ready hp.left) ha (by decide) (by decide),
      HPrime.fixed_ready (finalize_ready hp.right) hb (by decide) (by decide),
      by rw [ha.keeps.rbx, hb.keeps.rbx, hp.bx], by rw [ha.count, hb.count],
      by rw [ha.data, hb.data, hp.bx], by rw [ha.size, hb.size], by rw [ha.keeps.rsp, hb.keeps.rsp, hp.sp]⟩)
  obtain ct := args.seq call
  obtain result := hash_keeps_rel [] (by simp) ct (fun _ _ h => ⟨h, by simp [HPrime.AgreeRegs]⟩)
    (fun s t h => ⟨HPrime.absorbFixed_keeps v s 768 24 (finalize_ready h.left) (by decide) (by decide),
      HPrime.absorbFixed_keeps v t 768 24 (finalize_ready h.right) (by decide) (by decide)⟩)
  exact result.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem initialCount_rel : RelCT isa Related (.block [.mov32 .r12 (.imm 24)]) (RelatedRegs [.r12]) := by
  obtain ct := (RelCT.taint (A := taint) (P := Related) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.mov32 .r12 (.imm 24)]) (by taint_decide)).wpDep
    (fun s t _ => ⟨initialCount_ok s, initialCount_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨la, _, ka⟩, ⟨lb, _, kb⟩⟩
  refine ⟨hp.keeps ka kb, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact la.trans lb.symm

theorem start_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa Related (start (HPrime.hash v)) (RelatedRegs [.r12]) :=
  digestLength_rel.seq ((init_hash_rel v).seq (header_state_rel.seq
    ((fixed_header_rel v).seq initialCount_rel)))

end VG.Proof.Argon2.X86_64.Initial
end

/-! Merged from `Proof.Argon2.X86_64.InitialFinishCT`. -/
section
/-! H₀ finalization and its fixed-size digest copy reveal no input contents. -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial

theorem finishCount_rel : RelCT isa (RelatedRegs [.r12]) (.block [.mov .rsi (.reg .r12)])
    (fun s t => RelatedRegs [.r12] s t ∧ s.gpr .rsi = t.gpr .rsi) := by
  obtain ct := (RelCT.taint (A := taint) (P := RelatedRegs [.r12]) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.mov .rsi (.reg .r12)]) (by taint_decide)).wpDep
    (fun s t _ => ⟨finishCount_ok s, finishCount_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨ca, _, ka⟩, ⟨cb, _, kb⟩⟩
  refine ⟨⟨hp.1.keeps (Keeps.of_hash ka) (Keeps.of_hash kb), ?_⟩, ?_⟩
  · intro r hr
    simp only [List.mem_singleton] at hr; subst r
    rw [ka.regs .r12 (by decide), kb.regs .r12 (by decide)]
    exact hp.2 _ (by simp)
  · rw [ca, cb]; exact hp.2 _ (by simp)

theorem finalize_hash_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (fun s t => RelatedRegs [.r12] s t ∧ s.gpr .rsi = t.gpr .rsi)
      (Impl.Argon2.X86_64.HPrime.finalize (HPrime.hash v)) Related := by
  obtain ct := HPrime.finalize_rel v (P := fun s t => RelatedRegs [.r12] s t ∧ s.gpr .rsi = t.gpr .rsi)
    (fun s t h => ⟨finalize_ready h.1.1.left, finalize_ready h.1.1.right, h.1.1.bx, h.2, h.1.1.sp⟩)
  obtain result := hash_keeps_rel [] (by simp) ct (fun _ _ h => ⟨h.1.1, by simp [HPrime.AgreeRegs]⟩)
    (fun s t h => ⟨HPrime.finalize_keeps v s (finalize_ready h.1.1.left),
      HPrime.finalize_keeps v t (finalize_ready h.1.1.right)⟩)
  exact result.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem finishOutput_rel : RelCT isa Related
    (.block [.mov .r14 (.reg .rbp), .mov32 .rax (.imm 64)])
      (HPrime.AgreeRegs [.rbx, .r14, .rax]) := by
  obtain ct := (RelCT.taint (A := taint) (P := Related) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.mov .r14 (.reg .rbp), .mov32 .rax (.imm 64)]) (by taint_decide)).wpDep
    (fun s t _ => ⟨finishOutput_ok s, finishOutput_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨da, la, _, ka⟩, ⟨db, lb, _, kb⟩⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [ka.rbx, kb.rbx, hp.bx]
  · rw [da, db, hp.bp]
  · rw [la, lb]

theorem copy_digest_rel : RelCT isa (HPrime.AgreeRegs [.rbx, .r14, .rax])
    Impl.Argon2.X86_64.HPrime.copy (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbx, .r14, .rax])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem finish_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (RelatedRegs [.r12]) (finish (HPrime.hash v)) (fun _ _ => True) :=
  finishCount_rel.seq ((finalize_hash_rel v).seq (finishOutput_rel.seq copy_digest_rel))

end VG.Proof.Argon2.X86_64.Initial
end

/-! Merged from `Proof.Argon2.X86_64.InitialCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.InitialAbsorbCT`. -/
section
/-! H₀ updates depend on public lengths and pointers, never on input contents. -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial

def PrefixRelated (lo : Nat) (a b : State) : Prop :=
  True ∧ ∃ s t, RelatedRegs [.r12] s t ∧ LengthArgs s lo a ∧ LengthArgs t lo b

theorem prefix_rel (v : Proof.Blake2.X86_64.Backend) (lo : Nat) (slot : lo ∈ slots)
    (bound : lo + 8 ≤ 272)
    (check : ∃ hint, (taint.check (Taint.ofRegs [.rbp, .rbx]) (.block (lengthArgs lo)) hint).isSome = true) :
    RelCT isa (RelatedRegs [.r12])
      (.seq (.block (lengthArgs lo)) (Impl.Argon2.X86_64.HPrime.update (HPrime.hash v))) (LengthRelated lo) := by
  obtain args := ((lengthArgs_rel lo check).mono (P' := RelatedRegs [.r12])
    (fun _ _ h => ⟨h.1.bp, h.1.bx⟩) (fun _ _ h => h)).wpDep
    (fun s t h => ⟨lengthArgs_ok s lo (h.1.left.space.readable lo slot)
      (by simpa using h.1.left.space.write 792 4 (by decide)),
      lengthArgs_ok t lo (h.1.right.space.readable lo slot)
      (by simpa using h.1.right.space.write 792 4 (by decide))⟩)
  obtain call := HPrime.update_rel v (P := PrefixRelated lo) (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨prefix_update_ready hp.1.left.space ha, prefix_update_ready hp.1.right.space hb,
      by rw [ha.keeps.rbx, hb.keeps.rbx, hp.1.bx], by rw [ha.count, hb.count]; exact hp.2 _ (by simp),
      by rw [ha.pointer, hb.pointer, hp.1.bx], by rw [ha.size, hb.size],
      by rw [ha.keeps.rsp, hb.keeps.rsp, hp.1.sp]⟩)
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
        · rw [ha.other _ (by decide) (by decide) (by decide) (by decide),
            hb.other _ (by decide) (by decide) (by decide) (by decide)]
          exact hp.2 _ (by simp)
        · rw [ha.length, hb.length]; exact hp.1.words lo slot
      · rw [hp.1.left.space.word_keeps ha.keeps lo bound]; exact ha.length
      · rw [hp.1.right.space.word_keeps hb.keeps lo bound]; exact hb.length
    exact prepared.hash_keeps bound ka kb)
  exact args.seq finished

def InputRelated (lo po : Nat) (a b : State) : Prop :=
  True ∧ ∃ s t, LengthRelated lo s t ∧ InputArgs s a po ∧ InputArgs t b po

theorem input_rel (v : Proof.Blake2.X86_64.Backend) (po lo : Nat) (input : (po, lo) ∈ inputs)
    (check : ∃ hint, (taint.check (Taint.ofRegs [.rbp]) (.block (inputArgs po)) hint).isSome = true) :
    RelCT isa (LengthRelated lo)
      (.seq (.block (inputArgs po)) (Impl.Argon2.X86_64.HPrime.update (HPrime.hash v))) (LengthRelated lo) := by
  obtain args := ((inputArgs_rel po check).mono (P' := LengthRelated lo)
    (fun _ _ h => h.related.1.bp) (fun _ _ h => h)).wpDep
    (fun s t h => ⟨inputArgs_ok s po (h.related.1.left.space.readable po (h.related.1.left.inputs _ input).pointerSlot),
      inputArgs_ok t po (h.related.1.right.space.readable po (h.related.1.right.inputs _ input).pointerSlot)⟩)
  obtain call := HPrime.update_rel v (P := InputRelated lo po) (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨input_update_ready (hp.related.1.left.inputs _ input) hp.leftLength ha,
      input_update_ready (hp.related.1.right.inputs _ input) hp.rightLength hb,
      by rw [ha.keeps.rbx, hb.keeps.rbx, hp.related.1.bx],
      by rw [ha.count, hb.count, hp.related.2 .r12 (by simp)],
      by rw [ha.pointer, hb.pointer]; exact hp.related.1.words po (hp.related.1.left.inputs _ input).pointerSlot,
      by rw [ha.length, hb.length]; exact hp.related.2 .r14 (by simp),
      by rw [ha.keeps.rsp, hb.keeps.rsp, hp.related.1.sp]⟩)
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
        · rw [ha.total, hb.total, hp.related.2 .r12 (by simp)]
        · rw [ha.other _ (by decide) (by decide) (by decide) (by decide),
            hb.other _ (by decide) (by decide) (by decide) (by decide)]
          exact hp.related.2 .r14 (by simp)
      · rw [left.space.word_keeps ha.keeps lo left.lengthBound,
          ha.other _ (by decide) (by decide) (by decide) (by decide)]
        exact hp.leftLength
      · rw [right.space.word_keeps hb.keeps lo right.lengthBound,
          hb.other _ (by decide) (by decide) (by decide) (by decide)]
        exact hp.rightLength
    exact prepared.hash_keeps left.lengthBound ka kb)
  exact args.seq finished

theorem addCount_rel (lo : Nat) :
    RelCT isa (LengthRelated lo) (.block [.alu .add .r12 (.reg .r14)]) (RelatedRegs [.r12]) := by
  obtain ct := (RelCT.taint (A := taint) (P := LengthRelated lo) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.alu .add .r12 (.reg .r14)]) (by taint_decide)).wpDep
    (fun s t _ => ⟨addCount_ok s, addCount_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨ca, _, ka⟩, ⟨cb, _, kb⟩⟩
  refine ⟨hp.related.1.keeps ka kb, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  rw [ca, cb, hp.related.2 .r12 (by simp), hp.related.2 .r14 (by simp)]

theorem absorb_rel (v : Proof.Blake2.X86_64.Backend) (po lo : Nat) (input : (po, lo) ∈ inputs)
    (lengthCheck : ∃ hint, (taint.check (Taint.ofRegs [.rbp, .rbx]) (.block (lengthArgs lo)) hint).isSome = true)
    (pointerCheck : ∃ hint, (taint.check (Taint.ofRegs [.rbp]) (.block (inputArgs po)) hint).isSome = true) :
    RelCT isa (RelatedRegs [.r12]) (absorb (HPrime.hash v) po lo) (RelatedRegs [.r12]) := by
  obtain slot : lo ∈ slots := by
    obtain all : ∀ p ∈ inputs, p.2 ∈ slots := by decide
    exact all _ input
  obtain bound : lo + 8 ≤ 272 := by
    obtain all : ∀ d ∈ slots, d + 8 ≤ 272 := by decide
    exact all lo slot
  exact ((prefix_rel v lo slot bound lengthCheck).seq
    (((input_rel v po lo input pointerCheck).seq (addCount_rel lo)).assoc)).assoc

end VG.Proof.Argon2.X86_64.Initial
end

/-! Complete H₀ is constant time for every verified BLAKE2b backend. -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial

theorem code_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa Related (code (HPrime.hash v)) (fun _ _ => True) :=
  (start_rel v).seq
    ((absorb_rel v passwordOffset passwordLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    ((absorb_rel v saltOffset saltLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    ((absorb_rel v secretOffset secretLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    ((absorb_rel v adOffset adLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
      (finish_rel v)))))

end VG.Proof.Argon2.X86_64.Initial
end

/-! Merged from `Proof.Argon2.X86_64.InitialBodyReviewedCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.InitialBodyCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.InitFillCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FinishStageCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FinalOutputCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FinalCallCT`. -/
section
/-! # The final H′ call leak only their public argument registers -/

namespace VG.Proof.Argon2.X86_64.FinalCall

open VG VG.X86_64
open VG.Impl.Argon2.X86_64.HPrime (code)

theorem hPrime_call_rel (v : Proof.Blake2.X86_64.Backend) (name : String) (len : Nat)
    {P : State → State → Prop}
    (pre : ∀ s t, P s t → CallReady len s ∧ CallReady len t ∧
      s.gpr .rsi = 1024 ∧ t.gpr .rsi = 1024 ∧ s.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rcx = BitVec.ofNat 64 len ∧
      s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rdx = t.gpr .rdx ∧
      s.gpr .r8 = t.gpr .r8 ∧ s.gpr .rsp = t.gpr .rsp) :
    RelCT isa P (.call name (code (HPrime.hash v))) (fun _ _ => True) := by
  apply RelCT.callEx (k := HPrime.localContract) (HPrime.code_correct v) (HPrime.code_ct v)
  intro s t hp
  obtain ⟨hs, ht, ls, lt, os, ot, di, dx, r8, sp⟩ := pre s t hp
  obtain ⟨ps, cs, ws⟩ := hPrime_call_hyps len s hs ls os
  obtain ⟨pt, ct, wt⟩ := hPrime_call_hyps len t ht lt ot
  refine ⟨_, _, _, _, ps, pt, ?_, cs, ws, ct, wt, sp⟩
  change s.callEntry.gpr .rdi = t.callEntry.gpr .rdi ∧
    s.callEntry.gpr .rsi = t.callEntry.gpr .rsi ∧
    s.callEntry.gpr .rdx = t.callEntry.gpr .rdx ∧
    s.callEntry.gpr .rcx = t.callEntry.gpr .rcx ∧
    s.callEntry.gpr .r8 = t.callEntry.gpr .r8 ∧
    s.callEntry.gpr .rsp = t.callEntry.gpr .rsp
  simp only [State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_rsp]
  exact ⟨di, ls.trans lt.symm, dx, os.trans ot.symm, r8, congrArg (· - 8) sp⟩

end VG.Proof.Argon2.X86_64.FinalCall
end

/-! Final hashing exposes only the public tag length and pointers, for any hash backend. -/

namespace VG.Proof.Argon2.X86_64.FinalOutput

open VG VG.X86_64 VG.Spec.Argon2

structure Related (p : Params) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : ReductionState.matrix s = ReductionState.matrix t
  outputs : output s = output t
  works : work s = work t

structure NextRelated (p : Params) (s t : State) : Prop where
  left : FinalCall.CallReady p.tagLen s
  right : FinalCall.CallReady p.tagLen t
  leftInputLength : s.gpr .rsi = 1024
  rightInputLength : t.gpr .rsi = 1024
  leftOutputLength : s.gpr .rcx = BitVec.ofNat 64 p.tagLen
  rightOutputLength : t.gpr .rcx = BitVec.ofNat 64 p.tagLen
  inputs : s.gpr .rdi = t.gpr .rdi
  outputs : s.gpr .rdx = t.gpr .rdx
  works : s.gpr .r8 = t.gpr .r8
  stacks : s.gpr .rsp = t.gpr .rsp

theorem args_trace : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block Impl.Argon2.X86_64.FinalOutput.args) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

theorem args_rel (p : Params) : RelCT isa (Related p)
    (.block Impl.Argon2.X86_64.FinalOutput.args) (NextRelated p) := by
  obtain trace := args_trace.mono (P' := Related p) (fun _ _ h => h.bases) (fun _ _ h => h)
  obtain full := trace.wpDep (fun s t h => ⟨args_ok s h.left.reads, args_ok t h.right.reads⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.ready hp.left, hb.ready hp.right, ha.inputLength, hb.inputLength,
    ha.outputLength.trans hp.left.tagWord, hb.outputLength.trans hp.right.tagWord,
    ha.input.trans (hp.matrices.trans hb.input.symm), ha.output.trans (hp.outputs.trans hb.output.symm),
    ha.work.trans (hp.works.trans hb.work.symm),
    (ha.regs .rsp (by simp [calleeSaved])).trans (hp.stacks.trans (hb.regs .rsp (by simp [calleeSaved])).symm)⟩

theorem code_rel (v : Proof.Blake2.X86_64.Backend) (name : String) (p : Params) :
    RelCT isa (Related p) (Impl.Argon2.X86_64.FinalOutput.code name (HPrime.hash v)) (fun _ _ => True) :=
  (args_rel p).seq (FinalCall.hPrime_call_rel v name p.tagLen (fun _ _ h =>
    ⟨h.left, h.right, h.leftInputLength, h.rightInputLength, h.leftOutputLength, h.rightOutputLength,
      h.inputs, h.outputs, h.works, h.stacks⟩))

end VG.Proof.Argon2.X86_64.FinalOutput
end

/-! Complete finalization has a public trace for every BLAKE2b backend. -/

namespace VG.Proof.Argon2.X86_64.Finish

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (leftMemory rightMemory : Array Block) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : matrix s = matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  leftMatrix : Proof.Argon2.Represents s.mem (matrix s) p.blocks leftMemory
  rightMatrix : Proof.Argon2.Represents t.mem (matrix t) p.blocks rightMemory

theorem code_rel (v : Proof.Blake2.X86_64.Backend) (name : String) (p : Params)
    (leftMemory rightMemory : Array Block) :
    RelCT isa (Related p leftMemory rightMemory) (Impl.Argon2.X86_64.Finish.code name (HPrime.hash v))
      (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq reduceA outputA =>
    cases eb with
    | seq reduceB outputB =>
      obtain related : ReductionInit.Related p leftMemory rightMemory s t :=
        ⟨hp.left.reduction, hp.right.reduction, hp.bases, hp.matrices, hp.leftMatrix, hp.rightMatrix⟩
      obtain ⟨reduceTrace, _⟩ := FinalReduction.code_rel p hp.left.reduction.allocation.positive
        leftMemory rightMemory _ _ _ _ _ _ related reduceA reduceB
      obtain ⟨_, sa, runA, doneA⟩ := FinalReduction.code_ok s p hp.left.reduction leftMemory hp.leftMatrix
      obtain ⟨_, sb, runB, doneB⟩ := FinalReduction.code_ok t p hp.right.reduction rightMemory hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det reduceA runA
      obtain ⟨_, rfl⟩ := Exec.det reduceB runB
      obtain finalRelated : FinalOutput.Related p _ _ :=
        ⟨output_ready hp.left doneA, output_ready hp.right doneB,
          (doneA.regs .rbp (by simp [calleeSaved]) (by decide)).trans
            (hp.bases.trans (doneB.regs .rbp (by simp [calleeSaved]) (by decide)).symm),
          (doneA.regs .rsp (by simp [calleeSaved]) (by decide)).trans
            (hp.stacks.trans (doneB.regs .rsp (by simp [calleeSaved]) (by decide)).symm),
          doneA.base.trans (hp.matrices.trans doneB.base.symm),
          (frame_word hp.left.reduction doneA 256 (by decide)).trans
            (hp.outputs.trans (frame_word hp.right.reduction doneB 256 (by decide)).symm),
          (frame_word hp.left.reduction doneA 248 (by decide)).trans
            (hp.works.trans (frame_word hp.right.reduction doneB 248 (by decide)).symm)⟩
      obtain ⟨outputTrace, _⟩ := FinalOutput.code_rel v name p _ _ _ _ _ _ finalRelated outputA outputB
      exact ⟨by rw [reduceTrace, outputTrace], trivial⟩

end VG.Proof.Argon2.X86_64.Finish
end

/-! Merged from `Proof.Argon2.X86_64.FillSlicesCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillSlicesBodyCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillSliceCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillLanesCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillLanesBodyCT`. -/
section
/-! Lane iteration preserves public allocations and loops on the public lane count. -/

namespace VG.Proof.Argon2.X86_64.FillLanes

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillLanes

theorem advance_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp) (.block advance) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

structure NextRelated (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  ready : SegmentSetup.RelatedReady p pass lane slice s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel [CompressImpl] (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (SegmentSetup.Related p pass lane slice leftState rightState) body
      (fun s t => s.cf = t.cf ∧ (lane + 1 < p.lanes → NextRelated p pass (lane + 1) slice
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
      obtain bases := (filledA.regs .rbp (by simp [calleeSaved]) (by decide)).trans
        (hp.ready.bases.trans (filledB.regs .rbp (by simp [calleeSaved]) (by decide)).symm)
      obtain ⟨advancedTrace, _⟩ := advance_rel _ _ _ _ _ _ bases advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := body_ok s p pass lane slice hp.ready.left leftState hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := body_ok t p pass lane slice hp.ready.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentB advanceB) runB
      refine ⟨by rw [segmentTrace, advancedTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨⟨doneA.next active, doneB.next active, ?_, ?_,
        doneA.matrix.trans (hp.ready.matrices.trans doneB.matrix.symm),
        doneA.work.trans (hp.ready.work.trans doneB.work.symm)⟩, doneA.represented, doneB.represented⟩
      · exact (doneA.regs .rbp (by simp [calleeSaved]) (by decide) (by decide)).trans
          (hp.ready.bases.trans (doneB.regs .rbp (by simp [calleeSaved]) (by decide) (by decide)).symm)
      · exact (doneA.regs .rsp (by simp [calleeSaved]) (by decide) (by decide)).trans
          (hp.ready.stacks.trans (doneB.regs .rsp (by simp [calleeSaved]) (by decide) (by decide)).symm)

end VG.Proof.Argon2.X86_64.FillLanes
end

/-! The lane loop exposes only the slice's specified reference log. -/

namespace VG.Proof.Argon2.X86_64.FillLanes

open VG VG.X86_64 VG.Spec.Argon2

structure Related (p : Params) (pass lane slice count : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  ready : SegmentSetup.RelatedReady p pass lane slice s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.lanes p pass slice lane count leftState).indices =
    (Proof.Argon2.lanes p pass slice lane count rightState).indices

theorem loop_rel [CompressImpl] (p : Params) (pass lane slice count : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    RelCT isa (Related p pass lane slice count leftState rightState) Impl.Argon2.X86_64.FillLanes.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (lane : Nat) (leftState rightState : FillState),
    lane + n = p.lanes ∧ 0 < n ∧ Related p pass lane slice n leftState rightState s t
  obtain steps : ∀ n, RelCT isa (I n) Impl.Argon2.X86_64.FillLanes.body fun s t =>
      isa.eval .b s = isa.eval .b t ∧ (isa.eval .b s = some false → True) ∧
        (isa.eval .b s = some true → ∃ m < n, I m s t) := by
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
      · simp only [eval, flags]
      · intro taken
        obtain active : j + 1 < p.lanes := by
          simp only [eval, done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        obtain ⟨ready, matrixA, matrixB⟩ := next active
        have indices := hp.indices
        rw [Proof.Argon2.lanes_succ, Proof.Argon2.lanes_succ] at indices
        exact ⟨n, by omega_using [], j + 1, Proof.Argon2.segment p pass j slice 0 p.segmentLen ls,
          Proof.Argon2.segment p pass j slice 0 p.segmentLen rs, by omega_using [endLane], by omega_using [endLane, active], ready, matrixA, matrixB, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨lane, leftState, rightState, endLane, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.FillLanes
end

/-! A complete slice exposes only its specified reference log. -/

namespace VG.Proof.Argon2.X86_64.FillSlice

open VG VG.X86_64 VG.Spec.Argon2

structure Related (p : Params) (pass slice : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : Ready p pass slice s
  right : Ready p pass slice t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.lanes p pass slice 0 p.lanes leftState).indices =
    (Proof.Argon2.lanes p pass slice 0 p.lanes rightState).indices

theorem setup_trace : RelCT isa (fun _ _ : State => True) (.block Impl.Argon2.X86_64.FillSlice.setup) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)

theorem setup_public_rel (p : Params) (pass slice : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass slice leftState rightState) (.block Impl.Argon2.X86_64.FillSlice.setup)
      (FillLanes.Related p pass 0 slice p.lanes leftState rightState) := by
  obtain trace := setup_trace.mono (P' := Related p pass slice leftState rightState)
    (fun _ _ _ => trivial) (fun _ _ h => h)
  obtain full := trace.wpDep (fun s t h => ⟨setup_ok s p pass slice h.left, setup_ok t p pass slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨⟨ha.ready, hb.ready, ?_, ?_, ?_, ?_⟩, ?_, ?_, hp.indices⟩
  · rw [ha.keeps.regs .rbp (by decide), hb.keeps.regs .rbp (by decide)]; exact hp.bases
  · rw [ha.keeps.regs .rsp (by decide), hb.keeps.regs .rsp (by decide)]; exact hp.stacks
  · unfold FillKernel.matrix
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .rbp (by decide), hb.keeps.regs .rbp (by decide)]
    exact hp.matrices
  · unfold AddressCalls.work
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .rbp (by decide), hb.keeps.regs .rbp (by decide)]
    exact hp.work
  · unfold FillKernel.matrix; rw [ha.keeps.mem, ha.keeps.regs .rbp (by decide)]; exact hp.leftMatrix
  · unfold FillKernel.matrix; rw [hb.keeps.mem, hb.keeps.regs .rbp (by decide)]; exact hp.rightMatrix

theorem code_rel [CompressImpl] (p : Params) (pass slice : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass slice leftState rightState) Impl.Argon2.X86_64.FillSlice.code (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq setupA lanesA =>
    cases eb with
    | seq setupB lanesB =>
      obtain ⟨setupTrace, related⟩ := setup_public_rel p pass slice leftState rightState _ _ _ _ _ _ hp setupA setupB
      obtain ⟨lanesTrace, _⟩ := FillLanes.loop_rel p pass 0 slice p.lanes leftState rightState
        hp.left.parameters.lanesPositive (by omega_using []) _ _ _ _ _ _ related lanesA lanesB
      exact ⟨by rw [setupTrace, lanesTrace], trivial⟩

end VG.Proof.Argon2.X86_64.FillSlice
end

/-! A slice iteration preserves public allocations and its public continuation guard. -/

namespace VG.Proof.Argon2.X86_64.FillSlices

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillSlices

theorem advance_rel : RelCT isa (fun _ _ : State => True) (.block advance) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)

structure NextRelated (p : Params) (pass slice : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : FillSlice.Ready p pass slice s
  right : FillSlice.Ready p pass slice t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel [CompressImpl] (p : Params) (pass slice : Nat) (leftState rightState : FillState) :
    RelCT isa (FillSlice.Related p pass slice leftState rightState) body
      (fun s t => s.cf = t.cf ∧ (slice + 1 < 4 → NextRelated p pass (slice + 1)
        (Proof.Argon2.lanes p pass slice 0 p.lanes leftState) (Proof.Argon2.lanes p pass slice 0 p.lanes rightState) s t)) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq sliceA advanceA =>
    cases eb with
    | seq sliceB advanceB =>
      obtain ⟨sliceTrace, _⟩ := FillSlice.code_rel p pass slice leftState rightState _ _ _ _ _ _ hp sliceA sliceB
      obtain ⟨advanceTrace, _⟩ := advance_rel _ _ _ _ _ _ trivial advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := body_ok s p pass slice hp.left leftState hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := body_ok t p pass slice hp.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq sliceA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq sliceB advanceB) runB
      refine ⟨by rw [sliceTrace, advanceTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨doneA.next active, doneB.next active, ?_, ?_,
        doneA.matrix.trans (hp.matrices.trans doneB.matrix.symm),
        doneA.work.trans (hp.work.trans doneB.work.symm), doneA.represented, doneB.represented⟩
      · exact (doneA.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).trans
          (hp.bases.trans (doneB.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).symm)
      · exact (doneA.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).trans
          (hp.stacks.trans (doneB.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).symm)

end VG.Proof.Argon2.X86_64.FillSlices
end

/-! The complete pass leaks only its reviewed reference log, including Argon2id's mode change. -/

namespace VG.Proof.Argon2.X86_64.FillSlices

open VG VG.X86_64 VG.Spec.Argon2

structure Related (p : Params) (pass slice count : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  states : NextRelated p pass slice leftState rightState s t
  indices : (Proof.Argon2.slices p pass slice count leftState).indices =
    (Proof.Argon2.slices p pass slice count rightState).indices

theorem loop_rel [CompressImpl] (p : Params) (pass slice count : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endSlice : slice + count = 4) :
    RelCT isa (Related p pass slice count leftState rightState) Impl.Argon2.X86_64.FillSlices.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (slice : Nat) (leftState rightState : FillState),
    slice + n = 4 ∧ 0 < n ∧ Related p pass slice n leftState rightState s t
  obtain steps : ∀ n, RelCT isa (I n) Impl.Argon2.X86_64.FillSlices.body fun s t =>
      isa.eval .b s = isa.eval .b t ∧ (isa.eval .b s = some false → True) ∧
        (isa.eval .b s = some true → ∃ m < n, I m s t) := by
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
      · simp only [eval, flags]
      · intro taken
        obtain active : j + 1 < 4 := by
          simp only [eval, done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        have indices := hp.indices
        rw [Proof.Argon2.slices_succ, Proof.Argon2.slices_succ] at indices
        exact ⟨n, by omega_using [], j + 1, Proof.Argon2.lanes p pass j 0 p.lanes ls,
          Proof.Argon2.lanes p pass j 0 p.lanes rs, by omega_using [endSlice], by omega_using [endSlice, active], next active, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨slice, leftState, rightState, endSlice, positive, h⟩) (fun _ _ h => h)

theorem pass_rel [CompressImpl] (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (fun s t => NextRelated p pass 0 leftState rightState s t ∧
      (fillPass p leftState pass).indices = (fillPass p rightState pass).indices)
      Impl.Argon2.X86_64.FillSlices.loop (fun _ _ => True) := by
  refine (loop_rel p pass 0 4 leftState rightState (by decide) (by decide)).mono ?_ (fun _ _ h => h)
  intro s t h
  refine ⟨h.1, ?_⟩
  rw [Proof.Argon2.slices_pass p pass leftState, Proof.Argon2.slices_pass p pass rightState]
  exact h.2

end VG.Proof.Argon2.X86_64.FillSlices
end

/-! Merged from `Proof.Argon2.X86_64.FillIterationsCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillIterationsBodyCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillIterationCT`. -/
section
/-! Pass setup retains public pointers and exposes only the reviewed pass log. -/

namespace VG.Proof.Argon2.X86_64.FillIteration

open VG VG.X86_64 VG.Spec.Argon2

structure Related (p : Params) (pass : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : Ready p pass s
  right : Ready p pass t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (fillPass p leftState pass).indices = (fillPass p rightState pass).indices

theorem setup_trace : RelCT isa (fun _ _ : State => True) (.block Impl.Argon2.X86_64.FillIteration.setup) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)

theorem setup_public_rel (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass leftState rightState) (.block Impl.Argon2.X86_64.FillIteration.setup)
      (fun s t => FillSlices.NextRelated p pass 0 leftState rightState s t ∧
        (fillPass p leftState pass).indices = (fillPass p rightState pass).indices) := by
  obtain trace := setup_trace.mono (P' := Related p pass leftState rightState)
    (fun _ _ _ => trivial) (fun _ _ h => h)
  obtain full := trace.wpDep (fun s t h => ⟨setup_ok s p pass h.left, setup_ok t p pass h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨⟨ha.ready, hb.ready, ?_, ?_, ?_, ?_, ?_, ?_⟩, hp.indices⟩
  · rw [ha.keeps.regs .rbp (by decide), hb.keeps.regs .rbp (by decide)]; exact hp.bases
  · rw [ha.keeps.regs .rsp (by decide), hb.keeps.regs .rsp (by decide)]; exact hp.stacks
  · unfold FillKernel.matrix
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .rbp (by decide), hb.keeps.regs .rbp (by decide)]; exact hp.matrices
  · unfold AddressCalls.work
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .rbp (by decide), hb.keeps.regs .rbp (by decide)]; exact hp.work
  · unfold FillKernel.matrix; rw [ha.keeps.mem, ha.keeps.regs .rbp (by decide)]; exact hp.leftMatrix
  · unfold FillKernel.matrix; rw [hb.keeps.mem, hb.keeps.regs .rbp (by decide)]; exact hp.rightMatrix

theorem code_rel [CompressImpl] (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass leftState rightState) Impl.Argon2.X86_64.FillIteration.code (fun _ _ => True) :=
  (setup_public_rel p pass leftState rightState).seq (FillSlices.pass_rel p pass leftState rightState)

end VG.Proof.Argon2.X86_64.FillIteration
end

/-! Iteration advances its public pass counter and retains the reviewed filling log. -/

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillIterations

theorem advance_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp) advance (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

structure NextRelated (p : Params) (pass : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : Ready p pass s
  right : Ready p pass t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel [CompressImpl] (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (fun s t => NextRelated p pass leftState rightState s t ∧
      (fillPass p leftState pass).indices = (fillPass p rightState pass).indices) body
      (fun s t => s.cf = t.cf ∧ (pass + 1 < p.passes → NextRelated p (pass + 1)
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
      obtain bases := (filledA.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).trans
        (hp.bases.trans (filledB.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).symm)
      obtain ⟨advancedTrace, _⟩ := advance_rel _ _ _ _ _ _ bases advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := body_ok s p pass hp.left leftState hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := body_ok t p pass hp.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentB advanceB) runB
      refine ⟨by rw [segmentTrace, advancedTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨doneA.next active, doneB.next active, ?_, ?_,
        doneA.matrix.trans (hp.matrices.trans doneB.matrix.symm),
        doneA.work.trans (hp.work.trans doneB.work.symm), doneA.represented, doneB.represented⟩
      · exact (doneA.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).trans
          (hp.bases.trans (doneB.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).symm)
      · exact (doneA.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).trans
          (hp.stacks.trans (doneB.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).symm)

end VG.Proof.Argon2.X86_64.FillIterations
end

/-! The pass loop exposes only the complete filling reference log. -/

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2

structure Related (p : Params) (pass count : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  ready : NextRelated p pass leftState rightState s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.iterations p pass count leftState).indices =
    (Proof.Argon2.iterations p pass count rightState).indices

theorem loop_rel [CompressImpl] (p : Params) (pass count : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endPass : pass + count = p.passes) :
    RelCT isa (Related p pass count leftState rightState) Impl.Argon2.X86_64.FillIterations.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (pass : Nat) (leftState rightState : FillState),
    pass + n = p.passes ∧ 0 < n ∧ Related p pass n leftState rightState s t
  obtain steps : ∀ n, RelCT isa (I n) Impl.Argon2.X86_64.FillIterations.body fun s t =>
      isa.eval .b s = isa.eval .b t ∧ (isa.eval .b s = some false → True) ∧
        (isa.eval .b s = some true → ∃ m < n, I m s t) := by
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
      · simp only [eval, flags]
      · intro taken
        obtain active : j + 1 < p.passes := by
          simp only [eval, done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        obtain ready := next active
        have indices := hp.indices
        rw [Proof.Argon2.iterations_succ, Proof.Argon2.iterations_succ] at indices
        exact ⟨n, by omega_using [], j + 1, fillPass p ls j,
          fillPass p rs j, by omega_using [endPass], by omega_using [endPass, active], ready, ready.leftMatrix, ready.rightMatrix, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨pass, leftState, rightState, endPass, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.FillIterations
end

/-! Merged from `Proof.Argon2.X86_64.FillFinishCT`. -/
section
/-! Filling and finalization expose only the reviewed filling reference log. -/

namespace VG.Proof.Argon2.X86_64.FillFinish

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (leftState rightState : FillState) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : matrix s = matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  leftMatrix : Proof.Argon2.Represents s.mem (matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.iterations p 0 p.passes leftState).indices =
    (Proof.Argon2.iterations p 0 p.passes rightState).indices

theorem code_rel [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) (p : Params)
    (leftState rightState : FillState) :
    RelCT isa (Related p leftState rightState) (Impl.Argon2.X86_64.FillFinish.code name (HPrime.hash v))
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
          (doneA.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).trans
            (hp.bases.trans (doneB.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).symm),
          (doneA.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).trans
            (hp.stacks.trans (doneB.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).symm),
          doneA.matrix.trans (hp.matrices.trans doneB.matrix.symm),
          (doneA.frame_word hp.left.filling 256 (by decide) (by decide)).trans
            (hp.outputs.trans (doneB.frame_word hp.right.filling 256 (by decide) (by decide)).symm),
          (doneA.frame_word hp.left.filling 248 (by decide) (by decide)).trans
            (hp.works.trans (doneB.frame_word hp.right.filling 248 (by decide) (by decide)).symm),
          doneA.represented, doneB.represented⟩
      obtain ⟨finishTrace, _⟩ := Finish.code_rel v name p _ _ _ _ _ _ _ _ finalRelated finishA finishB
      exact ⟨by rw [fillTrace, finishTrace], trivial⟩

end VG.Proof.Argon2.X86_64.FillFinish
end

/-! The entire post-H₀ pipeline leaks only the reviewed complete filling reference log. -/

namespace VG.Proof.Argon2.X86_64.InitFill

open VG VG.X86_64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

def initial (p : Params) (s : State) : FillState := initMemory p (bytesAt s.mem (s.gpr .rbp) 64)

structure Related (p : Params) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  indices : (Proof.Argon2.iterations p 0 p.passes (initial p s)).indices =
    (Proof.Argon2.iterations p 0 p.passes (initial p t)).indices

theorem code_rel [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) (p : Params) :
    RelCT isa (Related p) (Impl.Argon2.X86_64.InitFill.code name (HPrime.hash v)) (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  have params := hp.left.environment.parameters
  obtain q : 2 ≤ p.laneLen := by
    obtain segments := Proof.Argon2.laneLen_segments p params.lanesPositive
    have minimum := params.segment_bound.1
    omega_using [segments, minimum]
  obtain lanesBound : p.lanes < 2 ^ 64 := Nat.lt_trans params.lanesBound (by decide)
  obtain pub : MemoryInit.AgreeBases s t := by
    intro r hr
    simp only [MemoryInit.publicBases, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.bases
    · exact hp.left.scratch.trans (hp.works.trans hp.right.scratch.symm)
    · exact hp.stacks
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
          obtain ⟨setupTrace, _⟩ := FillSetup.code_rel _ _ _ _ _ _ bases setupA setupB
          obtain ⟨_, ca, runA, preparedA⟩ := FillSetup.code_ok _ p (initialized_setup hp.left doneA)
          obtain ⟨_, cb, runB, preparedB⟩ := FillSetup.code_ok _ p (initialized_setup hp.right doneB)
          obtain ⟨_, rfl⟩ := Exec.det setupA runA
          obtain ⟨_, rfl⟩ := Exec.det setupB runB
          obtain preparedBases := (preparedA.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide) (by decide)).trans
            (bases.trans (preparedB.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide) (by decide)).symm)
          obtain preparedStacks := (preparedA.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide) (by decide)).trans
            ((doneA.sp.trans (hp.stacks.trans doneB.sp.symm)).trans
              (preparedB.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide) (by decide)).symm)
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

end VG.Proof.Argon2.X86_64.InitFill
end

/-! Complete derivation reveals only its reviewed filling reference sequence. -/

namespace VG.Proof.Argon2.X86_64.InitialBody

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64.Initial
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

theorem code_rel [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) (p : Params) :
    RelCT isa (Related p) (Impl.Argon2.X86_64.InitialBody.code name (HPrime.hash v)) (fun _ _ => True) := by
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
    ha.rbp.trans (hp.hashing.bp.trans hb.rbp.symm), ha.rsp.trans (hp.hashing.sp.trans hb.rsp.symm),
    baseA.trans (hp.matrices.trans baseB.symm), outputA.trans (hp.outputs.trans outputB.symm),
    workA.trans (hp.works.trans workB.symm), ?_⟩
  unfold InitFill.initial
  rw [ha.rbp, hb.rbp, da, db]
  exact hp.indices

end VG.Proof.Argon2.X86_64.InitialBody
end

/-! Use exactly the flattened leakage allowance of the shared derive contract. -/

namespace VG.Proof.Argon2.X86_64.InitialBody

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64.Initial

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

theorem reviewed_rel [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) (p : Params) :
    RelCT isa (ReviewedRelated p) (Impl.Argon2.X86_64.InitialBody.code name (HPrime.hash v)) (fun _ _ => True) :=
  (code_rel v name p).mono (fun _ _ h => h.related) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.InitialBody
end

/-! Preserve precisely the reviewed leakage relation across parameter computation. -/

namespace VG.Proof.Argon2.X86_64.InitialBody

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64.Initial

theorem ReviewedRelated.of_state {s₁ s₂ t₁ t₂ : State} {p : Params}
    (h : ReviewedRelated p s₁ s₂) (k₁ : SameFrame s₁ t₁) (k₂ : SameFrame s₂ t₂)
    (length₁ : t₁.gpr .r13 = BitVec.ofNat 64 p.laneLen)
    (length₂ : t₂.gpr .r13 = BitVec.ofNat 64 p.laneLen) : ReviewedRelated p t₁ t₂ := by
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
  · unfold VG.Proof.Argon2.X86_64.InitialBody.references
    rw [k₁.inputBytes passwordOffset passwordLenOffset, k₂.inputBytes passwordOffset passwordLenOffset,
      k₁.inputBytes saltOffset saltLenOffset, k₂.inputBytes saltOffset saltLenOffset,
      k₁.inputBytes secretOffset secretLenOffset, k₂.inputBytes secretOffset secretLenOffset,
      k₁.inputBytes adOffset adLenOffset, k₂.inputBytes adOffset adLenOffset]
    exact h.references

end VG.Proof.Argon2.X86_64.InitialBody
