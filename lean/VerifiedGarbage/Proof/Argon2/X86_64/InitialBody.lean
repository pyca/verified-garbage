module

public import VerifiedGarbage.Impl.Argon2.X86_64.InitialBody
public import VerifiedGarbage.Proof.Argon2.X86_64.InitFill
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Absorb
public import VerifiedGarbage.Proof.Argon2.X86_64.InitialLayout
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
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Space
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Finalize
import VerifiedGarbage.Proof.Argon2.HPrime
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

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
