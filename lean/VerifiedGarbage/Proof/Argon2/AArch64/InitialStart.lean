import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetupSteps
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Absorb
import VerifiedGarbage.Proof.Argon2.AArch64.InitialLayout

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
    exact (ih (by omega)).writeW (List.mem_singleton_self _) _
      (by
        rw [show (768 : Addr) = BitVec.ofNat 64 768 from rfl, BitVec.ofNat_add,
          ← BitVec.add_assoc]
        exact Offset.contains_base _ (by omega) (by omega))

theorem headerMem_read (s : State) (n j : Nat) (hn : n ≤ 6) (hj : j < n) :
    (headerMem s n).readW (s.gpr .x24 + BitVec.ofNat 64 (768 + 4 * j)) 32 =
      headerValue s j := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold headerMem
    by_cases he : j = n
    · subst j; exact Mem.readW_writeW_self32 ..
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega : 768 + 4 * j + 4 ≤ 768 + 4 * n ∨
        768 + 4 * n + 4 ≤ 768 + 4 * j) (by omega) (by omega)) (by decide)]
      exact ih (by omega) (by omega)

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
  have hw := h.write (768 + 4 * j) 4 (by omega)
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
        (Offset.contains_base _ (by omega) (by omega))
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
      have hn : r ≠ .x8 := by
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
    have align : headerSource j % 8 = 0 := by
      unfold headerSource
      split <;> (try split) <;> (try split) <;> (try split) <;> decide
    refine (headerWord_ok s _ _ align (by have := headerSource_bound j; omega)
      (by omega) (by omega) (h.readable _ (headerSource_slot j)) hw).mono ?_
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
    refine (ih (by omega)).mono ?_
    rintro u ⟨hu, ku⟩
    refine (headerSlot_ok u n (by omega) (h.keeps ku)).mono ?_
    rintro t ⟨ht, kt⟩
    refine ⟨?_, ku.trans kt⟩
    rw [ht, ku.x24, headerValue_keeps h ku, hu]
    rfl

theorem header_ok (s : State) (h : Space s) :
    WP isa (.block header) s fun t =>
      bytesAt t.mem (s.gpr .x24 + 768) 24 =
        (List.range 6).flatMap (fun j => Spec.Blake2.wordBytes (headerValue s j)) ∧ Keeps s t :=
  (headerWords_ok s 6 (by decide) h).mono fun t ⟨hm, hk⟩ =>
    ⟨by rw [hm]; exact headerMem_bytes s, hk⟩

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
  have f : Frame [⟨s.gpr .x24 + 792, 4⟩] s.mem t.mem := by
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
  have hn : r ≠ .x15 := by
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
  have all : ∀ d ∈ slots, d % 8 = 0 := by decide
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
  have reg := h.space.input_keeps k po lo h.pointerBound h.lengthBound
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
  refine WP.seq ((lengthArgs_ok s lo (slots_aligned lo h.lengthSlot) (by have := h.lengthBound; omega) (h.space.readable lo h.lengthSlot)
    (by simpa using h.space.write 792 4 (by decide))).mono ?_)
  intro a ha
  have ka := ha.keeps
  have hA := h.keeps ka
  have lenA : (a.gpr .x3).toNat = 4 := by rw [ha.size]; rfl
  have dataA : Covers [⟨a.gpr .x2, (a.gpr .x3).toNat⟩] (a.rd ++ a.wr) := by
    rw [ha.pointer, lenA, ka.x24.symm]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨a.gpr .x24, 16384⟩, List.mem_append_right _ hA.space.work,
      792, rfl, by change 792 + 4 ≤ 16384; decide⟩
  have dsA : (⟨a.gpr .x2, (a.gpr .x3).toNat⟩ : Region).Disjoint ⟨a.gpr .x24, 192⟩ := by
    rw [ha.pointer, lenA, ka.x24]
    exact (Offset.base_disjoint _ (by decide) (by decide)).symm
  have dwA : (⟨a.gpr .x2, (a.gpr .x3).toNat⟩ : Region).Disjoint ⟨a.gpr .x24 + 192, 576⟩ := by
    rw [ha.pointer, lenA, ka.x24]
    exact Offset.disjoint _ (by decide) (by decide) (by decide)
  have sdA : (below (a.sp) 16).Disjoint ⟨a.gpr .x2, (a.gpr .x3).toNat⟩ := by
    rw [ha.pointer, lenA, ka.x24.symm]
    exact hA.space.stackWork.sub_right (Offset.sub_base _ (by decide))
  refine WP.seq ((HPrime.update_ok v a _ d (ha.repr _ _ repr)
    (ha.count.trans count) (by rw [lenA]; omega) hA.space.stackMinimum hA.space.work dataA dsA dwA
    hA.space.stackWork sdA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, spU, frameU⟩
  have ku : Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, spU, HPrime.update_frame _ _ frameU⟩
  have ksu := ka.trans ku
  have hU := h.keeps ksu
  have prefixA : bytesAt a.mem (a.gpr .x2) (a.gpr .x3).toNat =
      Spec.Argon2.le32 (wordAt s lo).toNat := by rw [ha.pointer, lenA]; exact ha.prefix
  have r12U : u.gpr .x20 = s.gpr .x20 :=
    (regsU _ (by decide) (by decide)).trans (ha.other _ (by decide))
  have r14U : u.gpr .x22 = wordAt s lo := (regsU _ (by decide) (by decide)).trans ha.length
  refine WP.seq ((inputArgs_ok u po (slots_aligned po h.pointerSlot) (by have := h.pointerBound; omega) (hU.space.readable po h.pointerSlot)).mono ?_)
  intro x hx
  have kux := hx.keeps
  have ksx := ksu.trans kux
  have hX := h.keeps ksx
  have srcX : x.gpr .x2 = wordAt s po :=
    hx.pointer.trans (h.space.word_keeps ksu po h.pointerBound)
  have lenX : x.gpr .x3 = wordAt s lo := hx.length.trans r14U
  have r14X : x.gpr .x22 = wordAt s lo :=
    (hx.other _ (by decide)).trans r14U
  have reprX : Repr b (Spec.Blake2.init b 64 0) x.mem (x.gpr .x24)
      (d ++ Spec.Argon2.le32 (wordAt s lo).toNat) := by
    apply hx.repr
    rw [ku.x24]
    simpa only [prefixA] using reprU
  have prefixLen : (d ++ Spec.Argon2.le32 (wordAt s lo).toNat).length = d.length + 4 := by
    rw [List.length_append, Proof.Argon2.le32_length]
  have countX : x.gpr .x1 = BitVec.ofNat 64 (d ++ Spec.Argon2.le32 (wordAt s lo).toNat).length := by
    rw [hx.count, r12U, count, prefixLen, BitVec.ofNat_add]; rfl
  have coverX : Covers [⟨x.gpr .x2, (x.gpr .x3).toNat⟩] (x.rd ++ x.wr) := by
    rw [srcX, lenX, ksx.rd, ksx.wr]
    exact h.cover
  have dsX : (⟨x.gpr .x2, (x.gpr .x3).toNat⟩ : Region).Disjoint ⟨x.gpr .x24, 192⟩ := by
    rw [srcX, lenX, ksx.x24]
    exact h.work.sub_right (Region.sub_prefix (by decide))
  have dwX : (⟨x.gpr .x2, (x.gpr .x3).toNat⟩ : Region).Disjoint ⟨x.gpr .x24 + 192, 576⟩ := by
    rw [srcX, lenX, ksx.x24]
    exact h.work.sub_right (Offset.sub_base _ (by decide))
  have sdX : (below (x.sp) 16).Disjoint ⟨x.gpr .x2, (x.gpr .x3).toNat⟩ := by
    rw [srcX, lenX, ksx.sp]; exact h.stack.symm
  refine WP.seq ((HPrime.update_ok v x _ _ reprX countX
    (by rw [prefixLen, lenX]; exact bound) hX.space.stackMinimum hX.space.work coverX dsX dwX hX.space.stackWork sdX).mono ?_)
  rintro y ⟨reprY, regsY, rdY, wrY, spY, frameY⟩
  have ky : Keeps x y := Keeps.of_hash ⟨regsY, rdY, wrY, spY, HPrime.update_frame _ _ frameY⟩
  have ksy := ksx.trans ky
  have r12Y : y.gpr .x20 = BitVec.ofNat 64 (d.length + 4) := by
    rw [regsY _ (by decide) (by decide), hx.total, r12U, count, BitVec.ofNat_add]; rfl
  have r14Y : y.gpr .x22 = wordAt s lo := (regsY _ (by decide) (by decide)).trans r14X
  have bytesX : bytesAt x.mem (x.gpr .x2) (x.gpr .x3).toNat = inputBytes s po lo := by
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
  unfold headerBytes
  change (Spec.Blake2.wordBytes (headerValue s 0) ++ Spec.Blake2.wordBytes (headerValue s 1) ++
    Spec.Blake2.wordBytes (headerValue s 2) ++ Spec.Blake2.wordBytes (headerValue s 3) ++
    Spec.Blake2.wordBytes (headerValue s 4) ++ Spec.Blake2.wordBytes (headerValue s 5)).length = 24
  simp only [Spec.Blake2.wordBytes, List.length_append, List.length_map, List.length_range]

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
  have ka := Keeps.of_hash ka'
  have hA := h.keeps ka
  refine WP.seq ((HPrime.init_ok v a (by rw [lenA]; exact ⟨by decide, by decide⟩)
    hA.work).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, spU, frameU⟩
  have ku : Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, spU, HPrime.init_frame _ _ frameU⟩
  have ksu := ka.trans ku
  have hU := h.keeps ksu
  refine WP.seq ((headerWords_ok u 6 (by decide) hU).mono ?_)
  rintro w ⟨memW, kw⟩
  have ksw := ksu.trans kw
  have hW := h.keeps ksw
  have reprW : Repr b (Spec.Blake2.init b 64 0) w.mem (w.gpr .x24) [] := by
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
  have headW : bytesAt w.mem (w.gpr .x24 + 768) 24 = headerBytes s := by
    rw [kw.x24, memW, headerMem_bytes]
    exact headerBytes_keeps h ksu
  refine WP.seq ((HPrime.absorbFixed_ok v w _ 768 24 (by decide) hW.stackMinimum (by decide) (by decide)
    reprW hW.work hW.stackWork).mono ?_)
  rintro x ⟨reprX, kx'⟩
  have kx := Keeps.of_hash kx'
  have ksx := ksw.trans kx
  refine (initialCount_ok x).mono ?_
  rintro t ⟨countT, memT, kt⟩
  refine ⟨?_, countT, ksx.trans kt⟩
  rw [kt.x24, memT, kx.x24]
  simpa only [headW, show BitVec.ofNat 64 768 = (768 : Addr) from rfl] using reprX

end VG.Proof.Argon2.AArch64.Initial
