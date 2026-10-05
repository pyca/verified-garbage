import VerifiedGarbage.Proof.Argon2.X86_64.FillSegment
import VerifiedGarbage.Proof.Argon2.X86_64.CompressImpl
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Verified
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Argon2.X86_64.Initial
import VerifiedGarbage.Proof.Argon2.X86_64.InitFill
import VerifiedGarbage.Impl.Argon2.X86_64.Parameters
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Impl.Argon2.X86_64.InitialBody
import VerifiedGarbage.Proof.Argon2.References
import VerifiedGarbage.Impl.Argon2.X86_64.Finish
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.InitialLit`. -/
section

/-! A checked literal for the six-word H₀ header. -/

namespace VG

materialize_code Impl.Argon2.X86_64.Initial.headerCode

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.ParametersLit`. -/
section

/-! Checked literal of rounded-memory parameter computation. -/

namespace VG

materialize_code Impl.Argon2.X86_64.Parameters.code

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.InitialStart`. -/
section

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
  | n + 1 => (VG.Proof.Argon2.X86_64.Initial.headerMem s n).writeW (s.gpr .rbx + BitVec.ofNat 64 (768 + 4 * n))
    (VG.Proof.Argon2.X86_64.Initial.headerValue s n)

theorem headerSource_slot (j : Nat) : headerSource j ∈ slots := by
  unfold headerSource
  split <;> (try split) <;> (try split) <;> (try split) <;> decide

theorem headerSource_bound (j : Nat) : headerSource j + 8 ≤ 272 := by
  unfold headerSource
  split <;> (try split) <;> (try split) <;> (try split) <;> decide

theorem headerValue_keeps {s t : State} (h : VG.Proof.Argon2.X86_64.Initial.Space s) (k : VG.Proof.Argon2.X86_64.Initial.Keeps s t) (j : Nat) :
    VG.Proof.Argon2.X86_64.Initial.headerValue t j = VG.Proof.Argon2.X86_64.Initial.headerValue s j := by
  unfold VG.Proof.Argon2.X86_64.Initial.headerValue
  rw [h.word_keeps k _ (VG.Proof.Argon2.X86_64.Initial.headerSource_bound j)]

theorem headerMem_frame (s : State) (n : Nat) (hn : n ≤ 6) :
    Frame [⟨s.gpr .rbx + 768, 24⟩] s.mem (VG.Proof.Argon2.X86_64.Initial.headerMem s n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih =>
    exact (ih (by omega)).writeW (List.mem_singleton_self _) _
      (by
        rw [show (768 : Addr) = BitVec.ofNat 64 768 from rfl, BitVec.ofNat_add,
          ← BitVec.add_assoc]
        exact Offset.contains_base _ (by omega) (by omega))

theorem headerMem_read (s : State) (n j : Nat) (hn : n ≤ 6) (hj : j < n) :
    (VG.Proof.Argon2.X86_64.Initial.headerMem s n).readW (s.gpr .rbx + BitVec.ofNat 64 (768 + 4 * j)) 32 =
      VG.Proof.Argon2.X86_64.Initial.headerValue s j := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold VG.Proof.Argon2.X86_64.Initial.headerMem
    by_cases he : j = n
    · subst j; exact Mem.readW_writeW_self32 ..
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega : 768 + 4 * j + 4 ≤ 768 + 4 * n ∨
        768 + 4 * n + 4 ≤ 768 + 4 * j) (by omega) (by omega)) (by decide)]
      exact ih (by omega) (by omega)

theorem headerMem_bytes (s : State) :
    bytesAt (VG.Proof.Argon2.X86_64.Initial.headerMem s 6) (s.gpr .rbx + 768) 24 =
      (List.range 6).flatMap (fun j => Spec.Blake2.wordBytes (VG.Proof.Argon2.X86_64.Initial.headerValue s j)) := by
  rw [show 24 = 32 / 8 * 6 from rfl, Proof.Blake2.bytesAt_words (w := 32)]
  simp only [List.flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j hj
  rw [← Proof.Blake2.wordBytes_readW _ _ (Or.inl rfl)]
  rw [show (768 : Addr) = BitVec.ofNat 64 768 from rfl, BitVec.add_assoc,
    ← BitVec.ofNat_add, VG.Proof.Argon2.X86_64.Initial.headerMem_read s 6 j (by decide) (List.mem_range.mp hj)]

theorem headerSlot_ok (s : State) (j : Nat) (hj : j < 6) (h : VG.Proof.Argon2.X86_64.Initial.Space s) :
    WP isa (.block (headerSlot j)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .rbx + BitVec.ofNat 64 (768 + 4 * j)) (VG.Proof.Argon2.X86_64.Initial.headerValue s j) ∧
      VG.Proof.Argon2.X86_64.Initial.Keeps s t := by
  have hw := h.write (768 + 4 * j) 4 (by omega)
  have finish (t : State) (hm : t.mem = s.mem.writeW
      (s.gpr .rbx + BitVec.ofNat 64 (768 + 4 * j)) (VG.Proof.Argon2.X86_64.Initial.headerValue s j))
      (regs : ∀ r, r ≠ .rax → t.gpr r = s.gpr r) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
      t.mem = s.mem.writeW (s.gpr .rbx + BitVec.ofNat 64 (768 + 4 * j)) (VG.Proof.Argon2.X86_64.Initial.headerValue s j) ∧
        VG.Proof.Argon2.X86_64.Initial.Keeps s t := by
    refine ⟨hm, fun r hr _ _ => regs r ?_, rd, wr, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rw [hm]
      exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
        (Offset.contains_base _ (by omega) (by omega))
  unfold headerSlot
  split
  · next he =>
    subst j
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
      State.store32, VG.Proof.Argon2.X86_64.Initial.ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.wr_setReg,
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
    refine (headerWord_ok s _ _ (h.readable _ (VG.Proof.Argon2.X86_64.Initial.headerSource_slot j)) hw).mono ?_
    rintro t ⟨hm, regs, rd, wr⟩
    exact finish t (by simpa only [VG.Proof.Argon2.X86_64.Initial.headerValue, he, ite_false, wordAt] using hm) regs rd wr

theorem headerWords_ok (s : State) (n : Nat) (hn : n ≤ 6) (h : VG.Proof.Argon2.X86_64.Initial.Space s) :
    WP isa (.block ((List.range n).flatMap headerSlot)) s fun t =>
      t.mem = VG.Proof.Argon2.X86_64.Initial.headerMem s n ∧ VG.Proof.Argon2.X86_64.Initial.Keeps s t := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨rfl, fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine (ih (by omega)).mono ?_
    rintro u ⟨hu, ku⟩
    refine (VG.Proof.Argon2.X86_64.Initial.headerSlot_ok u n (by omega) (h.keeps ku)).mono ?_
    rintro t ⟨ht, kt⟩
    refine ⟨?_, ku.trans kt⟩
    rw [ht, ku.rbx, VG.Proof.Argon2.X86_64.Initial.headerValue_keeps h ku, hu]
    rfl

theorem header_ok (s : State) (h : VG.Proof.Argon2.X86_64.Initial.Space s) :
    WP isa (.block VG.Impl.Argon2.X86_64.Initial.header) s fun t =>
      bytesAt t.mem (s.gpr .rbx + 768) 24 =
        (List.range 6).flatMap (fun j => Spec.Blake2.wordBytes (VG.Proof.Argon2.X86_64.Initial.headerValue s j)) ∧ VG.Proof.Argon2.X86_64.Initial.Keeps s t :=
  (VG.Proof.Argon2.X86_64.Initial.headerWords_ok s 6 (by decide) h).mono fun t ⟨hm, hk⟩ =>
    ⟨by rw [hm]; exact VG.Proof.Argon2.X86_64.Initial.headerMem_bytes s, hk⟩

end VG.Proof.Argon2.X86_64.Initial
end

/-! # H₀: preserving the stack across input argument preparation -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
open VG.Spec.Blake2 (bytesAt)

theorem LengthArgs.keeps {s t : State} {offset : Nat} (h : LengthArgs s offset t) :
    VG.Proof.Argon2.X86_64.Initial.Keeps s t := by
  refine ⟨fun r hr _ h14 => ?_, h.rd, h.wr, ?_⟩
  · have hn : r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r h14 hn.1 hn.2.1 hn.2.2
  · rw [h.mem]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide) (by decide))

theorem InputArgs.keeps {s t : State} {offset : Nat} (h : VG.Proof.Argon2.X86_64.Initial.InputArgs s t offset) :
    VG.Proof.Argon2.X86_64.Initial.Keeps s t := by
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
  have f : Frame [⟨s.gpr .rbx + 792, 4⟩] s.mem t.mem := by
    rw [h.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  apply f.bytes (R := ⟨s.gpr .rbx, 192⟩) _ (show (192 : Nat) ≤ 2 ^ 64 from by decide) hi
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact Offset.base_disjoint _ (by decide) (by decide)

theorem InputArgs.repr {s t : State} {offset : Nat} (h : VG.Proof.Argon2.X86_64.Initial.InputArgs s t offset)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Spec.Blake2.Repr Spec.Blake2.b h0 s.mem (s.gpr .rbx) d) :
    Spec.Blake2.Repr Spec.Blake2.b h0 t.mem (t.gpr .rbx) d := by
  rw [h.keeps.rbx, h.mem]; exact repr

theorem addCount_ok (s : State) :
    WP isa (.block [.alu .add .r12 (.reg .r14)]) s fun t =>
      t.gpr .r12 = s.gpr .r12 + s.gpr .r14 ∧ t.mem = s.mem ∧ VG.Proof.Argon2.X86_64.Initial.Keeps s t := by
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
  space : VG.Proof.Argon2.X86_64.Initial.Space s
  pointerSlot : po ∈ slots
  lengthSlot : lo ∈ slots
  pointerBound : po + 8 ≤ 272
  lengthBound : lo + 8 ≤ 272
  length : (wordAt s lo).toNat < 2 ^ 32
  cover : Covers [inputRegion s po lo] (s.rd ++ s.wr)
  work : (inputRegion s po lo).Disjoint ⟨s.gpr .rbx, 16384⟩
  stack : (inputRegion s po lo).Disjoint (below (s.gpr .rsp) 16)

theorem InputReady.keeps {s t : State} {po lo : Nat} (h : VG.Proof.Argon2.X86_64.Initial.InputReady s po lo)
    (k : VG.Proof.Argon2.X86_64.Initial.Keeps s t) : VG.Proof.Argon2.X86_64.Initial.InputReady t po lo := by
  have reg := h.space.input_keeps k po lo h.pointerBound h.lengthBound
  refine ⟨h.space.keeps k, h.pointerSlot, h.lengthSlot, h.pointerBound, h.lengthBound,
    ?_, ?_, ?_, ?_⟩
  · rw [h.space.word_keeps k lo h.lengthBound]; exact h.length
  · rw [reg, k.rd, k.wr]; exact h.cover
  · rw [reg, k.rbx]; exact h.work
  · rw [reg, k.rsp]; exact h.stack

def inputBytes (s : State) (po lo : Nat) : List Byte :=
  bytesAt s.mem (wordAt s po) (wordAt s lo).toNat

theorem inputBytes_length (s : State) (po lo : Nat) :
    (VG.Proof.Argon2.X86_64.Initial.inputBytes s po lo).length = (wordAt s lo).toNat := by
  simp only [VG.Proof.Argon2.X86_64.Initial.inputBytes, bytesAt, List.length_map, List.length_range]

theorem InputReady.bytes_keeps {s t : State} {po lo : Nat} (h : VG.Proof.Argon2.X86_64.Initial.InputReady s po lo)
    (k : VG.Proof.Argon2.X86_64.Initial.Keeps s t) : VG.Proof.Argon2.X86_64.Initial.inputBytes t po lo = VG.Proof.Argon2.X86_64.Initial.inputBytes s po lo := by
  unfold VG.Proof.Argon2.X86_64.Initial.inputBytes
  rw [h.space.word_keeps k po h.pointerBound, h.space.word_keeps k lo h.lengthBound]
  exact k.bytes (inputRegion s po lo) h.work h.stack (by
    change (wordAt s lo).toNat ≤ 2 ^ 64
    exact Nat.le_of_lt (wordAt s lo).isLt)

theorem absorb_ok (v : Proof.Blake2.X86_64.Backend) (s : State) (po lo : Nat)
    (h : VG.Proof.Argon2.X86_64.Initial.InputReady s po lo) (d : List Byte)
    (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (s.gpr .rbx) d)
    (count : s.gpr .r12 = BitVec.ofNat 64 d.length)
    (bound : d.length + 4 + (wordAt s lo).toNat < 2 ^ 64) :
    WP isa (absorb (HPrime.hash v) po lo) s fun t =>
      Repr b (Spec.Blake2.init b 64 0) t.mem (t.gpr .rbx)
        (appendInput d (VG.Proof.Argon2.X86_64.Initial.inputBytes s po lo)) ∧
      t.gpr .r12 = BitVec.ofNat 64 (appendInput d (VG.Proof.Argon2.X86_64.Initial.inputBytes s po lo)).length ∧ VG.Proof.Argon2.X86_64.Initial.Keeps s t := by
  unfold absorb
  refine WP.seq ((lengthArgs_ok s lo (h.space.readable lo h.lengthSlot)
    (by simpa using h.space.write 792 4 (by decide))).mono ?_)
  intro a ha
  have ka := ha.keeps
  have hA := h.keeps ka
  have lenA : (a.gpr .rcx).toNat = 4 := by rw [ha.size]; rfl
  have dataA : Covers [⟨a.gpr .rdx, (a.gpr .rcx).toNat⟩] (a.rd ++ a.wr) := by
    rw [ha.pointer, lenA, ka.rbx.symm]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨a.gpr .rbx, 16384⟩, List.mem_append_right _ hA.space.work,
      792, rfl, by change 792 + 4 ≤ 16384; decide⟩
  have dsA : (⟨a.gpr .rdx, (a.gpr .rcx).toNat⟩ : Region).Disjoint ⟨a.gpr .rbx, 192⟩ := by
    rw [ha.pointer, lenA, ka.rbx]
    exact (Offset.base_disjoint _ (by decide) (by decide)).symm
  have dwA : (⟨a.gpr .rdx, (a.gpr .rcx).toNat⟩ : Region).Disjoint ⟨a.gpr .rbx + 192, 576⟩ := by
    rw [ha.pointer, lenA, ka.rbx]
    exact Offset.disjoint _ (by decide) (by decide) (by decide)
  have sdA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .rdx, (a.gpr .rcx).toNat⟩ := by
    rw [ha.pointer, lenA, ka.rbx.symm]
    exact hA.space.stackWork.sub_right (Offset.sub_base _ (by decide))
  refine WP.seq ((HPrime.update_ok v a _ d (ha.repr _ _ repr)
    (ha.count.trans count) (by rw [lenA]; omega) hA.space.work dataA dsA dwA
    hA.space.stackWork sdA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, frameU⟩
  have ku : VG.Proof.Argon2.X86_64.Initial.Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, HPrime.update_frame _ _ frameU⟩
  have ksu := ka.trans ku
  have hU := h.keeps ksu
  have prefixA : bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat =
      Spec.Argon2.le32 (wordAt s lo).toNat := by rw [ha.pointer, lenA]; exact ha.prefix
  have r12U : u.gpr .r12 = s.gpr .r12 :=
    (regsU _ (by decide)).trans (ha.other _ (by decide) (by decide) (by decide) (by decide))
  have r14U : u.gpr .r14 = wordAt s lo := (regsU _ (by decide)).trans ha.length
  refine WP.seq ((VG.Proof.Argon2.X86_64.Initial.inputArgs_ok u po (hU.space.readable po h.pointerSlot)).mono ?_)
  intro x hx
  have kux := hx.keeps
  have ksx := ksu.trans kux
  have hX := h.keeps ksx
  have srcX : x.gpr .rdx = wordAt s po :=
    hx.pointer.trans (h.space.word_keeps ksu po h.pointerBound)
  have lenX : x.gpr .rcx = wordAt s lo := hx.length.trans r14U
  have r14X : x.gpr .r14 = wordAt s lo :=
    (hx.other _ (by decide) (by decide) (by decide) (by decide)).trans r14U
  have reprX : Repr b (Spec.Blake2.init b 64 0) x.mem (x.gpr .rbx)
      (d ++ Spec.Argon2.le32 (wordAt s lo).toNat) := by
    apply hx.repr
    rw [ku.rbx]
    simpa only [prefixA] using reprU
  have prefixLen : (d ++ Spec.Argon2.le32 (wordAt s lo).toNat).length = d.length + 4 := by
    rw [List.length_append, Proof.Argon2.le32_length]
  have countX : x.gpr .rsi = BitVec.ofNat 64 (d ++ Spec.Argon2.le32 (wordAt s lo).toNat).length := by
    rw [hx.count, r12U, count, prefixLen, BitVec.ofNat_add]; rfl
  have coverX : Covers [⟨x.gpr .rdx, (x.gpr .rcx).toNat⟩] (x.rd ++ x.wr) := by
    rw [srcX, lenX, ksx.rd, ksx.wr]
    exact h.cover
  have dsX : (⟨x.gpr .rdx, (x.gpr .rcx).toNat⟩ : Region).Disjoint ⟨x.gpr .rbx, 192⟩ := by
    rw [srcX, lenX, ksx.rbx]
    exact h.work.sub_right (Region.sub_prefix (by decide))
  have dwX : (⟨x.gpr .rdx, (x.gpr .rcx).toNat⟩ : Region).Disjoint ⟨x.gpr .rbx + 192, 576⟩ := by
    rw [srcX, lenX, ksx.rbx]
    exact h.work.sub_right (Offset.sub_base _ (by decide))
  have sdX : (below (x.gpr .rsp) 16).Disjoint ⟨x.gpr .rdx, (x.gpr .rcx).toNat⟩ := by
    rw [srcX, lenX, ksx.rsp]; exact h.stack.symm
  refine WP.seq ((HPrime.update_ok v x _ _ reprX countX
    (by rw [prefixLen, lenX]; exact bound) hX.space.work coverX dsX dwX hX.space.stackWork sdX).mono ?_)
  rintro y ⟨reprY, regsY, rdY, wrY, frameY⟩
  have ky : VG.Proof.Argon2.X86_64.Initial.Keeps x y := Keeps.of_hash ⟨regsY, rdY, wrY, HPrime.update_frame _ _ frameY⟩
  have ksy := ksx.trans ky
  have r12Y : y.gpr .r12 = BitVec.ofNat 64 (d.length + 4) := by
    rw [regsY _ (by decide), hx.total, r12U, count, BitVec.ofNat_add]; rfl
  have r14Y : y.gpr .r14 = wordAt s lo := (regsY _ (by decide)).trans r14X
  have bytesX : bytesAt x.mem (x.gpr .rdx) (x.gpr .rcx).toNat = VG.Proof.Argon2.X86_64.Initial.inputBytes s po lo := by
    rw [srcX, lenX]
    exact ksx.bytes (inputRegion s po lo) h.work h.stack (Nat.le_of_lt (wordAt s lo).isLt)
  refine (VG.Proof.Argon2.X86_64.Initial.addCount_ok y).mono ?_
  rintro t ⟨ht12, hm, kt⟩
  refine ⟨?_, ?_, ksy.trans kt⟩
  · rw [kt.rbx, hm, ky.rbx]
    simpa only [appendInput, VG.Proof.Argon2.X86_64.Initial.inputBytes_length, bytesX] using reprY
  · have hw : BitVec.ofNat 64 (wordAt s lo).toNat = wordAt s lo := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [ht12, r12Y, r14Y, ← hw, ← BitVec.ofNat_add,
      Proof.Argon2.appendInput_length, VG.Proof.Argon2.X86_64.Initial.inputBytes_length]

end VG.Proof.Argon2.X86_64.Initial

end

/-! # H₀: initialize BLAKE2b and absorb the public parameter header -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)

def headerBytes (s : State) : List Byte :=
  (List.range 6).flatMap fun j => Spec.Blake2.wordBytes (VG.Proof.Argon2.X86_64.Initial.headerValue s j)

theorem headerBytes_keeps {s t : State} (h : VG.Proof.Argon2.X86_64.Initial.Space s) (k : VG.Proof.Argon2.X86_64.Initial.Keeps s t) :
    VG.Proof.Argon2.X86_64.Initial.headerBytes t = VG.Proof.Argon2.X86_64.Initial.headerBytes s := by
  unfold VG.Proof.Argon2.X86_64.Initial.headerBytes
  simp only [List.flatMap]
  apply congrArg List.flatten
  exact List.map_congr_left fun j _ => congrArg Spec.Blake2.wordBytes (VG.Proof.Argon2.X86_64.Initial.headerValue_keeps h k j)

theorem headerBytes_length (s : State) : (VG.Proof.Argon2.X86_64.Initial.headerBytes s).length = 24 := by
  unfold VG.Proof.Argon2.X86_64.Initial.headerBytes
  change (Spec.Blake2.wordBytes (VG.Proof.Argon2.X86_64.Initial.headerValue s 0) ++ Spec.Blake2.wordBytes (VG.Proof.Argon2.X86_64.Initial.headerValue s 1) ++
    Spec.Blake2.wordBytes (VG.Proof.Argon2.X86_64.Initial.headerValue s 2) ++ Spec.Blake2.wordBytes (VG.Proof.Argon2.X86_64.Initial.headerValue s 3) ++
    Spec.Blake2.wordBytes (VG.Proof.Argon2.X86_64.Initial.headerValue s 4) ++ Spec.Blake2.wordBytes (VG.Proof.Argon2.X86_64.Initial.headerValue s 5)).length = 24
  simp only [Spec.Blake2.wordBytes, List.length_append, List.length_map, List.length_range]

theorem digestLength_ok (s : State) :
    WP isa (.block [.mov32 .rsi (.imm 64)]) s fun t =>
      t.gpr .rsi = 64 ∧ t.mem = s.mem ∧ HPrime.Keeps s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, Frame.refl _ _⟩
  have hn : r ≠ .rsi := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [RegUpd.gpr_setReg, hn, ite_false]

theorem initialCount_ok (s : State) :
    WP isa (.block [.mov32 .r12 (.imm 24)]) s fun t =>
      t.gpr .r12 = 24 ∧ t.mem = s.mem ∧ VG.Proof.Argon2.X86_64.Initial.Keeps s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r _ h12 _ => ?_, rfl, rfl, Frame.refl _ _⟩
  simp only [RegUpd.gpr_setReg, h12, ite_false]

theorem start_ok (v : Proof.Blake2.X86_64.Backend) (s : State) (h : VG.Proof.Argon2.X86_64.Initial.Space s) :
    WP isa (VG.Impl.Argon2.X86_64.Initial.start (HPrime.hash v)) s fun t =>
      Repr b (Spec.Blake2.init b 64 0) t.mem (t.gpr .rbx) (VG.Proof.Argon2.X86_64.Initial.headerBytes s) ∧
      t.gpr .r12 = 24 ∧ VG.Proof.Argon2.X86_64.Initial.Keeps s t := by
  unfold VG.Impl.Argon2.X86_64.Initial.start headerCode
  refine WP.seq ((VG.Proof.Argon2.X86_64.Initial.digestLength_ok s).mono ?_)
  rintro a ⟨lenA, memA, ka'⟩
  have ka := Keeps.of_hash ka'
  have hA := h.keeps ka
  have retA : (below (a.gpr .rsp) 8).Disjoint ⟨a.gpr .rbx, 192⟩ := (hA.stackWork.sub_left (below_sub (by decide) (by decide))).sub_right
    (Region.sub_prefix (by decide : 192 ≤ 16384))
  refine WP.seq ((HPrime.init_ok v a (by rw [lenA]; exact ⟨by decide, by decide⟩)
    hA.work retA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, frameU⟩
  have ku : VG.Proof.Argon2.X86_64.Initial.Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, HPrime.init_frame _ _ frameU⟩
  have ksu := ka.trans ku
  have hU := h.keeps ksu
  refine WP.seq ((VG.Proof.Argon2.X86_64.Initial.headerWords_ok u 6 (by decide) hU).mono ?_)
  rintro w ⟨memW, kw⟩
  have ksw := ksu.trans kw
  have hW := h.keeps ksw
  have reprW : Repr b (Spec.Blake2.init b 64 0) w.mem (w.gpr .rbx) [] := by
    rw [kw.rbx]
    apply Proof.Blake2.X86_64.Stream.Update.repr_congr Proof.Blake2.X86_64.Stream.okB
      (mem := u.mem) _ (by simpa only [lenA, ku.rbx, show (64 : BitVec 64).toNat = 64 from rfl] using reprU)
    intro i hi
    rw [memW]
    apply (VG.Proof.Argon2.X86_64.Initial.headerMem_frame u 6 (by decide)).bytes (R := ⟨u.gpr .rbx, 192⟩) _
      (show (192 : Nat) ≤ 2 ^ 64 from by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact Offset.base_disjoint _ (by decide) (by decide)
  have headW : bytesAt w.mem (w.gpr .rbx + 768) 24 = VG.Proof.Argon2.X86_64.Initial.headerBytes s := by
    rw [kw.rbx, memW, VG.Proof.Argon2.X86_64.Initial.headerMem_bytes]
    exact VG.Proof.Argon2.X86_64.Initial.headerBytes_keeps h ksu
  refine WP.seq ((HPrime.absorbFixed_ok v w _ 768 24 (by decide) (by decide)
    reprW hW.work hW.stackWork).mono ?_)
  rintro x ⟨reprX, kx'⟩
  have kx := Keeps.of_hash kx'
  have ksx := ksw.trans kx
  refine (VG.Proof.Argon2.X86_64.Initial.initialCount_ok x).mono ?_
  rintro t ⟨countT, memT, kt⟩
  refine ⟨?_, countT, ksx.trans kt⟩
  rw [kt.rbx, memT, kx.rbx]
  simpa only [headW, show BitVec.ofNat 64 768 = (768 : Addr) from rfl] using reprX

end VG.Proof.Argon2.X86_64.Initial

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Initial`. -/
section

/-! Merged from `Proof.Argon2.X86_64.InitialFinish`. -/
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
  have hn : r ≠ .rsi := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [RegUpd.gpr_setReg, hn, ite_false]

theorem finishOutput_ok (s : State) :
    WP isa (.block [.mov .r14 (.reg .rbp), .mov32 .rax (.imm 64)]) s fun t =>
      t.gpr .r14 = s.gpr .rbp ∧ t.gpr .rax = 64 ∧ t.mem = s.mem ∧ VG.Proof.Argon2.X86_64.Initial.Keeps s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    State.setReg32, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg,
    RegUpd.mem_setReg]
  refine ⟨rfl, rfl, trivial, fun r hr h12 h14 => ?_, rfl, rfl, Frame.refl _ _⟩
  have hn : r ≠ .rax := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [RegUpd.gpr_setReg, hn, h14, ite_false]

theorem finish_ok (v : Proof.Blake2.X86_64.Backend) (s : State) (h : VG.Proof.Argon2.X86_64.Initial.Space s)
    (d : List Byte) (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (s.gpr .rbx) d)
    (count : s.gpr .r12 = BitVec.ofNat 64 d.length) (bound : d.length < 2 ^ 64) :
    WP isa (VG.Impl.Argon2.X86_64.Initial.finish (HPrime.hash v)) s fun t =>
      bytesAt t.mem (s.gpr .rbp) 64 = Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) d ∧
      VG.Proof.Argon2.X86_64.Initial.Finished s t := by
  unfold VG.Impl.Argon2.X86_64.Initial.finish
  refine WP.seq ((VG.Proof.Argon2.X86_64.Initial.finishCount_ok s).mono ?_)
  rintro a ⟨countA, memA, ka'⟩
  have ka := Keeps.of_hash ka'
  have hA := h.keeps ka
  have reprA : Repr b (Spec.Blake2.init b 64 0) a.mem (a.gpr .rbx) d := by
    rw [memA, ka.rbx]; exact repr
  refine WP.seq ((HPrime.finalize_ok v a _ d reprA (countA.trans count) bound
    hA.work hA.stackWork).mono ?_)
  rintro u ⟨digestU, regsU, rdU, wrU, frameU⟩
  have ku : VG.Proof.Argon2.X86_64.Initial.Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, HPrime.finalize_frame _ _ frameU⟩
  have ksu := ka.trans ku
  refine WP.seq ((VG.Proof.Argon2.X86_64.Initial.finishOutput_ok u).mono ?_)
  rintro w ⟨dstW, countW, memW, kw⟩
  have ksw := ksu.trans kw
  have hW := h.keeps ksw
  have outW : ∀ i < 64, InRegions w.wr (w.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [dstW, ← kw.rbp]
    rcases hW.output with ⟨r, hr, hc⟩
    exact ⟨r, hr, hc.byte (by rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]; exact hi)⟩
  have sepW : (⟨w.gpr .rbx + 768, 64⟩ : Region).Disjoint ⟨w.gpr .r14, 64⟩ := by
    rw [dstW, ← kw.rbp]
    exact (hW.frameWork.sub_left (Region.sub_prefix (by decide : 64 ≤ 272))).symm.sub_left
      (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))
  refine (HPrime.copy_ok w 64 (by decide) (by decide) countW hW.work outW sepW).mono ?_
  intro t ht
  have sourceLength : (bytesAt w.mem (w.gpr .rbx + 768) 64).length = 64 := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨?_, fun r hr h12 h14 => ?_, ht.rd.trans ksw.rd, ht.wr.trans ksw.wr, ?_⟩
  · have dst : w.gpr .r14 = s.gpr .rbp := dstW.trans ksu.rbp
    rw [ht.mem]
    conv_lhs => arg 2; rw [← dst]
    have copied := HPrime.bytesAt_writeBytes w.mem (w.gpr .r14)
      (bytesAt w.mem (w.gpr .rbx + 768) 64) (by rw [sourceLength]; decide)
    rw [sourceLength] at copied
    rw [copied, memW, kw.rbx, ku.rbx]
    exact digestU
  · have hrax : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrcx : r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrdx : r ≠ .rdx := by
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
  ps.foldl (fun m p => appendInput m (VG.Proof.Argon2.X86_64.Initial.inputBytes s p.1 p.2)) d

def inputSize (s : State) (ps : List (Nat × Nat)) : Nat :=
  (ps.map fun p => 4 + (wordAt s p.2).toNat).sum

def remaining (h : VG.Impl.Argon2.X86_64.HPrime.Hash) : List (Nat × Nat) → Prog isa
  | [] => VG.Impl.Argon2.X86_64.Initial.finish h
  | p :: ps => .seq (absorb h p.1 p.2) (VG.Proof.Argon2.X86_64.Initial.remaining h ps)

theorem message_keeps {s t : State} (ps : List (Nat × Nat)) (d : List Byte)
    (ready : ∀ p ∈ ps, VG.Proof.Argon2.X86_64.Initial.InputReady s p.1 p.2) (k : VG.Proof.Argon2.X86_64.Initial.Keeps s t) :
    VG.Proof.Argon2.X86_64.Initial.message t ps d = VG.Proof.Argon2.X86_64.Initial.message s ps d := by
  induction ps generalizing d with
  | nil => rfl
  | cons p ps ih =>
    simp only [VG.Proof.Argon2.X86_64.Initial.message, List.foldl_cons]
    rw [(ready p (by simp only [List.mem_cons, true_or])).bytes_keeps k]
    exact ih _ (fun q hq => ready q (List.mem_cons_of_mem p hq))

theorem inputSize_keeps {s t : State} (ps : List (Nat × Nat))
    (ready : ∀ p ∈ ps, VG.Proof.Argon2.X86_64.Initial.InputReady s p.1 p.2) (k : VG.Proof.Argon2.X86_64.Initial.Keeps s t) :
    VG.Proof.Argon2.X86_64.Initial.inputSize t ps = VG.Proof.Argon2.X86_64.Initial.inputSize s ps := by
  unfold VG.Proof.Argon2.X86_64.Initial.inputSize
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [(ready p hp).space.word_keeps k p.2 (ready p hp).lengthBound]

theorem Finished.before {s u t : State} (k : VG.Proof.Argon2.X86_64.Initial.Keeps s u) (f : VG.Proof.Argon2.X86_64.Initial.Finished u t) : VG.Proof.Argon2.X86_64.Initial.Finished s t := by
  refine ⟨fun r hr h12 h14 => (f.regs r hr h12 h14).trans (k.regs r hr h12 h14),
    f.rd.trans k.rd, f.wr.trans k.wr, ?_⟩
  apply (k.frame.mono ?_).trans
  · simpa only [k.rbx, k.rsp, k.rbp] using f.frame
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    exact hr.elim Or.inl (fun h => Or.inr (Or.inl h))

theorem remaining_ok (v : Proof.Blake2.X86_64.Backend) (ps : List (Nat × Nat))
    (s : State) (space : VG.Proof.Argon2.X86_64.Initial.Space s) (ready : ∀ p ∈ ps, VG.Proof.Argon2.X86_64.Initial.InputReady s p.1 p.2)
    (d : List Byte) (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (s.gpr .rbx) d)
    (count : s.gpr .r12 = BitVec.ofNat 64 d.length)
    (bound : d.length + VG.Proof.Argon2.X86_64.Initial.inputSize s ps < 2 ^ 64) :
    WP isa (VG.Proof.Argon2.X86_64.Initial.remaining (HPrime.hash v) ps) s fun t =>
      bytesAt t.mem (s.gpr .rbp) 64 =
        Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) (VG.Proof.Argon2.X86_64.Initial.message s ps d) ∧ VG.Proof.Argon2.X86_64.Initial.Finished s t := by
  induction ps generalizing s d with
  | nil =>
    exact VG.Proof.Argon2.X86_64.Initial.finish_ok v s space d repr count (by simpa only [VG.Proof.Argon2.X86_64.Initial.inputSize, List.map_nil,
                                     List.sum_nil, Nat.add_zero] using bound)
  | cons p ps ih =>
    have hp := ready p (by simp only [List.mem_cons, true_or])
    have tailReady : ∀ q ∈ ps, VG.Proof.Argon2.X86_64.Initial.InputReady s q.1 q.2 := fun q hq =>
      ready q (List.mem_cons_of_mem p hq)
    have size : VG.Proof.Argon2.X86_64.Initial.inputSize s (p :: ps) = 4 + (wordAt s p.2).toNat + VG.Proof.Argon2.X86_64.Initial.inputSize s ps := rfl
    refine WP.seq ((VG.Proof.Argon2.X86_64.Initial.absorb_ok v s p.1 p.2 hp d repr count (by rw [size] at bound; omega)).mono ?_)
    rintro u ⟨reprU, countU, ku⟩
    refine (ih u (space.keeps ku) (fun q hq => (tailReady q hq).keeps ku)
      _ reprU countU ?_).mono ?_
    · rw [VG.Proof.Argon2.X86_64.Initial.inputSize_keeps ps tailReady ku, Proof.Argon2.appendInput_length, VG.Proof.Argon2.X86_64.Initial.inputBytes_length]
      rw [size] at bound; omega
    · rintro t ⟨digestT, ft⟩
      refine ⟨?_, ft.before ku⟩
      rw [ku.rbp] at digestT
      rw [VG.Proof.Argon2.X86_64.Initial.message_keeps ps _ tailReady ku] at digestT
      exact digestT

theorem code_ok (v : Proof.Blake2.X86_64.Backend) (s : State) (space : VG.Proof.Argon2.X86_64.Initial.Space s)
    (ready : ∀ p ∈ VG.Proof.Argon2.X86_64.Initial.inputs, VG.Proof.Argon2.X86_64.Initial.InputReady s p.1 p.2) :
    WP isa (VG.Impl.Argon2.X86_64.Initial.code (HPrime.hash v)) s fun t =>
      bytesAt t.mem (s.gpr .rbp) 64 =
        Spec.Argon2.H 64 (VG.Proof.Argon2.X86_64.Initial.message s VG.Proof.Argon2.X86_64.Initial.inputs (VG.Proof.Argon2.X86_64.Initial.headerBytes s)) ∧ VG.Proof.Argon2.X86_64.Initial.Finished s t := by
  change WP isa (.seq (VG.Impl.Argon2.X86_64.Initial.start (HPrime.hash v)) (VG.Proof.Argon2.X86_64.Initial.remaining (HPrime.hash v) VG.Proof.Argon2.X86_64.Initial.inputs)) s _
  refine WP.seq ((VG.Proof.Argon2.X86_64.Initial.start_ok v s space).mono ?_)
  rintro u ⟨reprU, countU, ku⟩
  have count : u.gpr .r12 = BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Initial.headerBytes s).length := by
    rw [VG.Proof.Argon2.X86_64.Initial.headerBytes_length]; exact countU
  have bound : (VG.Proof.Argon2.X86_64.Initial.headerBytes s).length + VG.Proof.Argon2.X86_64.Initial.inputSize s VG.Proof.Argon2.X86_64.Initial.inputs < 2 ^ 64 := by
    have hp := (ready (passwordOffset, passwordLenOffset) (by decide)).length
    have hs := (ready (saltOffset, saltLenOffset) (by decide)).length
    have hk := (ready (secretOffset, secretLenOffset) (by decide)).length
    have ha := (ready (adOffset, adLenOffset) (by decide)).length
    simp only at hp hs hk ha
    rw [VG.Proof.Argon2.X86_64.Initial.headerBytes_length]
    change 24 + (4 + (wordAt s passwordLenOffset).toNat +
      (4 + (wordAt s saltLenOffset).toNat + (4 + (wordAt s secretLenOffset).toNat +
      (4 + (wordAt s adLenOffset).toNat + 0)))) < 2 ^ 64
    omega
  refine (VG.Proof.Argon2.X86_64.Initial.remaining_ok v VG.Proof.Argon2.X86_64.Initial.inputs u (space.keeps ku) (fun p hp => (ready p hp).keeps ku)
    _ reprU count (by rw [VG.Proof.Argon2.X86_64.Initial.inputSize_keeps VG.Proof.Argon2.X86_64.Initial.inputs ready ku]; exact bound)).mono ?_
  rintro t ⟨digestT, ft⟩
  refine ⟨?_, ft.before ku⟩
  rw [ku.rbp, VG.Proof.Argon2.X86_64.Initial.message_keeps VG.Proof.Argon2.X86_64.Initial.inputs _ ready ku] at digestT
  rw [Proof.Argon2.H_stream, ← digestT]
  exact (List.take_of_length_le (by simp only [bytesAt, List.length_map, List.length_range,
    Nat.le_refl])).symm

/-- The public header is supplied by the enclosing argument-validation proof.
The byte-string contents remain unrestricted. -/
theorem initialHash_ok (v : Proof.Blake2.X86_64.Backend) (s : State) (space : VG.Proof.Argon2.X86_64.Initial.Space s)
    (ready : ∀ p ∈ VG.Proof.Argon2.X86_64.Initial.inputs, VG.Proof.Argon2.X86_64.Initial.InputReady s p.1 p.2) (p : Spec.Argon2.Params)
    (header : VG.Proof.Argon2.X86_64.Initial.headerBytes s = Proof.Argon2.initialHeader p) :
    WP isa (VG.Impl.Argon2.X86_64.Initial.code (HPrime.hash v)) s fun t =>
      bytesAt t.mem (s.gpr .rbp) 64 = Spec.Argon2.initialHash p
        (VG.Proof.Argon2.X86_64.Initial.inputBytes s passwordOffset passwordLenOffset) (VG.Proof.Argon2.X86_64.Initial.inputBytes s saltOffset saltLenOffset)
        (VG.Proof.Argon2.X86_64.Initial.inputBytes s secretOffset secretLenOffset) (VG.Proof.Argon2.X86_64.Initial.inputBytes s adOffset adLenOffset) ∧
      VG.Proof.Argon2.X86_64.Initial.Finished s t := by
  refine (VG.Proof.Argon2.X86_64.Initial.code_ok v s space ready).mono ?_
  rintro t ⟨digest, frame⟩
  refine ⟨?_, frame⟩
  rw [header] at digest
  exact digest

end VG.Proof.Argon2.X86_64.Initial

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.InitialBody`. -/
section

/-! Merged from `Proof.Argon2.X86_64.InitialMetadata`. -/
section
/-! H₀ writes its digest into the frame while retaining all enclosing arguments. -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64

theorem Finished.rbp {s t : State} (h : VG.Proof.Argon2.X86_64.Initial.Finished s t) : t.gpr .rbp = s.gpr .rbp :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Finished.rbx {s t : State} (h : VG.Proof.Argon2.X86_64.Initial.Finished s t) : t.gpr .rbx = s.gpr .rbx :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Finished.rsp {s t : State} (h : VG.Proof.Argon2.X86_64.Initial.Finished s t) : t.gpr .rsp = s.gpr .rsp :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Finished.frame_word {s t : State} (h : VG.Proof.Argon2.X86_64.Initial.Finished s t) (space : Space s)
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
        (Or.inr afterDigest) (by omega) (by decide)

end VG.Proof.Argon2.X86_64.Initial
end

/-! Merged from `Proof.Argon2.X86_64.InitialBodyReady`. -/
section
/-! H₀ retains the allocation and parameter environment of complete derivation. -/

namespace VG.Proof.Argon2.X86_64.InitialBody

open VG VG.X86_64 VG.Spec.Argon2

theorem hashed_environment {s t : State} {p : Params} (h : InitFill.Ready p s) (space : Initial.Space s) (done : Initial.Finished s t) : FillSetup.Environment p t := by
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word space 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work s := done.frame_word space 248 (by decide) (by decide)
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
  have base : ReductionState.matrix t = ReductionState.matrix s := done.frame_word space 232 (by decide) (by decide)
  have output : FinalOutput.output t = FinalOutput.output s := done.frame_word space 256 (by decide) (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := done.frame_word space 248 (by decide) (by decide)
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
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word space 232 (by decide) (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := done.frame_word space 248 (by decide) (by decide)
  refine ⟨?_, VG.Proof.Argon2.X86_64.InitialBody.hashed_environment h space done, VG.Proof.Argon2.X86_64.InitialBody.hashed_output h space done, h.positive, ?_⟩
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

theorem code_ok [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State) (p : Params) (h : VG.Proof.Argon2.X86_64.InitialBody.Ready p s) :
    WP isa (Impl.Argon2.X86_64.InitialBody.code name (HPrime.hash v)) s (VG.Proof.Argon2.X86_64.InitialBody.Done s · p) := by
  unfold Impl.Argon2.X86_64.InitialBody.code
  refine WP.seq ((Initial.initialHash_ok v s h.hashSpace h.inputs p h.header).mono ?_)
  rintro a ⟨digest, hashed⟩
  refine (InitFill.code_ok v name a p (VG.Proof.Argon2.X86_64.InitialBody.hashed_ready h.filling h.hashSpace hashed)).mono ?_
  intro t filled
  have base : FillKernel.matrix a = FillKernel.matrix s := hashed.frame_word h.hashSpace 232 (by decide) (by decide)
  have work : FinalOutput.work a = FinalOutput.work s := hashed.frame_word h.hashSpace 248 (by decide) (by decide)
  have output : FinalOutput.output a = FinalOutput.output s := hashed.frame_word h.hashSpace 256 (by decide) (by decide)
  refine ⟨?_, filled.bp.trans hashed.rbp, filled.sp.trans hashed.rsp,
    filled.rd.trans hashed.rd, filled.wr.trans hashed.wr, ?_⟩
  · have result := filled.digest
    rw [output, hashed.rbp, digest, InitFill.result_derive] at result
    exact result
  · have frame := filled.frame
    rw [InitFill.writes_eq s a p hashed.rbp hashed.rsp base work output] at frame
    exact (VG.Proof.Argon2.X86_64.InitialBody.hash_frame h.filling hashed).trans frame

end VG.Proof.Argon2.X86_64.InitialBody

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.InitialBodyState`. -/
section

/-! The complete body depends on the frame, allocation, and computed lane length. -/

namespace VG.Proof.Argon2.X86_64.InitialBody

open VG VG.X86_64 VG.Spec.Argon2

structure SameFrame (s t : State) : Prop where
  bp : t.gpr .rbp = s.gpr .rbp
  bx : t.gpr .rbx = s.gpr .rbx
  sp : t.gpr .rsp = s.gpr .rsp
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem SameFrame.word {s t : State} (k : VG.Proof.Argon2.X86_64.InitialBody.SameFrame s t) (d : Nat) :
    Initial.wordAt t d = Initial.wordAt s d := by
  unfold Initial.wordAt; rw [k.mem, k.bp]

theorem SameFrame.inputBytes {s t : State} (k : VG.Proof.Argon2.X86_64.InitialBody.SameFrame s t) (po lo : Nat) :
    Initial.inputBytes t po lo = Initial.inputBytes s po lo := by
  unfold Initial.inputBytes; rw [k.word po, k.word lo, k.mem]

theorem SameFrame.hashSpace {s t : State} (k : VG.Proof.Argon2.X86_64.InitialBody.SameFrame s t)
    (h : Initial.Space s) : Initial.Space t := by
  constructor
  · rw [k.bx, k.wr]; exact h.work
  · rw [k.sp, k.bx]; exact h.stackWork
  · rw [k.bp, k.bx]; exact h.frameWork
  · rw [k.bp, k.sp]; exact h.frameStack
  · rw [k.rd, k.wr, k.bp]; exact h.readable
  · rw [k.wr, k.bp]; exact h.output

theorem SameFrame.input {s t : State} (k : VG.Proof.Argon2.X86_64.InitialBody.SameFrame s t) {po lo : Nat}
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

theorem SameFrame.output {s t : State} (k : VG.Proof.Argon2.X86_64.InitialBody.SameFrame s t) {p : Params}
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

theorem SameFrame.filling {s t : State} (k : VG.Proof.Argon2.X86_64.InitialBody.SameFrame s t) {p : Params}
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

theorem Ready.of_state {s t : State} {p : Params} (h : VG.Proof.Argon2.X86_64.InitialBody.Ready p s)
    (k : VG.Proof.Argon2.X86_64.InitialBody.SameFrame s t) (laneLength : t.gpr .r13 = BitVec.ofNat 64 p.laneLen) : VG.Proof.Argon2.X86_64.InitialBody.Ready p t := by
  refine ⟨k.hashSpace h.hashSpace, fun input hi => k.input (h.inputs input hi), ?_,
    k.filling h.filling laneLength⟩
  have header : Initial.headerBytes t = Initial.headerBytes s := by
    unfold Initial.headerBytes
    simp only [Initial.headerValue, Initial.wordAt, k.mem, k.bp]
  exact header.trans h.header

end VG.Proof.Argon2.X86_64.InitialBody

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.InitialBodyReviewedState`. -/
section

/-! Merged from `Proof.Argon2.X86_64.InitialCTState`. -/
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

theorem agreeBases_taint {s t : State} (h : VG.Proof.Argon2.X86_64.Initial.AgreeBases s t) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rbp, .rbx]) s t := by
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

theorem header_rel : RelCT isa VG.Proof.Argon2.X86_64.Initial.AgreeBases headerCode (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp, .rbx])
    (fun _ _ h => VG.Proof.Argon2.X86_64.Initial.agreeBases_taint h) (by taint_decide)

theorem lengthArgs_rel (offset : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs [.rbp, .rbx])
      (.block (lengthArgs offset)) hint).isSome = true) :
    RelCT isa VG.Proof.Argon2.X86_64.Initial.AgreeBases (.block (lengthArgs offset)) (fun _ _ => True) := by
  obtain ⟨_, check⟩ := ct
  exact RelCT.taint (A := taint) (Taint.ofRegs [.rbp, .rbx])
    (fun _ _ h => VG.Proof.Argon2.X86_64.Initial.agreeBases_taint h) check

theorem inputArgs_rel (offset : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs [.rbp])
      (.block (inputArgs offset)) hint).isSome = true) :
    RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (inputArgs offset)) (fun _ _ => True) := by
  obtain ⟨_, check⟩ := ct
  exact RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h)) check

/-- All four concrete input blocks use their checked public base address. -/
theorem inputs_rel :
    RelCT isa VG.Proof.Argon2.X86_64.Initial.AgreeBases (.block (lengthArgs passwordLenOffset)) (fun _ _ => True) ∧
    RelCT isa VG.Proof.Argon2.X86_64.Initial.AgreeBases (.block (lengthArgs saltLenOffset)) (fun _ _ => True) ∧
    RelCT isa VG.Proof.Argon2.X86_64.Initial.AgreeBases (.block (lengthArgs secretLenOffset)) (fun _ _ => True) ∧
    RelCT isa VG.Proof.Argon2.X86_64.Initial.AgreeBases (.block (lengthArgs adLenOffset)) (fun _ _ => True) ∧
    RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (inputArgs passwordOffset)) (fun _ _ => True) ∧
    RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (inputArgs saltOffset)) (fun _ _ => True) ∧
    RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (inputArgs secretOffset)) (fun _ _ => True) ∧
    RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (inputArgs adOffset)) (fun _ _ => True) :=
  ⟨VG.Proof.Argon2.X86_64.Initial.lengthArgs_rel _ ⟨_, by taint_decide⟩, VG.Proof.Argon2.X86_64.Initial.lengthArgs_rel _ ⟨_, by taint_decide⟩,
    VG.Proof.Argon2.X86_64.Initial.lengthArgs_rel _ ⟨_, by taint_decide⟩, VG.Proof.Argon2.X86_64.Initial.lengthArgs_rel _ ⟨_, by taint_decide⟩,
    VG.Proof.Argon2.X86_64.Initial.inputArgs_rel _ ⟨_, by taint_decide⟩, VG.Proof.Argon2.X86_64.Initial.inputArgs_rel _ ⟨_, by taint_decide⟩,
    VG.Proof.Argon2.X86_64.Initial.inputArgs_rel _ ⟨_, by taint_decide⟩, VG.Proof.Argon2.X86_64.Initial.inputArgs_rel _ ⟨_, by taint_decide⟩⟩

end VG.Proof.Argon2.X86_64.Initial
end

/-! Public input metadata survives every hash call without relating input bytes. -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64

structure Ready (s : State) : Prop where
  space : Space s
  inputs : ∀ input ∈ VG.Proof.Argon2.X86_64.Initial.inputs, VG.Proof.Argon2.X86_64.Initial.InputReady s input.1 input.2

theorem Ready.keeps {s t : State} (h : VG.Proof.Argon2.X86_64.Initial.Ready s) (k : Keeps s t) : VG.Proof.Argon2.X86_64.Initial.Ready t :=
  ⟨h.space.keeps k, fun p hp => (h.inputs p hp).keeps k⟩

structure Related (s t : State) : Prop where
  left : VG.Proof.Argon2.X86_64.Initial.Ready s
  right : VG.Proof.Argon2.X86_64.Initial.Ready t
  bp : s.gpr .rbp = t.gpr .rbp
  bx : s.gpr .rbx = t.gpr .rbx
  sp : s.gpr .rsp = t.gpr .rsp
  words : ∀ d ∈ slots, wordAt s d = wordAt t d

theorem Related.keeps {s₁ s₂ t₁ t₂ : State} (h : VG.Proof.Argon2.X86_64.Initial.Related s₁ s₂)
    (k₁ : Keeps s₁ t₁) (k₂ : Keeps s₂ t₂) : VG.Proof.Argon2.X86_64.Initial.Related t₁ t₂ := by
  refine ⟨h.left.keeps k₁, h.right.keeps k₂, ?_, ?_, ?_, ?_⟩
  · rw [k₁.rbp, k₂.rbp, h.bp]
  · rw [k₁.rbx, k₂.rbx, h.bx]
  · rw [k₁.rsp, k₂.rsp, h.sp]
  · intro d hd
    have bound : ∀ d ∈ slots, d + 8 ≤ 272 := by decide
    rw [h.left.space.word_keeps k₁ d (bound d hd), h.right.space.word_keeps k₂ d (bound d hd)]
    exact h.words d hd

def RelatedRegs (rs : List Reg) (s t : State) : Prop :=
  VG.Proof.Argon2.X86_64.Initial.Related s t ∧ HPrime.AgreeRegs rs s t

theorem hash_keeps_rel {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (saved : ∀ r ∈ rs, r ∈ calleeSaved)
    (ct : RelCT isa P c (fun _ _ => True))
    (pre : ∀ s t, P s t → VG.Proof.Argon2.X86_64.Initial.RelatedRegs rs s t)
    (wp : ∀ s t, P s t → WP isa c s (HPrime.Keeps s) ∧ WP isa c t (HPrime.Keeps t)) :
    RelCT isa P c (VG.Proof.Argon2.X86_64.Initial.RelatedRegs rs) := by
  apply (ct.wpDep wp).mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ha, hb⟩
  have h := pre s t hp
  refine ⟨h.1.keeps (Keeps.of_hash ha) (Keeps.of_hash hb), ?_⟩
  intro r hr
  rw [ha.regs r (saved r hr), hb.regs r (saved r hr)]
  exact h.2 r hr

theorem finalize_ready {s : State} (h : VG.Proof.Argon2.X86_64.Initial.Ready s) : HPrime.FinalizeReady s :=
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
  have ht := h.keeps k
  have len : (t.gpr .rcx).toNat = 4 := by rw [args.size]; rfl
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

theorem input_update_ready {s t : State} {po lo : Nat} (h : VG.Proof.Argon2.X86_64.Initial.InputReady s po lo)
    (length : s.gpr .r14 = wordAt s lo) (args : InputArgs s t po) : HPrime.UpdateReady t := by
  have k := args.keeps
  have ptr : t.gpr .rdx = wordAt s po := args.pointer
  have len : t.gpr .rcx = wordAt s lo := args.length.trans length
  refine ⟨(h.space.keeps k).work, ?_, ?_, ?_, (h.space.keeps k).stackWork, ?_⟩
  · rw [ptr, len, k.rd, k.wr]; exact h.cover
  · rw [ptr, len, k.rbx]; exact h.work.sub_right (Region.sub_prefix (by decide))
  · rw [ptr, len, k.rbx]; exact h.work.sub_right (Offset.sub_base _ (by decide))
  · rw [ptr, len, k.rsp]; exact h.stack.symm

structure LengthRelated (lo : Nat) (s t : State) : Prop where
  related : VG.Proof.Argon2.X86_64.Initial.RelatedRegs [.r12, .r14] s t
  leftLength : s.gpr .r14 = wordAt s lo
  rightLength : t.gpr .r14 = wordAt t lo

theorem LengthRelated.hash_keeps {lo : Nat} {s t a b : State} (h : VG.Proof.Argon2.X86_64.Initial.LengthRelated lo s t)
    (bound : lo + 8 ≤ 272) (ka : HPrime.Keeps s a) (kb : HPrime.Keeps t b) : VG.Proof.Argon2.X86_64.Initial.LengthRelated lo a b := by
  refine ⟨⟨h.related.1.keeps (Keeps.of_hash ka) (Keeps.of_hash kb), ?_⟩, ?_, ?_⟩
  · intro r hr
    have saved : ∀ r ∈ ([.r12, .r14] : List Reg), r ∈ calleeSaved := by decide
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

theorem digestLength_rel : RelCT isa VG.Proof.Argon2.X86_64.Initial.Related (.block [.mov32 .rsi (.imm 64)])
    (fun s t => VG.Proof.Argon2.X86_64.Initial.Related s t ∧ s.gpr .rsi = 64 ∧ t.gpr .rsi = 64) := by
  have ct := (RelCT.taint (A := taint) (P := VG.Proof.Argon2.X86_64.Initial.Related) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.mov32 .rsi (.imm 64)]) (by taint_decide)).wpDep
    (fun s t _ => ⟨VG.Proof.Argon2.X86_64.Initial.digestLength_ok s, VG.Proof.Argon2.X86_64.Initial.digestLength_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨la, _, ka⟩, ⟨lb, _, kb⟩⟩
  exact ⟨hp.keeps (Keeps.of_hash ka) (Keeps.of_hash kb), la, lb⟩

theorem init_hash_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (fun s t => VG.Proof.Argon2.X86_64.Initial.Related s t ∧ s.gpr .rsi = 64 ∧ t.gpr .rsi = 64)
      (Impl.Argon2.X86_64.HPrime.init (HPrime.hash v)) VG.Proof.Argon2.X86_64.Initial.Related := by
  have ready (s : State) (h : VG.Proof.Argon2.X86_64.Initial.Ready s) (len : s.gpr .rsi = 64) : HPrime.InitReady s :=
    ⟨by rw [len]; decide, h.space.work,
      (h.space.stackWork.sub_left (below_sub (by decide) (by decide))).sub_right (Region.sub_prefix (by decide))⟩
  have ct := HPrime.init_rel v (P := fun s t => VG.Proof.Argon2.X86_64.Initial.Related s t ∧ s.gpr .rsi = 64 ∧ t.gpr .rsi = 64)
    (fun s t ⟨h, ls, lt⟩ => ⟨ready s h.left ls, ready t h.right lt,
      h.bx, ls.trans lt.symm, h.sp⟩)
  have result := VG.Proof.Argon2.X86_64.Initial.hash_keeps_rel [] (by simp) ct (fun _ _ h => ⟨h.1, by simp [HPrime.AgreeRegs]⟩)
    (fun s t ⟨h, ls, lt⟩ => ⟨HPrime.init_keeps v s (ready s h.left ls), HPrime.init_keeps v t (ready t h.right lt)⟩)
  exact result.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem header_state_rel : RelCT isa VG.Proof.Argon2.X86_64.Initial.Related headerCode VG.Proof.Argon2.X86_64.Initial.Related := by
  have ct := (header_rel.mono (P' := VG.Proof.Argon2.X86_64.Initial.Related) (fun _ _ h => ⟨h.bp, h.bx⟩)
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨VG.Proof.Argon2.X86_64.Initial.headerWords_ok s 6 (by decide) h.left.space, VG.Proof.Argon2.X86_64.Initial.headerWords_ok t 6 (by decide) h.right.space⟩)
  exact ct.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, hp, ⟨_, ka⟩, ⟨_, kb⟩⟩ => hp.keeps ka kb)

theorem fixed_header_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa VG.Proof.Argon2.X86_64.Initial.Related (Impl.Argon2.X86_64.HPrime.absorbFixed (HPrime.hash v) 768 24) VG.Proof.Argon2.X86_64.Initial.Related := by
  have args := (RelCT.taint (A := taint) (P := VG.Proof.Argon2.X86_64.Initial.Related) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block (Impl.Argon2.X86_64.HPrime.fixedArgs 768 24)) (by taint_decide)).wpDep
    (fun s t _ => ⟨HPrime.fixedArgs_ok s 768 24 (by decide) (by decide),
      HPrime.fixedArgs_ok t 768 24 (by decide) (by decide)⟩)
  have call := HPrime.update_rel v (P := fun a b => True ∧ ∃ s t, VG.Proof.Argon2.X86_64.Initial.Related s t ∧
      HPrime.FixedArgs s a 768 24 ∧ HPrime.FixedArgs t b 768 24)
    (fun a b ⟨_, s, t, hp, ha, hb⟩ => ⟨HPrime.fixed_ready (VG.Proof.Argon2.X86_64.Initial.finalize_ready hp.left) ha (by decide) (by decide),
      HPrime.fixed_ready (VG.Proof.Argon2.X86_64.Initial.finalize_ready hp.right) hb (by decide) (by decide),
      by rw [ha.keeps.rbx, hb.keeps.rbx, hp.bx], by rw [ha.count, hb.count],
      by rw [ha.data, hb.data, hp.bx], by rw [ha.size, hb.size], by rw [ha.keeps.rsp, hb.keeps.rsp, hp.sp]⟩)
  have ct := args.seq call
  have result := VG.Proof.Argon2.X86_64.Initial.hash_keeps_rel [] (by simp) ct (fun _ _ h => ⟨h, by simp [HPrime.AgreeRegs]⟩)
    (fun s t h => ⟨HPrime.absorbFixed_keeps v s 768 24 (VG.Proof.Argon2.X86_64.Initial.finalize_ready h.left) (by decide) (by decide),
      HPrime.absorbFixed_keeps v t 768 24 (VG.Proof.Argon2.X86_64.Initial.finalize_ready h.right) (by decide) (by decide)⟩)
  exact result.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem initialCount_rel : RelCT isa VG.Proof.Argon2.X86_64.Initial.Related (.block [.mov32 .r12 (.imm 24)]) (VG.Proof.Argon2.X86_64.Initial.RelatedRegs [.r12]) := by
  have ct := (RelCT.taint (A := taint) (P := VG.Proof.Argon2.X86_64.Initial.Related) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.mov32 .r12 (.imm 24)]) (by taint_decide)).wpDep
    (fun s t _ => ⟨VG.Proof.Argon2.X86_64.Initial.initialCount_ok s, VG.Proof.Argon2.X86_64.Initial.initialCount_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨la, _, ka⟩, ⟨lb, _, kb⟩⟩
  refine ⟨hp.keeps ka kb, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact la.trans lb.symm

theorem start_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa VG.Proof.Argon2.X86_64.Initial.Related (start (HPrime.hash v)) (VG.Proof.Argon2.X86_64.Initial.RelatedRegs [.r12]) :=
  digestLength_rel.seq ((VG.Proof.Argon2.X86_64.Initial.init_hash_rel v).seq (header_state_rel.seq
    ((VG.Proof.Argon2.X86_64.Initial.fixed_header_rel v).seq VG.Proof.Argon2.X86_64.Initial.initialCount_rel)))

end VG.Proof.Argon2.X86_64.Initial
end

/-! Merged from `Proof.Argon2.X86_64.InitialFinishCT`. -/
section
/-! H₀ finalization and its fixed-size digest copy reveal no input contents. -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial

theorem finishCount_rel : RelCT isa (VG.Proof.Argon2.X86_64.Initial.RelatedRegs [.r12]) (.block [.mov .rsi (.reg .r12)])
    (fun s t => VG.Proof.Argon2.X86_64.Initial.RelatedRegs [.r12] s t ∧ s.gpr .rsi = t.gpr .rsi) := by
  have ct := (RelCT.taint (A := taint) (P := VG.Proof.Argon2.X86_64.Initial.RelatedRegs [.r12]) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.mov .rsi (.reg .r12)]) (by taint_decide)).wpDep
    (fun s t _ => ⟨VG.Proof.Argon2.X86_64.Initial.finishCount_ok s, VG.Proof.Argon2.X86_64.Initial.finishCount_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨ca, _, ka⟩, ⟨cb, _, kb⟩⟩
  refine ⟨⟨hp.1.keeps (Keeps.of_hash ka) (Keeps.of_hash kb), ?_⟩, ?_⟩
  · intro r hr
    simp only [List.mem_singleton] at hr; subst r
    rw [ka.regs .r12 (by decide), kb.regs .r12 (by decide)]
    exact hp.2 _ (by simp)
  · rw [ca, cb]; exact hp.2 _ (by simp)

theorem finalize_hash_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (fun s t => VG.Proof.Argon2.X86_64.Initial.RelatedRegs [.r12] s t ∧ s.gpr .rsi = t.gpr .rsi)
      (Impl.Argon2.X86_64.HPrime.finalize (HPrime.hash v)) VG.Proof.Argon2.X86_64.Initial.Related := by
  have ct := HPrime.finalize_rel v (P := fun s t => VG.Proof.Argon2.X86_64.Initial.RelatedRegs [.r12] s t ∧ s.gpr .rsi = t.gpr .rsi)
    (fun s t h => ⟨VG.Proof.Argon2.X86_64.Initial.finalize_ready h.1.1.left, VG.Proof.Argon2.X86_64.Initial.finalize_ready h.1.1.right, h.1.1.bx, h.2, h.1.1.sp⟩)
  have result := VG.Proof.Argon2.X86_64.Initial.hash_keeps_rel [] (by simp) ct (fun _ _ h => ⟨h.1.1, by simp [HPrime.AgreeRegs]⟩)
    (fun s t h => ⟨HPrime.finalize_keeps v s (VG.Proof.Argon2.X86_64.Initial.finalize_ready h.1.1.left),
      HPrime.finalize_keeps v t (VG.Proof.Argon2.X86_64.Initial.finalize_ready h.1.1.right)⟩)
  exact result.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem finishOutput_rel : RelCT isa VG.Proof.Argon2.X86_64.Initial.Related
    (.block [.mov .r14 (.reg .rbp), .mov32 .rax (.imm 64)])
      (HPrime.AgreeRegs [.rbx, .r14, .rax]) := by
  have ct := (RelCT.taint (A := taint) (P := VG.Proof.Argon2.X86_64.Initial.Related) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.mov .r14 (.reg .rbp), .mov32 .rax (.imm 64)]) (by taint_decide)).wpDep
    (fun s t _ => ⟨VG.Proof.Argon2.X86_64.Initial.finishOutput_ok s, VG.Proof.Argon2.X86_64.Initial.finishOutput_ok t⟩)
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
    RelCT isa (VG.Proof.Argon2.X86_64.Initial.RelatedRegs [.r12]) (VG.Impl.Argon2.X86_64.Initial.finish (HPrime.hash v)) (fun _ _ => True) :=
  finishCount_rel.seq ((VG.Proof.Argon2.X86_64.Initial.finalize_hash_rel v).seq (finishOutput_rel.seq VG.Proof.Argon2.X86_64.Initial.copy_digest_rel))

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
  True ∧ ∃ s t, VG.Proof.Argon2.X86_64.Initial.RelatedRegs [.r12] s t ∧ LengthArgs s lo a ∧ LengthArgs t lo b

theorem prefix_rel (v : Proof.Blake2.X86_64.Backend) (lo : Nat) (slot : lo ∈ slots)
    (bound : lo + 8 ≤ 272)
    (check : ∃ hint, (taint.check (Taint.ofRegs [.rbp, .rbx]) (.block (lengthArgs lo)) hint).isSome = true) :
    RelCT isa (VG.Proof.Argon2.X86_64.Initial.RelatedRegs [.r12])
      (.seq (.block (lengthArgs lo)) (Impl.Argon2.X86_64.HPrime.update (HPrime.hash v))) (VG.Proof.Argon2.X86_64.Initial.LengthRelated lo) := by
  have args := ((VG.Proof.Argon2.X86_64.Initial.lengthArgs_rel lo check).mono (P' := VG.Proof.Argon2.X86_64.Initial.RelatedRegs [.r12])
    (fun _ _ h => ⟨h.1.bp, h.1.bx⟩) (fun _ _ h => h)).wpDep
    (fun s t h => ⟨lengthArgs_ok s lo (h.1.left.space.readable lo slot)
      (by simpa using h.1.left.space.write 792 4 (by decide)),
      lengthArgs_ok t lo (h.1.right.space.readable lo slot)
      (by simpa using h.1.right.space.write 792 4 (by decide))⟩)
  have call := HPrime.update_rel v (P := VG.Proof.Argon2.X86_64.Initial.PrefixRelated lo) (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨VG.Proof.Argon2.X86_64.Initial.prefix_update_ready hp.1.left.space ha, VG.Proof.Argon2.X86_64.Initial.prefix_update_ready hp.1.right.space hb,
      by rw [ha.keeps.rbx, hb.keeps.rbx, hp.1.bx], by rw [ha.count, hb.count]; exact hp.2 _ (by simp),
      by rw [ha.pointer, hb.pointer, hp.1.bx], by rw [ha.size, hb.size],
      by rw [ha.keeps.rsp, hb.keeps.rsp, hp.1.sp]⟩)
  have called := call.wpDep (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨HPrime.update_keeps v a (VG.Proof.Argon2.X86_64.Initial.prefix_update_ready hp.1.left.space ha),
      HPrime.update_keeps v b (VG.Proof.Argon2.X86_64.Initial.prefix_update_ready hp.1.right.space hb)⟩)
  have finished := called.mono (fun _ _ h => h) (fun a b h => by
    obtain ⟨_, x, y, ⟨_, s, t, hp, ha, hb⟩, ka, kb⟩ := h
    have rel := hp.1.keeps ha.keeps hb.keeps
    have prepared : VG.Proof.Argon2.X86_64.Initial.LengthRelated lo x y := by
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
  True ∧ ∃ s t, VG.Proof.Argon2.X86_64.Initial.LengthRelated lo s t ∧ InputArgs s a po ∧ InputArgs t b po

theorem input_rel (v : Proof.Blake2.X86_64.Backend) (po lo : Nat) (input : (po, lo) ∈ VG.Proof.Argon2.X86_64.Initial.inputs)
    (check : ∃ hint, (taint.check (Taint.ofRegs [.rbp]) (.block (inputArgs po)) hint).isSome = true) :
    RelCT isa (VG.Proof.Argon2.X86_64.Initial.LengthRelated lo)
      (.seq (.block (inputArgs po)) (Impl.Argon2.X86_64.HPrime.update (HPrime.hash v))) (VG.Proof.Argon2.X86_64.Initial.LengthRelated lo) := by
  have args := ((VG.Proof.Argon2.X86_64.Initial.inputArgs_rel po check).mono (P' := VG.Proof.Argon2.X86_64.Initial.LengthRelated lo)
    (fun _ _ h => h.related.1.bp) (fun _ _ h => h)).wpDep
    (fun s t h => ⟨inputArgs_ok s po (h.related.1.left.space.readable po (h.related.1.left.inputs _ input).pointerSlot),
      inputArgs_ok t po (h.related.1.right.space.readable po (h.related.1.right.inputs _ input).pointerSlot)⟩)
  have call := HPrime.update_rel v (P := VG.Proof.Argon2.X86_64.Initial.InputRelated lo po) (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨VG.Proof.Argon2.X86_64.Initial.input_update_ready (hp.related.1.left.inputs _ input) hp.leftLength ha,
      VG.Proof.Argon2.X86_64.Initial.input_update_ready (hp.related.1.right.inputs _ input) hp.rightLength hb,
      by rw [ha.keeps.rbx, hb.keeps.rbx, hp.related.1.bx],
      by rw [ha.count, hb.count, hp.related.2 .r12 (by simp)],
      by rw [ha.pointer, hb.pointer]; exact hp.related.1.words po (hp.related.1.left.inputs _ input).pointerSlot,
      by rw [ha.length, hb.length]; exact hp.related.2 .r14 (by simp),
      by rw [ha.keeps.rsp, hb.keeps.rsp, hp.related.1.sp]⟩)
  have called := call.wpDep (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨HPrime.update_keeps v a (VG.Proof.Argon2.X86_64.Initial.input_update_ready (hp.related.1.left.inputs _ input) hp.leftLength ha),
      HPrime.update_keeps v b (VG.Proof.Argon2.X86_64.Initial.input_update_ready (hp.related.1.right.inputs _ input) hp.rightLength hb)⟩)
  have finished := called.mono (fun _ _ h => h) (fun a b h => by
    obtain ⟨_, x, y, ⟨_, s, t, hp, ha, hb⟩, ka, kb⟩ := h
    have left := hp.related.1.left.inputs _ input
    have right := hp.related.1.right.inputs _ input
    have prepared : VG.Proof.Argon2.X86_64.Initial.LengthRelated lo x y := by
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
    RelCT isa (VG.Proof.Argon2.X86_64.Initial.LengthRelated lo) (.block [.alu .add .r12 (.reg .r14)]) (VG.Proof.Argon2.X86_64.Initial.RelatedRegs [.r12]) := by
  have ct := (RelCT.taint (A := taint) (P := VG.Proof.Argon2.X86_64.Initial.LengthRelated lo) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.alu .add .r12 (.reg .r14)]) (by taint_decide)).wpDep
    (fun s t _ => ⟨VG.Proof.Argon2.X86_64.Initial.addCount_ok s, VG.Proof.Argon2.X86_64.Initial.addCount_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨ca, _, ka⟩, ⟨cb, _, kb⟩⟩
  refine ⟨hp.related.1.keeps ka kb, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  rw [ca, cb, hp.related.2 .r12 (by simp), hp.related.2 .r14 (by simp)]

theorem absorb_rel (v : Proof.Blake2.X86_64.Backend) (po lo : Nat) (input : (po, lo) ∈ VG.Proof.Argon2.X86_64.Initial.inputs)
    (lengthCheck : ∃ hint, (taint.check (Taint.ofRegs [.rbp, .rbx]) (.block (lengthArgs lo)) hint).isSome = true)
    (pointerCheck : ∃ hint, (taint.check (Taint.ofRegs [.rbp]) (.block (inputArgs po)) hint).isSome = true) :
    RelCT isa (VG.Proof.Argon2.X86_64.Initial.RelatedRegs [.r12]) (absorb (HPrime.hash v) po lo) (VG.Proof.Argon2.X86_64.Initial.RelatedRegs [.r12]) := by
  have slot : lo ∈ slots := by
    have all : ∀ p ∈ VG.Proof.Argon2.X86_64.Initial.inputs, p.2 ∈ slots := by decide
    exact all _ input
  have bound : lo + 8 ≤ 272 := by
    have all : ∀ d ∈ slots, d + 8 ≤ 272 := by decide
    exact all lo slot
  exact ((VG.Proof.Argon2.X86_64.Initial.prefix_rel v lo slot bound lengthCheck).seq
    (((VG.Proof.Argon2.X86_64.Initial.input_rel v po lo input pointerCheck).seq (VG.Proof.Argon2.X86_64.Initial.addCount_rel lo)).assoc)).assoc

end VG.Proof.Argon2.X86_64.Initial
end

/-! Complete H₀ is constant time for every verified BLAKE2b backend. -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial

theorem code_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa VG.Proof.Argon2.X86_64.Initial.Related (VG.Impl.Argon2.X86_64.Initial.code (HPrime.hash v)) (fun _ _ => True) :=
  (VG.Proof.Argon2.X86_64.Initial.start_rel v).seq
    ((VG.Proof.Argon2.X86_64.Initial.absorb_rel v passwordOffset passwordLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    ((VG.Proof.Argon2.X86_64.Initial.absorb_rel v saltOffset saltLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    ((VG.Proof.Argon2.X86_64.Initial.absorb_rel v secretOffset secretLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    ((VG.Proof.Argon2.X86_64.Initial.absorb_rel v adOffset adLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
      (VG.Proof.Argon2.X86_64.Initial.finish_rel v)))))

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
    RelCT isa P (.call name (VG.Impl.Argon2.X86_64.HPrime.code (HPrime.hash v))) (fun _ _ => True) := by
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
  left : VG.Proof.Argon2.X86_64.FinalOutput.Ready p s
  right : VG.Proof.Argon2.X86_64.FinalOutput.Ready p t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : ReductionState.matrix s = ReductionState.matrix t
  outputs : VG.Proof.Argon2.X86_64.FinalOutput.output s = VG.Proof.Argon2.X86_64.FinalOutput.output t
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

theorem args_rel (p : Params) : RelCT isa (VG.Proof.Argon2.X86_64.FinalOutput.Related p)
    (.block Impl.Argon2.X86_64.FinalOutput.args) (VG.Proof.Argon2.X86_64.FinalOutput.NextRelated p) := by
  have trace := args_trace.mono (P' := VG.Proof.Argon2.X86_64.FinalOutput.Related p) (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨VG.Proof.Argon2.X86_64.FinalOutput.args_ok s h.left.reads, VG.Proof.Argon2.X86_64.FinalOutput.args_ok t h.right.reads⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.ready hp.left, hb.ready hp.right, ha.inputLength, hb.inputLength,
    ha.outputLength.trans hp.left.tagWord, hb.outputLength.trans hp.right.tagWord,
    ha.input.trans (hp.matrices.trans hb.input.symm), ha.output.trans (hp.outputs.trans hb.output.symm),
    ha.work.trans (hp.works.trans hb.work.symm),
    (ha.regs .rsp (by simp [calleeSaved])).trans (hp.stacks.trans (hb.regs .rsp (by simp [calleeSaved])).symm)⟩

theorem code_rel (v : Proof.Blake2.X86_64.Backend) (name : String) (p : Params) :
    RelCT isa (VG.Proof.Argon2.X86_64.FinalOutput.Related p) (Impl.Argon2.X86_64.FinalOutput.code name (HPrime.hash v)) (fun _ _ => True) :=
  (VG.Proof.Argon2.X86_64.FinalOutput.args_rel p).seq (FinalCall.hPrime_call_rel v name p.tagLen (fun _ _ h =>
    ⟨h.left, h.right, h.leftInputLength, h.rightInputLength, h.leftOutputLength, h.rightOutputLength,
      h.inputs, h.outputs, h.works, h.stacks⟩))

end VG.Proof.Argon2.X86_64.FinalOutput
end

/-! Complete finalization has a public trace for every BLAKE2b backend. -/

namespace VG.Proof.Argon2.X86_64.Finish

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (leftMemory rightMemory : Array Block) (s t : State) : Prop where
  left : VG.Proof.Argon2.X86_64.Finish.Ready p s
  right : VG.Proof.Argon2.X86_64.Finish.Ready p t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : matrix s = matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  leftMatrix : Proof.Argon2.Represents s.mem (matrix s) p.blocks leftMemory
  rightMatrix : Proof.Argon2.Represents t.mem (matrix t) p.blocks rightMemory

theorem code_rel (v : Proof.Blake2.X86_64.Backend) (name : String) (p : Params)
    (leftMemory rightMemory : Array Block) :
    RelCT isa (VG.Proof.Argon2.X86_64.Finish.Related p leftMemory rightMemory) (Impl.Argon2.X86_64.Finish.code name (HPrime.hash v))
      (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq reduceA outputA =>
    cases eb with
    | seq reduceB outputB =>
      have related : ReductionInit.Related p leftMemory rightMemory s t :=
        ⟨hp.left.reduction, hp.right.reduction, hp.bases, hp.matrices, hp.leftMatrix, hp.rightMatrix⟩
      obtain ⟨reduceTrace, _⟩ := FinalReduction.code_rel p hp.left.reduction.allocation.positive
        leftMemory rightMemory _ _ _ _ _ _ related reduceA reduceB
      obtain ⟨_, sa, runA, doneA⟩ := FinalReduction.code_ok s p hp.left.reduction leftMemory hp.leftMatrix
      obtain ⟨_, sb, runB, doneB⟩ := FinalReduction.code_ok t p hp.right.reduction rightMemory hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det reduceA runA
      obtain ⟨_, rfl⟩ := Exec.det reduceB runB
      have finalRelated : FinalOutput.Related p _ _ :=
        ⟨output_ready hp.left doneA, output_ready hp.right doneB,
          (doneA.regs .rbp (by simp [calleeSaved]) (by decide)).trans
            (hp.bases.trans (doneB.regs .rbp (by simp [calleeSaved]) (by decide)).symm),
          (doneA.regs .rsp (by simp [calleeSaved]) (by decide)).trans
            (hp.stacks.trans (doneB.regs .rsp (by simp [calleeSaved]) (by decide)).symm),
          doneA.base.trans (hp.matrices.trans doneB.base.symm),
          (VG.Proof.Argon2.X86_64.Finish.frame_word hp.left.reduction doneA 256 (by decide)).trans
            (hp.outputs.trans (VG.Proof.Argon2.X86_64.Finish.frame_word hp.right.reduction doneB 256 (by decide)).symm),
          (VG.Proof.Argon2.X86_64.Finish.frame_word hp.left.reduction doneA 248 (by decide)).trans
            (hp.works.trans (VG.Proof.Argon2.X86_64.Finish.frame_word hp.right.reduction doneB 248 (by decide)).symm)⟩
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
    RelCT isa (SegmentSetup.Related p pass lane slice leftState rightState) VG.Impl.Argon2.X86_64.FillLanes.body
      (fun s t => s.cf = t.cf ∧ (lane + 1 < p.lanes → VG.Proof.Argon2.X86_64.FillLanes.NextRelated p pass (lane + 1) slice
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
      have bases := (filledA.regs .rbp (by simp [calleeSaved]) (by decide)).trans
        (hp.ready.bases.trans (filledB.regs .rbp (by simp [calleeSaved]) (by decide)).symm)
      obtain ⟨advancedTrace, _⟩ := VG.Proof.Argon2.X86_64.FillLanes.advance_rel _ _ _ _ _ _ bases advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := VG.Proof.Argon2.X86_64.FillLanes.body_ok s p pass lane slice hp.ready.left leftState hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := VG.Proof.Argon2.X86_64.FillLanes.body_ok t p pass lane slice hp.ready.right rightState hp.rightMatrix
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
    RelCT isa (VG.Proof.Argon2.X86_64.FillLanes.Related p pass lane slice count leftState rightState) Impl.Argon2.X86_64.FillLanes.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (lane : Nat) (leftState rightState : FillState),
    lane + n = p.lanes ∧ 0 < n ∧ VG.Proof.Argon2.X86_64.FillLanes.Related p pass lane slice n leftState rightState s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.X86_64.FillLanes.body fun s t =>
      isa.eval .b s = isa.eval .b t ∧ (isa.eval .b s = some false → True) ∧
        (isa.eval .b s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, ls, rs, endLane, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      have segmentRelated : SegmentSetup.Related p pass j slice ls rs s t :=
        ⟨hp.ready, hp.leftMatrix, hp.rightMatrix, Proof.Argon2.lanes_first_segment p pass slice j n ls rs
          hp.ready.left.parameters.segment_bound.1 hp.indices⟩
      obtain ⟨trace, flags, next⟩ := VG.Proof.Argon2.X86_64.FillLanes.body_rel p pass j slice ls rs _ _ _ _ _ _ segmentRelated ea eb
      obtain ⟨_, a', runA, done⟩ := VG.Proof.Argon2.X86_64.FillLanes.body_ok s p pass j slice hp.ready.left ls hp.leftMatrix
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · simp only [eval, flags]
      · intro taken
        have active : j + 1 < p.lanes := by
          simp only [eval, done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        obtain ⟨ready, matrixA, matrixB⟩ := next active
        have indices := hp.indices
        rw [Proof.Argon2.lanes_succ, Proof.Argon2.lanes_succ] at indices
        exact ⟨n, by omega, j + 1, Proof.Argon2.segment p pass j slice 0 p.segmentLen ls,
          Proof.Argon2.segment p pass j slice 0 p.segmentLen rs, by omega, by omega, ready, matrixA, matrixB, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨lane, leftState, rightState, endLane, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.FillLanes
end

/-! A complete slice exposes only its specified reference log. -/

namespace VG.Proof.Argon2.X86_64.FillSlice

open VG VG.X86_64 VG.Spec.Argon2

structure Related (p : Params) (pass slice : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : VG.Proof.Argon2.X86_64.FillSlice.Ready p pass slice s
  right : VG.Proof.Argon2.X86_64.FillSlice.Ready p pass slice t
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
    RelCT isa (VG.Proof.Argon2.X86_64.FillSlice.Related p pass slice leftState rightState) (.block Impl.Argon2.X86_64.FillSlice.setup)
      (FillLanes.Related p pass 0 slice p.lanes leftState rightState) := by
  have trace := setup_trace.mono (P' := VG.Proof.Argon2.X86_64.FillSlice.Related p pass slice leftState rightState)
    (fun _ _ _ => trivial) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨VG.Proof.Argon2.X86_64.FillSlice.setup_ok s p pass slice h.left, VG.Proof.Argon2.X86_64.FillSlice.setup_ok t p pass slice h.right⟩)
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
    RelCT isa (VG.Proof.Argon2.X86_64.FillSlice.Related p pass slice leftState rightState) Impl.Argon2.X86_64.FillSlice.code (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq setupA lanesA =>
    cases eb with
    | seq setupB lanesB =>
      obtain ⟨setupTrace, related⟩ := VG.Proof.Argon2.X86_64.FillSlice.setup_public_rel p pass slice leftState rightState _ _ _ _ _ _ hp setupA setupB
      obtain ⟨lanesTrace, _⟩ := FillLanes.loop_rel p pass 0 slice p.lanes leftState rightState
        hp.left.parameters.lanesPositive (by omega) _ _ _ _ _ _ related lanesA lanesB
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
    RelCT isa (FillSlice.Related p pass slice leftState rightState) VG.Impl.Argon2.X86_64.FillSlices.body
      (fun s t => s.cf = t.cf ∧ (slice + 1 < 4 → VG.Proof.Argon2.X86_64.FillSlices.NextRelated p pass (slice + 1)
        (Proof.Argon2.lanes p pass slice 0 p.lanes leftState) (Proof.Argon2.lanes p pass slice 0 p.lanes rightState) s t)) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq sliceA advanceA =>
    cases eb with
    | seq sliceB advanceB =>
      obtain ⟨sliceTrace, _⟩ := FillSlice.code_rel p pass slice leftState rightState _ _ _ _ _ _ hp sliceA sliceB
      obtain ⟨advanceTrace, _⟩ := VG.Proof.Argon2.X86_64.FillSlices.advance_rel _ _ _ _ _ _ trivial advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := VG.Proof.Argon2.X86_64.FillSlices.body_ok s p pass slice hp.left leftState hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := VG.Proof.Argon2.X86_64.FillSlices.body_ok t p pass slice hp.right rightState hp.rightMatrix
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
  states : VG.Proof.Argon2.X86_64.FillSlices.NextRelated p pass slice leftState rightState s t
  indices : (Proof.Argon2.slices p pass slice count leftState).indices =
    (Proof.Argon2.slices p pass slice count rightState).indices

theorem loop_rel [CompressImpl] (p : Params) (pass slice count : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endSlice : slice + count = 4) :
    RelCT isa (VG.Proof.Argon2.X86_64.FillSlices.Related p pass slice count leftState rightState) Impl.Argon2.X86_64.FillSlices.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (slice : Nat) (leftState rightState : FillState),
    slice + n = 4 ∧ 0 < n ∧ VG.Proof.Argon2.X86_64.FillSlices.Related p pass slice n leftState rightState s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.X86_64.FillSlices.body fun s t =>
      isa.eval .b s = isa.eval .b t ∧ (isa.eval .b s = some false → True) ∧
        (isa.eval .b s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, ls, rs, endSlice, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      have sliceRelated : FillSlice.Related p pass j ls rs s t :=
        ⟨hp.states.left, hp.states.right, hp.states.bases, hp.states.stacks, hp.states.matrices, hp.states.work,
          hp.states.leftMatrix, hp.states.rightMatrix, Proof.Argon2.slices_first_lane_fold p pass j n ls rs
            hp.states.left.parameters.segment_bound.1 hp.indices⟩
      obtain ⟨trace, flags, next⟩ := VG.Proof.Argon2.X86_64.FillSlices.body_rel p pass j ls rs _ _ _ _ _ _ sliceRelated ea eb
      obtain ⟨_, a', runA, done⟩ := VG.Proof.Argon2.X86_64.FillSlices.body_ok s p pass j hp.states.left ls hp.states.leftMatrix
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · simp only [eval, flags]
      · intro taken
        have active : j + 1 < 4 := by
          simp only [eval, done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        have indices := hp.indices
        rw [Proof.Argon2.slices_succ, Proof.Argon2.slices_succ] at indices
        exact ⟨n, by omega, j + 1, Proof.Argon2.lanes p pass j 0 p.lanes ls,
          Proof.Argon2.lanes p pass j 0 p.lanes rs, by omega, by omega, next active, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨slice, leftState, rightState, endSlice, positive, h⟩) (fun _ _ h => h)

theorem pass_rel [CompressImpl] (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (fun s t => VG.Proof.Argon2.X86_64.FillSlices.NextRelated p pass 0 leftState rightState s t ∧
      (fillPass p leftState pass).indices = (fillPass p rightState pass).indices)
      Impl.Argon2.X86_64.FillSlices.loop (fun _ _ => True) := by
  refine (VG.Proof.Argon2.X86_64.FillSlices.loop_rel p pass 0 4 leftState rightState (by decide) (by decide)).mono ?_ (fun _ _ h => h)
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
  left : VG.Proof.Argon2.X86_64.FillIteration.Ready p pass s
  right : VG.Proof.Argon2.X86_64.FillIteration.Ready p pass t
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
    RelCT isa (VG.Proof.Argon2.X86_64.FillIteration.Related p pass leftState rightState) (.block Impl.Argon2.X86_64.FillIteration.setup)
      (fun s t => FillSlices.NextRelated p pass 0 leftState rightState s t ∧
        (fillPass p leftState pass).indices = (fillPass p rightState pass).indices) := by
  have trace := setup_trace.mono (P' := VG.Proof.Argon2.X86_64.FillIteration.Related p pass leftState rightState)
    (fun _ _ _ => trivial) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨VG.Proof.Argon2.X86_64.FillIteration.setup_ok s p pass h.left, VG.Proof.Argon2.X86_64.FillIteration.setup_ok t p pass h.right⟩)
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
    RelCT isa (VG.Proof.Argon2.X86_64.FillIteration.Related p pass leftState rightState) Impl.Argon2.X86_64.FillIteration.code (fun _ _ => True) :=
  (VG.Proof.Argon2.X86_64.FillIteration.setup_public_rel p pass leftState rightState).seq (FillSlices.pass_rel p pass leftState rightState)

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
  left : VG.Proof.Argon2.X86_64.FillIterations.Ready p pass s
  right : VG.Proof.Argon2.X86_64.FillIterations.Ready p pass t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel [CompressImpl] (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (fun s t => VG.Proof.Argon2.X86_64.FillIterations.NextRelated p pass leftState rightState s t ∧
      (fillPass p leftState pass).indices = (fillPass p rightState pass).indices) VG.Impl.Argon2.X86_64.FillIterations.body
      (fun s t => s.cf = t.cf ∧ (pass + 1 < p.passes → VG.Proof.Argon2.X86_64.FillIterations.NextRelated p (pass + 1)
        (fillPass p leftState pass)
        (fillPass p rightState pass) s t)) := by
  intro s t ts tt a b hp ea eb
  obtain ⟨hp, indices⟩ := hp
  have related : FillIteration.Related p pass leftState rightState s t :=
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
      have bases := (filledA.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).trans
        (hp.bases.trans (filledB.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).symm)
      obtain ⟨advancedTrace, _⟩ := VG.Proof.Argon2.X86_64.FillIterations.advance_rel _ _ _ _ _ _ bases advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := VG.Proof.Argon2.X86_64.FillIterations.body_ok s p pass hp.left leftState hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := VG.Proof.Argon2.X86_64.FillIterations.body_ok t p pass hp.right rightState hp.rightMatrix
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
  ready : VG.Proof.Argon2.X86_64.FillIterations.NextRelated p pass leftState rightState s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.iterations p pass count leftState).indices =
    (Proof.Argon2.iterations p pass count rightState).indices

theorem loop_rel [CompressImpl] (p : Params) (pass count : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endPass : pass + count = p.passes) :
    RelCT isa (VG.Proof.Argon2.X86_64.FillIterations.Related p pass count leftState rightState) Impl.Argon2.X86_64.FillIterations.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (pass : Nat) (leftState rightState : FillState),
    pass + n = p.passes ∧ 0 < n ∧ VG.Proof.Argon2.X86_64.FillIterations.Related p pass n leftState rightState s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.X86_64.FillIterations.body fun s t =>
      isa.eval .b s = isa.eval .b t ∧ (isa.eval .b s = some false → True) ∧
        (isa.eval .b s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, ls, rs, endPass, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      have passIndices := Proof.Argon2.iterations_first_pass p j n ls rs
        hp.ready.left.filling.parameters.segment_bound.1 hp.indices
      obtain ⟨trace, flags, next⟩ := VG.Proof.Argon2.X86_64.FillIterations.body_rel p j ls rs _ _ _ _ _ _ ⟨hp.ready, passIndices⟩ ea eb
      obtain ⟨_, a', runA, done⟩ := VG.Proof.Argon2.X86_64.FillIterations.body_ok s p j hp.ready.left ls hp.leftMatrix
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · simp only [eval, flags]
      · intro taken
        have active : j + 1 < p.passes := by
          simp only [eval, done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        have ready := next active
        have indices := hp.indices
        rw [Proof.Argon2.iterations_succ, Proof.Argon2.iterations_succ] at indices
        exact ⟨n, by omega, j + 1, fillPass p ls j,
          fillPass p rs j, by omega, by omega, ready, ready.leftMatrix, ready.rightMatrix, indices⟩
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
  left : VG.Proof.Argon2.X86_64.FillFinish.Ready p s
  right : VG.Proof.Argon2.X86_64.FillFinish.Ready p t
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
    RelCT isa (VG.Proof.Argon2.X86_64.FillFinish.Related p leftState rightState) (Impl.Argon2.X86_64.FillFinish.code name (HPrime.hash v))
      (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq fillA finishA =>
    cases eb with
    | seq fillB finishB =>
      have related : FillIterations.Related p 0 p.passes leftState rightState s t :=
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
      have finalRelated : Finish.Related p (Proof.Argon2.iterations p 0 p.passes leftState).memory
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
  left : VG.Proof.Argon2.X86_64.InitFill.Ready p s
  right : VG.Proof.Argon2.X86_64.InitFill.Ready p t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  indices : (Proof.Argon2.iterations p 0 p.passes (VG.Proof.Argon2.X86_64.InitFill.initial p s)).indices =
    (Proof.Argon2.iterations p 0 p.passes (VG.Proof.Argon2.X86_64.InitFill.initial p t)).indices

theorem code_rel [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) (p : Params) :
    RelCT isa (VG.Proof.Argon2.X86_64.InitFill.Related p) (Impl.Argon2.X86_64.InitFill.code name (HPrime.hash v)) (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  have params := hp.left.environment.parameters
  have q : 2 ≤ p.laneLen := by
    have segments := Proof.Argon2.laneLen_segments p params.lanesPositive
    have minimum := params.segment_bound.1
    omega
  have lanesBound : p.lanes < 2 ^ 64 := Nat.lt_trans params.lanesBound (by decide)
  have pub : MemoryInit.AgreeBases s t := by
    intro r hr
    simp only [MemoryInit.publicBases, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.bases
    · exact hp.left.scratch.trans (hp.works.trans hp.right.scratch.symm)
    · exact hp.stacks
    · exact hp.left.initializing.laneLength.trans hp.right.initializing.laneLength.symm
  have rightReady : MemoryInit.Ready (FillKernel.matrix s) p.lanes p.laneLen t := by
    rw [hp.matrices]; exact hp.right.initializing
  cases ea with
  | seq initA restA =>
    cases eb with
    | seq initB restB =>
      have initTrace := MemoryInit.code_ct v name (FillKernel.matrix s) p.lanes p.laneLen
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
          have bases := doneA.bp.trans (hp.bases.trans doneB.bp.symm)
          obtain ⟨setupTrace, _⟩ := FillSetup.code_rel _ _ _ _ _ _ bases setupA setupB
          obtain ⟨_, ca, runA, preparedA⟩ := FillSetup.code_ok _ p (initialized_setup hp.left doneA)
          obtain ⟨_, cb, runB, preparedB⟩ := FillSetup.code_ok _ p (initialized_setup hp.right doneB)
          obtain ⟨_, rfl⟩ := Exec.det setupA runA
          obtain ⟨_, rfl⟩ := Exec.det setupB runB
          have preparedBases := (preparedA.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide) (by decide)).trans
            (bases.trans (preparedB.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide) (by decide)).symm)
          have preparedStacks := (preparedA.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide) (by decide)).trans
            ((doneA.sp.trans (hp.stacks.trans doneB.sp.symm)).trans
              (preparedB.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide) (by decide)).symm)
          have initMatrices := (doneA.frame_word hp.left.initializing.space 232 (by decide) (Or.inr (by decide))).trans
            (hp.matrices.trans (doneB.frame_word hp.right.initializing.space 232 (by decide) (Or.inr (by decide))).symm)
          have matrices := preparedA.matrix.trans (initMatrices.trans preparedB.matrix.symm)
          have initOutputs := (doneA.frame_word hp.left.initializing.space 256 (by decide) (Or.inr (by decide))).trans
            (hp.outputs.trans (doneB.frame_word hp.right.initializing.space 256 (by decide) (Or.inr (by decide))).symm)
          have outputs := (preparedA.words 256 (by decide) (by decide)).trans
            (initOutputs.trans (preparedB.words 256 (by decide) (by decide)).symm)
          have initWorks := (doneA.frame_word hp.left.initializing.space 248 (by decide) (Or.inr (by decide))).trans
            (hp.works.trans (doneB.frame_word hp.right.initializing.space 248 (by decide) (Or.inr (by decide))).symm)
          have works := (preparedA.words 248 (by decide) (by decide)).trans
            (initWorks.trans (preparedB.words 248 (by decide) (by decide)).symm)
          have related : FillFinish.Related p (VG.Proof.Argon2.X86_64.InitFill.initial p s) (VG.Proof.Argon2.X86_64.InitFill.initial p t) _ _ :=
            ⟨preparedA.finish_ready (initialized_setup hp.left doneA) (initialized_output hp.left doneA) hp.left.positive,
              preparedB.finish_ready (initialized_setup hp.right doneB) (initialized_output hp.right doneB) hp.right.positive,
              preparedBases, preparedStacks, matrices, outputs, works,
              preparedA.represents (initialized_setup hp.left doneA) _ (initialized_represents hp.left doneA),
              preparedB.represents (initialized_setup hp.right doneB) _ (initialized_represents hp.right doneB), hp.indices⟩
          obtain ⟨fillTrace, _⟩ := FillFinish.code_rel v name p (VG.Proof.Argon2.X86_64.InitFill.initial p s) (VG.Proof.Argon2.X86_64.InitFill.initial p t) _ _ _ _ _ _ related fillA fillB
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
  left : VG.Proof.Argon2.X86_64.InitialBody.Ready p s
  right : VG.Proof.Argon2.X86_64.InitialBody.Ready p t
  hashing : Initial.Related s t
  matrices : FillKernel.matrix s = FillKernel.matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  indices : (Proof.Argon2.iterations p 0 p.passes (VG.Proof.Argon2.X86_64.InitialBody.initial p s)).indices =
    (Proof.Argon2.iterations p 0 p.passes (VG.Proof.Argon2.X86_64.InitialBody.initial p t)).indices

theorem code_rel [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) (p : Params) :
    RelCT isa (VG.Proof.Argon2.X86_64.InitialBody.Related p) (Impl.Argon2.X86_64.InitialBody.code name (HPrime.hash v)) (fun _ _ => True) := by
  have hashed := ((Initial.code_rel v).mono (P' := VG.Proof.Argon2.X86_64.InitialBody.Related p) (fun _ _ h => h.hashing)
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨Initial.initialHash_ok v s h.left.hashSpace h.left.inputs p h.left.header,
        Initial.initialHash_ok v t h.right.hashSpace h.right.inputs p h.right.header⟩)
  refine hashed.seq ((InitFill.code_rel v name p).mono ?_ (fun _ _ h => h))
  rintro a b ⟨_, s, t, hp, ⟨da, ha⟩, ⟨db, hb⟩⟩
  have baseA : FillKernel.matrix a = FillKernel.matrix s := ha.frame_word hp.left.hashSpace 232 (by decide) (by decide)
  have baseB : FillKernel.matrix b = FillKernel.matrix t := hb.frame_word hp.right.hashSpace 232 (by decide) (by decide)
  have outputA : FinalOutput.output a = FinalOutput.output s := ha.frame_word hp.left.hashSpace 256 (by decide) (by decide)
  have outputB : FinalOutput.output b = FinalOutput.output t := hb.frame_word hp.right.hashSpace 256 (by decide) (by decide)
  have workA : FinalOutput.work a = FinalOutput.work s := ha.frame_word hp.left.hashSpace 248 (by decide) (by decide)
  have workB : FinalOutput.work b = FinalOutput.work t := hb.frame_word hp.right.hashSpace 248 (by decide) (by decide)
  refine ⟨VG.Proof.Argon2.X86_64.InitialBody.hashed_ready hp.left.filling hp.left.hashSpace ha, VG.Proof.Argon2.X86_64.InitialBody.hashed_ready hp.right.filling hp.right.hashSpace hb,
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
  left : VG.Proof.Argon2.X86_64.InitialBody.Ready p s
  right : VG.Proof.Argon2.X86_64.InitialBody.Ready p t
  hashing : Initial.Related s t
  matrices : FillKernel.matrix s = FillKernel.matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  references : VG.Proof.Argon2.X86_64.InitialBody.references p s = VG.Proof.Argon2.X86_64.InitialBody.references p t

theorem ReviewedRelated.related {p : Params} {s t : State} (h : VG.Proof.Argon2.X86_64.InitialBody.ReviewedRelated p s t) : VG.Proof.Argon2.X86_64.InitialBody.Related p s t := by
  refine ⟨h.left, h.right, h.hashing, h.matrices, h.outputs, h.works, ?_⟩
  have parameters := h.left.filling.environment.parameters
  have positive : 0 < p.laneLen := by
    have segments := Proof.Argon2.laneLen_segments p parameters.lanesPositive
    have minimum := parameters.segment_bound.1
    omega
  have indices := Proof.Argon2.references_injective p positive _ _ _ _ _ _ _ _ h.references
  unfold VG.Proof.Argon2.X86_64.InitialBody.initial
  rw [Proof.Argon2.iterations_fill, Proof.Argon2.iterations_fill]
  exact indices

theorem reviewed_rel [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) (p : Params) :
    RelCT isa (VG.Proof.Argon2.X86_64.InitialBody.ReviewedRelated p) (Impl.Argon2.X86_64.InitialBody.code name (HPrime.hash v)) (fun _ _ => True) :=
  (VG.Proof.Argon2.X86_64.InitialBody.code_rel v name p).mono (fun _ _ h => h.related) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.InitialBody
end

/-! Preserve precisely the reviewed leakage relation across parameter computation. -/

namespace VG.Proof.Argon2.X86_64.InitialBody

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64.Initial

theorem ReviewedRelated.of_state {s₁ s₂ t₁ t₂ : State} {p : Params}
    (h : VG.Proof.Argon2.X86_64.InitialBody.ReviewedRelated p s₁ s₂) (k₁ : VG.Proof.Argon2.X86_64.InitialBody.SameFrame s₁ t₁) (k₂ : VG.Proof.Argon2.X86_64.InitialBody.SameFrame s₂ t₂)
    (length₁ : t₁.gpr .r13 = BitVec.ofNat 64 p.laneLen)
    (length₂ : t₂.gpr .r13 = BitVec.ofNat 64 p.laneLen) : VG.Proof.Argon2.X86_64.InitialBody.ReviewedRelated p t₁ t₂ := by
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

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.DeriveVerified`. -/
section

section

/-! The complete derivation does not directly write the stack pointer for every BLAKE2b backend. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

local notation "property" => (fun i => !isa.writesSp i)

theorem initial_spSafe (v : Proof.Blake2.X86_64.Backend) :
    (Impl.Argon2.X86_64.Initial.code (HPrime.hash v)).all property = true := by
  have init : (HPrime.hash v).init.all property = true := by
    change (Impl.Blake2.X86_64.Stream.init Spec.Blake2.b).all _ = true
    lit_decide
  have update : (HPrime.hash v).update.all property = true := v.updateSpSafe
  have finalize : (HPrime.hash v).finalize.all property = true := v.finalizeSpSafe
  simp only [Impl.Argon2.X86_64.Initial.code, Impl.Argon2.X86_64.Initial.start,
    Impl.Argon2.X86_64.Initial.absorb, Impl.Argon2.X86_64.Initial.finish,
    Impl.Argon2.X86_64.HPrime.init, Impl.Argon2.X86_64.HPrime.absorbFixed,
    Impl.Argon2.X86_64.HPrime.update, Impl.Argon2.X86_64.HPrime.finalize, Code.all]
  rw [init, update, finalize]
  lit_decide

theorem memory_spSafe (v : Proof.Blake2.X86_64.Backend) (name : String) :
    (Impl.Argon2.X86_64.MemoryInit.code name (HPrime.hash v)).all property = true := by
  simp only [Impl.Argon2.X86_64.MemoryInit.code, Impl.Argon2.X86_64.MemoryInit.clear,
    Impl.Argon2.X86_64.MemoryInit.lane, Impl.Argon2.X86_64.MemoryInit.block, Code.all]
  rw [HPrime.spSafe v]
  lit_decide

theorem frame_spSafe (body : Prog isa) (rs : List Reg) (h : body.all property = true)
    (safe : ∀ r ∈ rs, r ≠ .rsp) :
    (Impl.Argon2.X86_64.Derive.frame body rs).all property = true := by
  induction rs with
  | nil =>
    change (true && body.all property && true) = true
    rw [h]; rfl
  | cons r rs ih =>
    change (true && (Impl.Argon2.X86_64.Derive.frame body rs).all property && property (.pop r 1)) = true
    rw [ih (fun q hq => safe q (List.mem_cons_of_mem _ hq))]
    simp only [Bool.true_and]
    change Bool.not ((some r == some Reg.rsp) : Bool) = true
    rw [Bool.not_eq_true', beq_eq_false_iff_ne]
    exact fun eq => safe r (List.mem_cons_self ..) (Option.some.inj eq)

/-- The filling passes, whose calls of G are `CompressImpl.spSafe`. -/
theorem fill_spSafe [CompressImpl] : Impl.Argon2.X86_64.FillIterations.loop.all property = true := by
  simp only [Impl.Argon2.X86_64.FillIterations.loop, Impl.Argon2.X86_64.FillIterations.body,
    Impl.Argon2.X86_64.FillIteration.code, Impl.Argon2.X86_64.FillSlices.loop,
    Impl.Argon2.X86_64.FillSlices.body, Impl.Argon2.X86_64.FillSlice.code,
    Impl.Argon2.X86_64.FillLanes.loop, Impl.Argon2.X86_64.FillLanes.body,
    Impl.Argon2.X86_64.SegmentSetup.code, Impl.Argon2.X86_64.FillSegment.loop,
    Impl.Argon2.X86_64.FillSegment.body, Impl.Argon2.X86_64.FillBlock.code,
    Impl.Argon2.X86_64.RandomSource.code, Impl.Argon2.X86_64.AddressCache.code,
    Impl.Argon2.X86_64.AddressCache.select, Impl.Argon2.X86_64.AddressCalls.code,
    Impl.Argon2.X86_64.AddressCalls.calls, Impl.Argon2.X86_64.AddressCalls.stage,
    Impl.Argon2.X86_64.FillKernel.code, Impl.Argon2.X86_64.FillCompress.code,
    Impl.Argon2.X86_64.FillCompress.operation, Code.all]
  rw [compressor_spSafe]
  lit_decide

theorem code_spSafe [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) :
    (Impl.Argon2.X86_64.Derive.code name (HPrime.hash v)).all property = true := by
  unfold Impl.Argon2.X86_64.Derive.code
  apply VG.Proof.Argon2.X86_64.Derive.frame_spSafe (safe := by decide)
  simp only [Impl.Argon2.X86_64.Derive.body, Impl.Argon2.X86_64.InitialBody.code,
    Impl.Argon2.X86_64.InitFill.code, Impl.Argon2.X86_64.FillFinish.code,
    Impl.Argon2.X86_64.Finish.code, Impl.Argon2.X86_64.FinalOutput.code, Code.all]
  rw [VG.Proof.Argon2.X86_64.Derive.initial_spSafe v, VG.Proof.Argon2.X86_64.Derive.memory_spSafe v name, HPrime.spSafe v, VG.Proof.Argon2.X86_64.Derive.fill_spSafe]
  lit_decide

end VG.Proof.Argon2.X86_64.Derive

end

/-! Merged from `Proof.Argon2.X86_64.ParametersCT`. -/
section
/-! Rounded-memory computation has a fixed trace, reading only public frame addresses. -/

namespace VG.Proof.Argon2.X86_64.Parameters

open VG VG.X86_64

theorem code_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    Impl.Argon2.X86_64.Parameters.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

end VG.Proof.Argon2.X86_64.Parameters
end

/-! Merged from `Proof.Argon2.X86_64.DeriveWords`. -/
section
/-! Exact words consumed by hashing, initialization, filling, and finalization. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64
open VG.Proof.Argon2.X86_64.Initial (wordAt)

theorem params_variant_code (kind passes memory lanes tagLen : Nat) (bound : kind ≤ 2) :
    (Spec.Argon2.params kind passes memory lanes tagLen).variant.code = kind := by
  by_cases zero : kind = 0
  · subst kind; rfl
  · by_cases one : kind = 1
    · subst kind; rfl
    · have two : kind = 2 := by omega
      subst kind; rfl

structure DeriveWords (s t : State) : Prop where
  passes : wordAt t 72 = BitVec.ofNat 64 (abiParams s).passes
  saltLength : wordAt t 80 = s.gpr .r8
  salt : wordAt t 88 = s.gpr .rcx
  passwordLength : wordAt t 96 = s.gpr .rdx
  password : wordAt t 104 = s.gpr .rsi
  kind : wordAt t 112 = BitVec.ofNat 64 (abiParams s).variant.code
  memory : wordAt t 176 = BitVec.ofNat 64 (abiParams s).memory
  lanes : wordAt t 184 = BitVec.ofNat 64 (abiParams s).lanes
  secret : wordAt t 200 = abiWord s 32
  secretLength : wordAt t 208 = abiWord s 40
  ad : wordAt t 216 = abiWord s 48
  adLength : wordAt t 224 = abiWord s 56
  matrix : wordAt t 232 = abiWord s 64
  blocks : wordAt t 240 = BitVec.ofNat 64 (abiParams s).blocks
  work : wordAt t 248 = abiWord s 80
  output : wordAt t 256 = abiWord s 88
  tagLength : wordAt t 264 = BitVec.ofNat 64 (abiParams s).tagLen

theorem private_words {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : VG.Proof.Argon2.X86_64.Derive.DeriveWords s t := by
  have parameters := private_parameters h prepared
  refine ⟨?_, private_argument_word prepared (80, .r8) (by decide),
    private_argument_word prepared (88, .rcx) (by decide),
    private_argument_word prepared (96, .rdx) (by decide),
    private_argument_word prepared (104, .rsi) (by decide), ?_, parameters.memoryWord, parameters.lanesWord,
    private_stack_word h prepared 3 (by decide), private_stack_word h prepared 4 (by decide),
    private_stack_word h prepared 5 (by decide), private_stack_word h prepared 6 (by decide),
    private_stack_word h prepared 7 (by decide), ?_, private_stack_word h prepared 9 (by decide),
    private_stack_word h prepared 10 (by decide), ?_⟩
  · have word := private_argument_word prepared (72, .r9) (by decide)
    change wordAt t 72 = ((s.gpr .r9).setWidth 32).setWidth 64 at word
    change wordAt t 72 = BitVec.ofNat 64 ((s.gpr .r9).setWidth 32).toNat
    rw [word, BitVec.ofNat_toNat]
  · have code := VG.Proof.Argon2.X86_64.Derive.params_variant_code ((s.gpr .rdi).setWidth 32).toNat
      (abiParams s).passes (abiParams s).memory (abiParams s).lanes (abiParams s).tagLen h.kind
    change (abiParams s).variant.code = ((s.gpr .rdi).setWidth 32).toNat at code
    rw [code]
    have word := private_argument_word prepared (112, .rdi) (by decide)
    change wordAt t 112 = ((s.gpr .rdi).setWidth 32).setWidth 64 at word
    rw [word, BitVec.ofNat_toNat]
  · have word := private_stack_word h prepared 8 (by decide)
    change wordAt t 240 = abiWord s 72 at word
    rw [word, ← h.blocks, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · have word := private_stack_word h prepared 11 (by decide)
    change wordAt t 264 = abiWord s 96 at word
    change wordAt t 264 = BitVec.ofNat 64 (abiWord s 96).toNat
    rw [word, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveSeparation`. -/
section
/-! Buffer separation is supplied by the shared signature, including read-only arguments. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure AbiSeparation (s : State) : Prop where
  inputWork : ∀ r ∈ abiInputs s, r.Disjoint (abiWork s)
  matrixWork : (abiMatrix s).Disjoint (abiWork s)
  outputWork : (abiOutput s).Disjoint (abiWork s)
  matrixOutput : (abiMatrix s).Disjoint (abiOutput s)

theorem abi_separation {s : State} (h : AbiEnvironment s) : VG.Proof.Argon2.X86_64.Derive.AbiSeparation s := by
  have pairs := h.pairs
  sig_eval [abiBuffers, abiInputs, abiMatrix, abiWork, abiOutput, abiArguments] at pairs
  sig_split pairs
  constructor
  all_goals sig_eval [abiInputs, abiMatrix, abiWork, abiOutput]
  all_goals sig_and_intros
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›

theorem private_scratch {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : t.gpr .rbx = (abiWork s).base := by
  have word := prologue_word h 9 (by decide)
  change (prologueState s).mem.readW ((prologueState s).gpr .rsp + 400) 64 = abiWord s 80 at word
  exact prepared.scratch.trans word

theorem abi_input_lengths {s : State} (h : AbiEnvironment s) : ∀ r ∈ abiInputs s, r.len < 2 ^ 32 := by
  have valid := h.valid
  unfold Spec.Argon2.valid at valid
  obtain ⟨_, _, _, _, _, _, _, _, password, salt, secret, ad⟩ := valid
  sig_eval [abiInputs]
  sig_and_intros
  all_goals with_reducible assumption

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveParameters`. -/
section
/-! Compute the rounded lane length before entering the complete Argon2 body. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64.Initial

/-- A specification state for the body's readiness predicate, not executable code. -/
def dimensionState (s : State) (p : Params) : State :=
  s.setReg .r13 (BitVec.ofNat 64 p.laneLen)

theorem dimension_frame (s : State) (p : Params) : InitialBody.SameFrame s (VG.Proof.Argon2.X86_64.Derive.dimensionState s p) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact RegUpd.gpr_setReg_of_ne _ _ (by decide)
  · exact RegUpd.gpr_setReg_of_ne _ _ (by decide)
  · exact RegUpd.gpr_setReg_of_ne _ _ (by decide)
  · exact RegUpd.mem_setReg ..
  · exact RegUpd.rd_setReg ..
  · exact RegUpd.wr_setReg ..

theorem parameters_frame {s t : State} (p : Params)
    (keeps : Divide.Keeps Parameters.changed s t) :
    InitialBody.SameFrame (VG.Proof.Argon2.X86_64.Derive.dimensionState s p) t := by
  have frame := VG.Proof.Argon2.X86_64.Derive.dimension_frame s p
  refine ⟨?_, ?_, ?_, keeps.mem.trans frame.mem.symm,
    keeps.rd.trans frame.rd.symm, keeps.wr.trans frame.wr.symm⟩
  · exact (keeps.regs .rbp (by decide)).trans frame.bp.symm
  · exact (keeps.regs .rbx (by decide)).trans frame.bx.symm
  · exact (keeps.regs .rsp (by decide)).trans frame.sp.symm

theorem parameters_ready {s t : State} {p : Params}
    (h : InitialBody.Ready p (VG.Proof.Argon2.X86_64.Derive.dimensionState s p))
    (length : t.gpr .r13 = BitVec.ofNat 64 p.laneLen)
    (keeps : Divide.Keeps Parameters.changed s t) : InitialBody.Ready p t :=
  h.of_state (VG.Proof.Argon2.X86_64.Derive.parameters_frame p keeps) length

theorem parameters_body_ok [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s : State) (p : Params) (parameters : Parameters.Ready p s)
    (body : InitialBody.Ready p (VG.Proof.Argon2.X86_64.Derive.dimensionState s p)) :
    WP isa (.seq Impl.Argon2.X86_64.Parameters.code
      (Impl.Argon2.X86_64.InitialBody.code name (HPrime.hash v))) s (InitialBody.Done s · p) := by
  refine WP.seq ((Parameters.code_ok s p parameters).mono ?_)
  rintro a ⟨length, keeps⟩
  refine (InitialBody.code_ok v name a p (VG.Proof.Argon2.X86_64.Derive.parameters_ready body length keeps)).mono ?_
  intro t done
  have bp := keeps.regs .rbp (by decide)
  have sp := keeps.regs .rsp (by decide)
  have base : FillKernel.matrix a = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : FinalOutput.work a = FinalOutput.work s := by
    unfold FinalOutput.work; rw [keeps.mem, bp]
  have output : FinalOutput.output a = FinalOutput.output s := by
    unfold FinalOutput.output; rw [keeps.mem, bp]
  refine ⟨?_, done.bp.trans bp, done.sp.trans sp,
    done.rd.trans keeps.rd, done.wr.trans keeps.wr, ?_⟩
  · have digest := done.digest
    simp only [Initial.inputBytes, Initial.wordAt, keeps.mem, bp, output] at digest
    exact digest
  · have frame := done.frame
    rw [InitFill.writes_eq s a p bp sp base work output] at frame
    rw [keeps.mem] at frame
    exact frame

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveInputBytes`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveMemorySpace`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveHashSpace`. -/
section
/-! Permissions for H₀ follow from the signature and the private ABI frame. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_hash_space {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : Initial.Space t := by
  have scratch := VG.Proof.Argon2.X86_64.Derive.private_scratch h prepared
  have member : (abiWork s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  refine ⟨?_, ?_, ?_, private_frame_stack prepared 16 (by decide), ?_,
    by simpa only [BitVec.add_zero] using private_local_write prepared 0 64 (by decide)⟩
  · rw [scratch]; exact private_work_member h prepared
  · rw [scratch]; exact private_stack_disjoint h prepared (abiWork s, true) member 16 (by decide)
  · rw [scratch]; exact private_frame_disjoint h prepared (abiWork s, true) member
  · intro d hd
    have bounds : ∀ d ∈ Initial.slots, d + 8 ≤ 272 := by decide
    exact private_local_read prepared d 8 (bounds d hd)

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveHashInputs`. -/
section
/-! All four secret inputs keep their original pointers and lengths in the private frame. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64
open VG.Proof.Argon2.X86_64.Initial (wordAt inputRegion)

theorem private_input_member {s t : State} (words : VG.Proof.Argon2.X86_64.Derive.DeriveWords s t) (input : Nat × Nat)
    (member : input ∈ Initial.inputs) : inputRegion t input.1 input.2 ∈ abiInputs s := by
  simp only [Initial.inputs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · change (⟨wordAt t 104, (wordAt t 96).toNat⟩ : Region) ∈ abiInputs s
    rw [words.password, words.passwordLength]
    exact List.mem_cons_self ..
  · change (⟨wordAt t 88, (wordAt t 80).toNat⟩ : Region) ∈ abiInputs s
    rw [words.salt, words.saltLength]
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · change (⟨wordAt t 200, (wordAt t 208).toNat⟩ : Region) ∈ abiInputs s
    rw [words.secret, words.secretLength]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · change (⟨wordAt t 216, (wordAt t 224).toNat⟩ : Region) ∈ abiInputs s
    rw [words.ad, words.adLength]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

theorem private_hash_inputs {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    ∀ input ∈ Initial.inputs, Initial.InputReady t input.1 input.2 := by
  have words := VG.Proof.Argon2.X86_64.Derive.private_words h prepared
  have space := VG.Proof.Argon2.X86_64.Derive.private_hash_space h prepared
  have separation := VG.Proof.Argon2.X86_64.Derive.abi_separation h
  have scratch := VG.Proof.Argon2.X86_64.Derive.private_scratch h prepared
  intro input hi
  have region := VG.Proof.Argon2.X86_64.Derive.private_input_member words input hi
  have facts : ∀ input ∈ Initial.inputs, input.1 ∈ Initial.slots ∧ input.2 ∈ Initial.slots ∧
      input.1 + 8 ≤ 272 ∧ input.2 + 8 ≤ 272 := by decide
  obtain ⟨pointerSlot, lengthSlot, pointerBound, lengthBound⟩ := facts input hi
  have buffer : (inputRegion t input.1 input.2, false) ∈ abiBuffers s ++ [(abiArguments s, false)] :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, region, rfl⟩))
  refine ⟨space, pointerSlot, lengthSlot, pointerBound, lengthBound,
    VG.Proof.Argon2.X86_64.Derive.abi_input_lengths h _ region, ?_, ?_, ?_⟩
  · intro p n ⟨r, hr, hc⟩
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨_, List.mem_append_left _ ?_, hc⟩
    rw [prepared.rd]
    change inputRegion t input.1 input.2 ∈ (frameStart s Impl.Argon2.X86_64.Derive.saved).rd
    rw [frameStart_rd, h.rd]
    exact List.mem_append_left _ region
  · rw [scratch]; exact separation.inputWork _ region
  · exact (private_stack_disjoint h prepared (inputRegion t input.1 input.2, false) buffer 16 (by decide)).symm

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveAllocations`. -/
section
/-! The exact matrix and output allocations of the signature remain writable. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_matrix_region {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    (⟨FillKernel.matrix t, (abiParams s).blocks * 1024⟩ : Region) = abiMatrix s := by
  have words := VG.Proof.Argon2.X86_64.Derive.private_words h prepared
  change (⟨Initial.wordAt t 232, (abiParams s).blocks * 1024⟩ : Region) = abiMatrix s
  rw [words.matrix, ← h.blocks]; rfl

theorem private_local_cover {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (n : Nat) (bound : n ≤ 272) : Covers [⟨t.gpr .rbp, n⟩] t.wr := by
  intro p k ⟨region, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst region
  refine ⟨⟨t.gpr .rbp, 272⟩, ?_, ?_⟩
  · rw [prepared.wr, prepared.bp]
    exact frameStart_locals s _
  · unfold Region.Contains at hc ⊢
    exact Nat.le_trans hc bound

theorem private_matrix_cover {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    Covers [⟨FillKernel.matrix t, (abiParams s).blocks * 1024⟩] t.wr := by
  have words := VG.Proof.Argon2.X86_64.Derive.private_words h prepared
  have member : abiMatrix s ∈ t.wr := private_wr_member prepared _ (by rw [h.wr]; exact List.mem_cons_self ..)
  have matrix : (⟨FillKernel.matrix t, (abiParams s).blocks * 1024⟩ : Region) = abiMatrix s := by
    change (⟨Initial.wordAt t 232, (abiParams s).blocks * 1024⟩ : Region) = abiMatrix s
    rw [words.matrix, ← h.blocks]; rfl
  intro p n ⟨region, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst region
  exact ⟨abiMatrix s, member, matrix ▸ hc⟩

theorem private_output_cover {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    Covers [⟨FinalOutput.output t, (abiParams s).tagLen⟩] t.wr := by
  have words := VG.Proof.Argon2.X86_64.Derive.private_words h prepared
  have member : abiOutput s ∈ t.wr := private_wr_member prepared _ (by
    rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have output : (⟨FinalOutput.output t, (abiParams s).tagLen⟩ : Region) = abiOutput s := by
    change (⟨Initial.wordAt t 256, (abiParams s).tagLen⟩ : Region) = abiOutput s
    rw [words.output]; rfl
  intro p n ⟨region, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst region
  exact ⟨abiOutput s, member, output ▸ hc⟩

theorem private_work_cover {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (n : Nat) (bound : n ≤ 16384) :
    Covers [⟨FinalOutput.work t, n⟩] t.wr := by
  have words := VG.Proof.Argon2.X86_64.Derive.private_words h prepared
  intro p k ⟨region, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst region
  refine ⟨abiWork s, private_work_member h prepared, ?_⟩
  change Region.Contains ⟨abiWord s 80, 16384⟩ p k
  have pointer : FinalOutput.work t = abiWord s 80 := words.work
  rw [pointer] at hc
  unfold Region.Contains at hc ⊢
  exact Nat.le_trans hc bound

end VG.Proof.Argon2.X86_64.Derive
end

/-! The signature's rounded block allocation supplies all initialization permissions. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_matrix_bytes {s : State} (h : AbiEnvironment s) :
    1024 * ((abiParams s).lanes * (abiParams s).laneLen) = (abiParams s).blocks * 1024 := by
  rw [← Proof.Argon2.blocks_lanes (abiParams s) h.valid.1, Nat.mul_comm]

theorem private_memory_space {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    MemoryInit.Space t (FillKernel.matrix t)
      (1024 * ((abiParams s).lanes * (abiParams s).laneLen)) := by
  have matrix := VG.Proof.Argon2.X86_64.Derive.private_matrix_region h prepared
  have separation := VG.Proof.Argon2.X86_64.Derive.abi_separation h
  have scratch := VG.Proof.Argon2.X86_64.Derive.private_scratch h prepared
  have matrixMember : (abiMatrix s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  have workMember : (abiWork s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  rw [VG.Proof.Argon2.X86_64.Derive.private_matrix_bytes h]
  refine ⟨VG.Proof.Argon2.X86_64.Derive.private_matrix_cover h prepared, VG.Proof.Argon2.X86_64.Derive.private_local_cover prepared 72 (by decide), ?_,
    ?_, ?_, ?_, (private_frame_stack prepared 24 (by decide)).symm, ?_, ?_, ?_⟩
  · rw [scratch]; exact private_work_member h prepared
  · rw [matrix]; exact private_frame_disjoint h prepared (abiMatrix s, true) matrixMember
  · rw [scratch]; exact private_frame_disjoint h prepared (abiWork s, true) workMember
  · rw [matrix, scratch]; exact separation.matrixWork
  · rw [matrix]; exact private_stack_disjoint h prepared (abiMatrix s, true) matrixMember 24 (by decide)
  · rw [scratch]; exact private_stack_disjoint h prepared (abiWork s, true) workMember 24 (by decide)
  · have blocks := Proof.Argon2.blocks_le_memory (abiParams s)
    have memoryBound := h.valid.2.2.2.2.2.1
    omega

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveHeader`. -/
section
/-! H₀ hashes the original requested memory cost and the exact reviewed parameters. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_header {s t : State} (words : VG.Proof.Argon2.X86_64.Derive.DeriveWords s t) :
    Initial.headerBytes t = Proof.Argon2.initialHeader (abiParams s) := by
  have headerWords : (List.range 6).map (Initial.headerValue t) =
      [BitVec.ofNat 32 (abiParams s).lanes, BitVec.ofNat 32 (abiParams s).tagLen,
        BitVec.ofNat 32 (abiParams s).memory, BitVec.ofNat 32 (abiParams s).passes,
        19#32, BitVec.ofNat 32 (abiParams s).variant.code] := by
    change [(Initial.wordAt t 184).setWidth 32, (Initial.wordAt t 264).setWidth 32,
      (Initial.wordAt t 176).setWidth 32, (Initial.wordAt t 72).setWidth 32, 19#32,
      (Initial.wordAt t 112).setWidth 32] = _
    rw [words.lanes, words.tagLength, words.memory, words.passes, words.kind]
    simp only [BitVec.setWidth_ofNat_of_le (show 32 ≤ 64 by decide)]
  unfold Initial.headerBytes
  rw [← List.flatMap_map, headerWords]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ← List.append_assoc,
    Proof.Argon2.initialHeader, Spec.Argon2.le32]

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveFinalLayout`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveFillLayout`. -/
section
/-! One reviewed allocation supplies all filling and address-generation ranges. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_fill_layout {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : FillKernel.Layout (abiParams s) t := by
  have space := VG.Proof.Argon2.X86_64.Derive.private_memory_space h prepared
  rw [VG.Proof.Argon2.X86_64.Derive.private_matrix_bytes h] at space
  refine ⟨?_, private_local_write prepared 16 8 (by decide), space.matrix,
    VG.Proof.Argon2.X86_64.Derive.private_work_cover h prepared 5120 (by decide), ?_, space.frameMatrix.symm, ?_, ?_,
    private_frame_stack prepared 8 (by decide), ?_⟩
  · intro d hd
    have bounds : ∀ d ∈ [0, 16, 184, 232, 248], d + 8 ≤ 272 := by decide
    exact private_local_read prepared d 8 (bounds d hd)
  · have pointer : t.gpr .rbx = FillKernel.work t := by
      rw [VG.Proof.Argon2.X86_64.Derive.private_scratch h prepared]; exact (VG.Proof.Argon2.X86_64.Derive.private_words h prepared).work.symm
    rw [← pointer]
    exact space.matrixWork.sub_right (Region.sub_prefix (by decide))
  · exact (space.stackMatrix.sub_left (below_sub (by decide) (by decide))).symm
  · have pointer : t.gpr .rbx = FillKernel.work t := by
      rw [VG.Proof.Argon2.X86_64.Derive.private_scratch h prepared]; exact (VG.Proof.Argon2.X86_64.Derive.private_words h prepared).work.symm
    rw [← pointer]
    exact space.frameWork.sub_right (Region.sub_prefix (by decide))
  · have pointer : t.gpr .rbx = FillKernel.work t := by
      rw [VG.Proof.Argon2.X86_64.Derive.private_scratch h prepared]; exact (VG.Proof.Argon2.X86_64.Derive.private_words h prepared).work.symm
    rw [← pointer]
    exact (space.stackWork.sub_left (below_sub (by decide) (by decide))).sub_right
      (Region.sub_prefix (by decide))

theorem private_address_layout {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : AddressCalls.Ready t := by
  have space := VG.Proof.Argon2.X86_64.Derive.private_memory_space h prepared
  have pointer : t.gpr .rbx = AddressCalls.work t := by
    rw [VG.Proof.Argon2.X86_64.Derive.private_scratch h prepared]; exact (VG.Proof.Argon2.X86_64.Derive.private_words h prepared).work.symm
  refine ⟨private_local_read prepared 248 8 (by decide), VG.Proof.Argon2.X86_64.Derive.private_work_cover h prepared 8192 (by decide),
    ?_, private_frame_stack prepared 8 (by decide), ?_⟩
  · rw [← pointer]; exact space.frameWork.sub_right (Region.sub_prefix (by decide))
  · rw [← pointer]
    exact (space.stackWork.sub_left (below_sub (by decide) (by decide))).sub_right (Region.sub_prefix (by decide))

theorem private_fill_environment {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : FillSetup.Environment (abiParams s) t := by
  have space := VG.Proof.Argon2.X86_64.Derive.private_memory_space h prepared
  have words := VG.Proof.Argon2.X86_64.Derive.private_words h prepared
  have pointer : t.gpr .rbx = AddressCalls.work t := by
    rw [VG.Proof.Argon2.X86_64.Derive.private_scratch h prepared]; exact words.work.symm
  rw [VG.Proof.Argon2.X86_64.Derive.private_matrix_bytes h] at space
  refine ⟨?_, h.valid.2.2.2.1, VG.Proof.Argon2.X86_64.Derive.private_fill_layout h prepared, VG.Proof.Argon2.X86_64.Derive.private_address_layout h prepared, ?_,
    private_local_write prepared 8 8 (by decide), private_local_write prepared 0 8 (by decide),
    ?_, words.blocks, words.passes, words.kind, words.lanes⟩
  · refine ⟨h.valid.1, Nat.lt_trans h.valid.2.1 (by decide), h.valid.2.2.2.2.1,
      h.valid.2.2.2.2.2.1, by decide, h.valid.1, by decide⟩
  · intro d hd
    have bounds : ∀ d ∈ [0, 8, 72, 112, 240], d + 8 ≤ 272 := by decide
    exact private_local_read prepared d 8 (bounds d hd)
  · rw [← pointer]; exact space.matrixWork.sub_right (Region.sub_prefix (by decide))

end VG.Proof.Argon2.X86_64.Derive
end

/-! Final lane reduction and H′ use the matrix and disjoint output/scratch allocations. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_final_layout {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : FinalOutput.Ready (abiParams s) t := by
  have words := VG.Proof.Argon2.X86_64.Derive.private_words h prepared
  have separation := VG.Proof.Argon2.X86_64.Derive.abi_separation h
  have environment := VG.Proof.Argon2.X86_64.Derive.private_fill_environment h prepared
  have parameters := environment.parameters
  have blocks := Proof.Argon2.lastIndex_bounds (abiParams s) parameters.lanesPositive
    parameters.segment_bound.1 0 parameters.lanesPositive
  have minimum : 1024 ≤ (abiParams s).blocks * 1024 := by
    have positive : 1 ≤ (abiParams s).blocks := by omega
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right 1024 positive
  have matrix := VG.Proof.Argon2.X86_64.Derive.private_matrix_region h prepared
  have work : FinalOutput.work t = (abiWork s).base := words.work
  have output : (⟨FinalOutput.output t, (abiParams s).tagLen⟩ : Region) = abiOutput s := by
    change (⟨Initial.wordAt t 256, (abiParams s).tagLen⟩ : Region) = abiOutput s
    rw [words.output]; rfl
  have matrixMember : (abiMatrix s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  have workMember : (abiWork s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  have outputMember : (abiOutput s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  have matrixWork : (⟨ReductionState.matrix t, 1024⟩ : Region).Disjoint ⟨FinalOutput.work t, 16384⟩ := by
    rw [work]
    apply Region.Disjoint.sub_left separation.matrixWork
    rw [← matrix]
    exact Region.sub_prefix minimum
  have stackMatrix : (below (t.gpr .rsp) 24).Disjoint ⟨ReductionState.matrix t, 1024⟩ := by
    apply Region.Disjoint.sub_right
      (private_stack_disjoint h prepared (abiMatrix s, true) matrixMember 24 (by decide))
    rw [← matrix]; exact Region.sub_prefix minimum
  refine ⟨by have tag := h.valid.2.2.2.2.2.2.1; omega, h.valid.2.2.2.2.2.2.2.1,
    ?_, words.tagLength, ?_, VG.Proof.Argon2.X86_64.Derive.private_output_cover h prepared, ?_, matrixWork, ?_, stackMatrix, ?_, ?_⟩
  · intro d hd
    have bounds : ∀ d ∈ [232, 256, 264, 248], d + 8 ≤ 272 := by decide
    exact private_local_read prepared d 8 (bounds d hd)
  · intro p n ⟨region, member, contains⟩
    simp only [List.mem_singleton] at member; subst region
    have contained : Region.Contains ⟨FillKernel.matrix t, (abiParams s).blocks * 1024⟩ p n := by
      unfold Region.Contains at contains ⊢; exact Nat.le_trans contains minimum
    obtain ⟨r, hr, hc⟩ := VG.Proof.Argon2.X86_64.Derive.private_matrix_cover h prepared p n ⟨_, List.mem_singleton_self _, contained⟩
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · rw [work]; exact private_work_member h prepared
  · rw [output, work]; exact separation.outputWork
  · rw [output]; exact private_stack_disjoint h prepared (abiOutput s, true) outputMember 24 (by decide)
  · rw [work]; exact private_stack_disjoint h prepared (abiWork s, true) workMember 24 (by decide)

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveBodyReady`. -/
section
/-! The shared API contract supplies the complete body's precondition after preparation. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem DeriveWords.of_state {s a b : State} (h : VG.Proof.Argon2.X86_64.Derive.DeriveWords s a) (k : InitialBody.SameFrame a b) :
    VG.Proof.Argon2.X86_64.Derive.DeriveWords s b :=
  ⟨(k.word 72).trans h.passes, (k.word 80).trans h.saltLength, (k.word 88).trans h.salt,
    (k.word 96).trans h.passwordLength, (k.word 104).trans h.password, (k.word 112).trans h.kind,
    (k.word 176).trans h.memory, (k.word 184).trans h.lanes, (k.word 200).trans h.secret,
    (k.word 208).trans h.secretLength, (k.word 216).trans h.ad, (k.word 224).trans h.adLength,
    (k.word 232).trans h.matrix, (k.word 240).trans h.blocks, (k.word 248).trans h.work,
    (k.word 256).trans h.output, (k.word 264).trans h.tagLength⟩

theorem private_body_ready {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    InitialBody.Ready (abiParams s) (VG.Proof.Argon2.X86_64.Derive.dimensionState t (abiParams s)) := by
  let a := VG.Proof.Argon2.X86_64.Derive.dimensionState t (abiParams s)
  have keeps : InitialBody.SameFrame t a := VG.Proof.Argon2.X86_64.Derive.dimension_frame t (abiParams s)
  have words : VG.Proof.Argon2.X86_64.Derive.DeriveWords s a := (VG.Proof.Argon2.X86_64.Derive.private_words h prepared).of_state keeps
  have matrix : FillKernel.matrix a = FillKernel.matrix t := by
    unfold FillKernel.matrix; rw [keeps.mem, keeps.bp]
  have scratch : a.gpr .rbx = FinalOutput.work a := by
    rw [keeps.bx, VG.Proof.Argon2.X86_64.Derive.private_scratch h prepared]
    exact words.work.symm
  refine ⟨keeps.hashSpace (VG.Proof.Argon2.X86_64.Derive.private_hash_space h prepared),
    fun input hi => keeps.input (VG.Proof.Argon2.X86_64.Derive.private_hash_inputs h prepared input hi), VG.Proof.Argon2.X86_64.Derive.private_header words, ?_⟩
  refine ⟨?_, (VG.Proof.Argon2.X86_64.Derive.private_fill_environment h prepared).of_state keeps.bp keeps.sp keeps.mem keeps.rd keeps.wr,
    keeps.output (VG.Proof.Argon2.X86_64.Derive.private_final_layout h prepared), h.valid.2.2.1, scratch⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, words.lanes, ?_, ?_⟩
  · rw [matrix]
    exact (VG.Proof.Argon2.X86_64.Derive.private_memory_space h prepared).same keeps.wr keeps.bp keeps.bx keeps.sp
  · rw [keeps.rd, keeps.wr, keeps.bp]; exact private_local_read prepared 232 8 (by decide)
  · rw [keeps.rd, keeps.wr, keeps.bp]; exact private_local_read prepared 184 8 (by decide)
  · rw [keeps.rd, keeps.wr, keeps.bp]; exact private_local_read prepared 240 8 (by decide)
  · rfl
  · rw [← Proof.Argon2.blocks_lanes (abiParams s) h.valid.1]; exact words.blocks
  · exact RegUpd.gpr_setReg_self ..

theorem private_pipeline_ok [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s t : State) (h : AbiEnvironment s) (prepared : PrivatePrepared (prologueState s) t) :
    WP isa (.seq Impl.Argon2.X86_64.Parameters.code
      (Impl.Argon2.X86_64.InitialBody.code name (HPrime.hash v))) t (InitialBody.Done t · (abiParams s)) :=
  VG.Proof.Argon2.X86_64.Derive.parameters_body_ok v name t (abiParams s) (private_parameters h prepared) (VG.Proof.Argon2.X86_64.Derive.private_body_ready h prepared)

end VG.Proof.Argon2.X86_64.Derive
end

/-! Saving registers and copying arguments leave all original input bytes unchanged. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_prepare_frame {s t : State} (prepared : PrivatePrepared (prologueState s) t) :
    Frame [⟨(prologueState s).gpr .rsp, 272⟩] (prologueState s).mem t.mem := by
  apply prepared.frame.sub
  intro region hr
  simp only [privateWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩

theorem private_prologue_frame {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : Frame [below (s.gpr .rsp) 320] s.mem t.mem := by
  have prologue := frameStart_frame s Impl.Argon2.X86_64.Derive.saved (by decide) (by
    have space := h.stack; change 320 ≤ (s.gpr .rsp).toNat; omega)
  apply prologue.trans
  have preparation := VG.Proof.Argon2.X86_64.Derive.private_prepare_frame prepared
  rw [prologue_sp] at preparation
  exact preparation.sub (by
    intro region hr; simp only [List.mem_singleton] at hr; subst region
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩)

theorem private_input_bytes {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (input : Nat × Nat) (hi : input ∈ Initial.inputs) :
    Initial.inputBytes t input.1 input.2 =
      Spec.Blake2.bytesAt s.mem (Initial.inputRegion t input.1 input.2).base
        (Initial.inputRegion t input.1 input.2).len := by
  have words := VG.Proof.Argon2.X86_64.Derive.private_words h prepared
  have region := VG.Proof.Argon2.X86_64.Derive.private_input_member words input hi
  have buffer : (Initial.inputRegion t input.1 input.2, false) ∈ abiBuffers s ++ [(abiArguments s, false)] :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, region, rfl⟩))
  have disjoint := h.reserved (below (s.gpr .rsp) 344)
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    (Initial.inputRegion t input.1 input.2, false) buffer
  have length := VG.Proof.Argon2.X86_64.Derive.abi_input_lengths h _ region
  apply Proof.Blake2.bytesAt_congr
  intro i hi'
  apply (VG.Proof.Argon2.X86_64.Derive.private_prologue_frame h prepared).bytes (R := Initial.inputRegion t input.1 input.2)
    _ (by omega) hi'
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact (disjoint.sub_left (below_sub (by decide) (by decide))).symm

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveReturn`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveRestore`. -/
section
/-! Reload all saved registers from their unchanged stack slots. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem frameEnd_sp (s : State) (rs : List Reg) :
    (frameEnd s rs).gpr .rsp = s.gpr .rsp + BitVec.ofNat 64 (272 + 8 * rs.length) := by
  induction rs with
  | nil => rw [frameEnd, popped_rsp]; rfl
  | cons r rs ih =>
    rw [frameEnd, popped_rsp, ih, BitVec.add_assoc,
      ← BitVec.ofNat_add]
    exact congrArg (fun n => s.gpr .rsp + BitVec.ofNat 64 n)
      (by simp only [List.length_cons]; omega)

theorem popped_one_reg (s : State) (r : Reg) (notSp : r ≠ .rsp) :
    (popped r 1 s).gpr r = s.mem.readW (s.gpr .rsp) 64 := by
  change ((s.setReg r (s.mem.readW (s.gpr .rsp) 64)).setReg .rsp (s.gpr .rsp + 8)).gpr r = _
  rw [RegUpd.gpr_setReg_of_ne _ _ notSp, RegUpd.gpr_setReg_self]

theorem frameEnd_restore (s : State) (rs : List Reg) (values : Reg → Addr)
    (notSp : .rsp ∉ rs) (distinct : rs.Nodup)
    (words : ∀ j (hj : j < rs.length),
      s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (272 + 8 * rs.length - 8 * (j + 1))) 64 = values rs[j]) :
    ∀ r ∈ rs, (frameEnd s rs).gpr r = values r := by
  induction rs with
  | nil => intro r hr; exact False.elim (List.not_mem_nil hr)
  | cons r rs ih =>
    simp only [List.mem_cons, not_or] at notSp
    have nodup := List.nodup_cons.mp distinct
    have innerWords : ∀ j (hj : j < rs.length),
        s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (272 + 8 * rs.length - 8 * (j + 1))) 64 = values rs[j] := by
      intro j hj
      have word := words (j + 1) (by simp only [List.length_cons]; omega)
      have offset : 272 + 8 * (r :: rs).length - 8 * (j + 1 + 1) =
          272 + 8 * rs.length - 8 * (j + 1) := by
        simp only [List.length_cons]; omega
      rw [offset] at word
      exact word
    have inner := ih notSp.2 nodup.2 innerWords
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · rw [frameEnd, VG.Proof.Argon2.X86_64.Derive.popped_one_reg _ _ (Ne.symm notSp.1), frameEnd_mem, VG.Proof.Argon2.X86_64.Derive.frameEnd_sp]
      have word := words 0 (by simp)
      have offset : 272 + 8 * (x :: rs).length - 8 * (0 + 1) = 272 + 8 * rs.length := by
        simp only [List.length_cons]; omega
      rw [offset] at word
      exact word
    · rw [frameEnd, popped_gpr r 1 (frameEnd s rs) (r' := x) (fun h => notSp.2 (h ▸ hx))
        (fun h => nodup.1 (h ▸ hx))]
      exact inner x hx

theorem frame_restored (s t : State) (rs : List Reg) (notSp : .rsp ∉ rs)
    (distinct : rs.Nodup) (space : 272 + 8 * rs.length ≤ (s.gpr .rsp).toNat)
    (sp : t.gpr .rsp = (frameStart s rs).gpr .rsp)
    (unchanged : ∀ j (_hj : j < rs.length),
      t.mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 =
        (frameStart s rs).mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64) :
    ∀ r ∈ rs, (frameEnd t rs).gpr r = s.gpr r := by
  apply VG.Proof.Argon2.X86_64.Derive.frameEnd_restore t rs s.gpr notSp distinct
  intro j hj
  have offsetBound : 8 * (j + 1) ≤ 272 + 8 * rs.length := by omega
  rw [sp, frameStart_sp, ← Offset.ofNat_sub_ofNat offsetBound, Offset.sub_add_sub_cancel,
    unchanged j hj]
  exact frameStart_word s rs notSp space j hj

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveBodySaved`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveBodyPost`. -/
section
/-! The complete body's digest is the public API postcondition on original input memory. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_done_post {s t u : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (done : InitialBody.Done t u (abiParams s)) :
    (Spec.Argon2.deriveContract X86_64.abi 344).post s u := by
  have words := VG.Proof.Argon2.X86_64.Derive.private_words h prepared
  have password := VG.Proof.Argon2.X86_64.Derive.private_input_bytes h prepared (104, 96) (by decide)
  have salt := VG.Proof.Argon2.X86_64.Derive.private_input_bytes h prepared (88, 80) (by decide)
  have secret := VG.Proof.Argon2.X86_64.Derive.private_input_bytes h prepared (200, 208) (by decide)
  have ad := VG.Proof.Argon2.X86_64.Derive.private_input_bytes h prepared (216, 224) (by decide)
  change Initial.inputBytes t 104 96 =
    Spec.Blake2.bytesAt s.mem (Initial.wordAt t 104) (Initial.wordAt t 96).toNat at password
  change Initial.inputBytes t 88 80 =
    Spec.Blake2.bytesAt s.mem (Initial.wordAt t 88) (Initial.wordAt t 80).toNat at salt
  change Initial.inputBytes t 200 208 =
    Spec.Blake2.bytesAt s.mem (Initial.wordAt t 200) (Initial.wordAt t 208).toNat at secret
  change Initial.inputBytes t 216 224 =
    Spec.Blake2.bytesAt s.mem (Initial.wordAt t 216) (Initial.wordAt t 224).toNat at ad
  rw [words.password, words.passwordLength] at password
  rw [words.salt, words.saltLength] at salt
  rw [words.secret, words.secretLength] at secret
  rw [words.ad, words.adLength] at ad
  have digest := done.digest
  change Spec.Blake2.bytesAt u.mem (Initial.wordAt t 256) (abiParams s).tagLen =
    Spec.Argon2.derive (abiParams s) (Initial.inputBytes t 104 96)
      (Initial.inputBytes t 88 80) (Initial.inputBytes t 200 208) (Initial.inputBytes t 216 224) at digest
  rw [words.output, password, salt, secret, ad] at digest
  sig_post [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop]
  exact digest

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveBodyCorrect`. -/
section
/-! Preparation and the entire algorithm establish the shared API postcondition. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def bodyWrites (s : State) : List Region :=
  [abiMatrix s, abiWork s, abiOutput s, ⟨(prologueState s).gpr .rsp, 272⟩,
    below ((prologueState s).gpr .rsp) 24]

structure BodyDone (s t : State) : Prop where
  post : (Spec.Argon2.deriveContract X86_64.abi 344).post s t
  sp : t.gpr .rsp = (prologueState s).gpr .rsp
  rd : t.rd = (prologueState s).rd
  wr : t.wr = (prologueState s).wr
  frame : Frame (VG.Proof.Argon2.X86_64.Derive.bodyWrites s) (prologueState s).mem t.mem

theorem private_body_frame {s t u : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (done : InitialBody.Done t u (abiParams s)) :
    Frame (VG.Proof.Argon2.X86_64.Derive.bodyWrites s) (prologueState s).mem u.mem := by
  have words := VG.Proof.Argon2.X86_64.Derive.private_words h prepared
  have matrix := VG.Proof.Argon2.X86_64.Derive.private_matrix_region h prepared
  have work : (⟨FinalOutput.work t, 16384⟩ : Region) = abiWork s := by
    change (⟨Initial.wordAt t 248, 16384⟩ : Region) = abiWork s
    rw [words.work]; rfl
  have output : (⟨FinalOutput.output t, (abiParams s).tagLen⟩ : Region) = abiOutput s := by
    change (⟨Initial.wordAt t 256, (abiParams s).tagLen⟩ : Region) = abiOutput s
    rw [words.output]; rfl
  have body := done.frame
  rw [InitFill.writes, matrix, work, output, prepared.sp, prepared.bp] at body
  apply ((VG.Proof.Argon2.X86_64.Derive.private_prepare_frame prepared).mono ?_).trans (body.sub ?_)
  · intro r hr
    simp only [List.mem_singleton] at hr; subst r
    simp only [VG.Proof.Argon2.X86_64.Derive.bodyWrites, List.mem_cons, true_or, or_true]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨abiMatrix s, by simp [VG.Proof.Argon2.X86_64.Derive.bodyWrites], fun _ h => h⟩
    · exact ⟨abiWork s, by simp [VG.Proof.Argon2.X86_64.Derive.bodyWrites], fun _ h => h⟩
    · exact ⟨abiOutput s, by simp [VG.Proof.Argon2.X86_64.Derive.bodyWrites], fun _ h => h⟩
    · exact ⟨below ((prologueState s).gpr .rsp) 24, by simp [VG.Proof.Argon2.X86_64.Derive.bodyWrites], fun _ h => h⟩
    · exact ⟨⟨(prologueState s).gpr .rsp, 272⟩, by simp [VG.Proof.Argon2.X86_64.Derive.bodyWrites], Region.sub_prefix (by decide)⟩

theorem body_ok [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State) (h : AbiEnvironment s) :
    WP isa (Impl.Argon2.X86_64.Derive.body name (HPrime.hash v)) (prologueState s) (VG.Proof.Argon2.X86_64.Derive.BodyDone s) := by
  unfold Impl.Argon2.X86_64.Derive.body
  refine WP.seq ((prologue_prepare s h).mono ?_)
  intro t prepared
  refine (VG.Proof.Argon2.X86_64.Derive.private_pipeline_ok v name s t h prepared).mono ?_
  intro u done
  exact ⟨VG.Proof.Argon2.X86_64.Derive.private_done_post h prepared done, done.sp.trans prepared.sp,
    done.rd.trans prepared.rd, done.wr.trans prepared.wr, VG.Proof.Argon2.X86_64.Derive.private_body_frame h prepared done⟩

end VG.Proof.Argon2.X86_64.Derive
end

/-! The whole body leaves the prologue's six saved-register slots untouched. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def savedSlot (s : State) (j : Nat) : Region :=
  ⟨s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1)), 8⟩

theorem saved_slot_sub (s : State) (j : Nat) (bound : j < 6) :
    Region.Sub (VG.Proof.Argon2.X86_64.Derive.savedSlot s j) (below (s.gpr .rsp) 344) :=
  Offset.sub_below _ (by omega) (by omega)

theorem saved_slot_address (s : State) (j : Nat) (bound : j < 6) :
    (VG.Proof.Argon2.X86_64.Derive.savedSlot s j).base = (prologueState s).gpr .rsp + BitVec.ofNat 64 (320 - 8 * (j + 1)) := by
  rw [prologue_sp]
  exact Offset.sub_ofNat_eq _ (by omega)

theorem saved_slot_buffers {s : State} (h : AbiEnvironment s) (j : Nat) (bound : j < 6)
    (buffer : Region × Bool) (member : buffer ∈ abiBuffers s ++ [(abiArguments s, false)]) :
    (VG.Proof.Argon2.X86_64.Derive.savedSlot s j).Disjoint buffer.1 :=
  (h.reserved _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) buffer member).sub_left
    (VG.Proof.Argon2.X86_64.Derive.saved_slot_sub s j bound)

theorem saved_slot_writes {s : State} (h : AbiEnvironment s) (j : Nat) (bound : j < 6) :
    ∀ r ∈ VG.Proof.Argon2.X86_64.Derive.bodyWrites s, (VG.Proof.Argon2.X86_64.Derive.savedSlot s j).Disjoint r := by
  intro r hr
  simp only [VG.Proof.Argon2.X86_64.Derive.bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · apply VG.Proof.Argon2.X86_64.Derive.saved_slot_buffers h j bound (abiMatrix s, true)
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  · apply VG.Proof.Argon2.X86_64.Derive.saved_slot_buffers h j bound (abiWork s, true)
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  · apply VG.Proof.Argon2.X86_64.Derive.saved_slot_buffers h j bound (abiOutput s, true)
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  · change (⟨(VG.Proof.Argon2.X86_64.Derive.savedSlot s j).base, 8⟩ : Region).Disjoint _
    rw [VG.Proof.Argon2.X86_64.Derive.saved_slot_address s j bound]
    exact Offset.disjoint_base _ (by omega) (by omega)
  · change (⟨(VG.Proof.Argon2.X86_64.Derive.savedSlot s j).base, 8⟩ : Region).Disjoint _
    rw [VG.Proof.Argon2.X86_64.Derive.saved_slot_address s j bound]
    exact Offset.disjoint_below _ (by omega)

theorem BodyDone.saved {s t : State} (h : AbiEnvironment s) (done : VG.Proof.Argon2.X86_64.Derive.BodyDone s t) (j : Nat) (bound : j < 6) :
    t.mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 =
      (prologueState s).mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 :=
  done.frame.readW (r := VG.Proof.Argon2.X86_64.Derive.savedSlot s j) (Region.contains_self _ _) (VG.Proof.Argon2.X86_64.Derive.saved_slot_writes h j bound) (by decide)

end VG.Proof.Argon2.X86_64.Derive
end

/-! The nested ABI frames return the complete result and restore all saved registers. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def wholeWrites (s : State) : List Region := [abiMatrix s, abiWork s, abiOutput s, below (s.gpr .rsp) 344]

theorem BodyDone.whole_frame {s t : State} (h : AbiEnvironment s) (done : VG.Proof.Argon2.X86_64.Derive.BodyDone s t) :
    Frame (VG.Proof.Argon2.X86_64.Derive.wholeWrites s) s.mem t.mem := by
  have prologue := frameStart_frame s Impl.Argon2.X86_64.Derive.saved (by decide) (by
    have space := h.stack; change 320 ≤ (s.gpr .rsp).toNat; omega)
  apply (prologue.sub ?_).trans (done.frame.sub ?_)
  · intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨below (s.gpr .rsp) 344, by simp [VG.Proof.Argon2.X86_64.Derive.wholeWrites], below_sub (by decide) (by decide)⟩
  · intro r hr
    simp only [VG.Proof.Argon2.X86_64.Derive.bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨abiMatrix s, by simp [VG.Proof.Argon2.X86_64.Derive.wholeWrites], fun _ h => h⟩
    · exact ⟨abiWork s, by simp [VG.Proof.Argon2.X86_64.Derive.wholeWrites], fun _ h => h⟩
    · exact ⟨abiOutput s, by simp [VG.Proof.Argon2.X86_64.Derive.wholeWrites], fun _ h => h⟩
    · refine ⟨below (s.gpr .rsp) 344, by simp [VG.Proof.Argon2.X86_64.Derive.wholeWrites], ?_⟩
      rw [prologue_sp]
      exact Offset.sub_below _ (by decide) (by decide)
    · refine ⟨below (s.gpr .rsp) 344, by simp [VG.Proof.Argon2.X86_64.Derive.wholeWrites], ?_⟩
      rw [prologue_sp]
      unfold below
      rw [BitVec.sub_sub, ← BitVec.ofNat_add]
      exact Region.sub_prefix (by decide)

theorem return_post {s t : State} (done : VG.Proof.Argon2.X86_64.Derive.BodyDone s t) :
    (Spec.Argon2.deriveContract X86_64.abi 344).post s (frameEnd t Impl.Argon2.X86_64.Derive.saved) := by
  have post := done.post
  sig_post [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at post
  sig_post [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop]
  exact post

theorem code_wp [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State)
    (pre : (Spec.Argon2.deriveContract X86_64.abi 344).pre s) :
    WP isa (Impl.Argon2.X86_64.Derive.code name (HPrime.hash v)) s fun t =>
      (Spec.Argon2.deriveContract X86_64.abi 344).post s t ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ Frame (VG.Proof.Argon2.X86_64.Derive.wholeWrites s) s.mem t.mem := by
  have h := abi_environment s pre
  unfold Impl.Argon2.X86_64.Derive.code
  apply frame_ok s Impl.Argon2.X86_64.Derive.saved _ _ (by decide)
    (by have space := h.stack; change 320 ≤ (s.gpr .rsp).toNat; omega)
  refine (VG.Proof.Argon2.X86_64.Derive.body_ok v name s h).mono ?_
  intro t done
  refine ⟨done.sp, done.wr, VG.Proof.Argon2.X86_64.Derive.return_post done, ?_, ?_⟩
  · have restored := VG.Proof.Argon2.X86_64.Derive.frame_restored s t Impl.Argon2.X86_64.Derive.saved (by decide) (by decide)
      (by have space := h.stack; change 320 ≤ (s.gpr .rsp).toNat; omega) done.sp
      (fun j hj => done.saved h j hj)
    have stack := (frameEnd_metadata s t Impl.Argon2.X86_64.Derive.saved done.sp done.wr).1
    intro r hr
    have member : ∀ r ∈ calleeSaved, r = .rsp ∨ r ∈ Impl.Argon2.X86_64.Derive.saved := by decide
    rcases member r hr with rfl | hr
    · exact stack
    · exact restored r hr
  · rw [frameEnd_mem]
    exact done.whole_frame h

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DerivePublic`. -/
section
/-! The public entry-point relation reads u32 arguments at their declared width. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure AbiPublic (s t : State) : Prop where
  sp : s.gpr .rsp = t.gpr .rsp
  regs : ∀ r ∈ [.rsi, .rdx, .rcx, .r8], s.gpr r = t.gpr r
  smallRegs : ∀ r ∈ [.rdi, .r9], (s.gpr r).setWidth 32 = (t.gpr r).setWidth 32
  smallWords : ∀ d ∈ [8, 16, 24], (abiWord s d).setWidth 32 = (abiWord t d).setWidth 32
  words : ∀ d ∈ [32, 40, 48, 56, 64, 72, 80, 88, 96], abiWord s d = abiWord t d
  references : Spec.Argon2.references (abiParams s)
      (Spec.Blake2.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
      (Spec.Blake2.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
      (Spec.Blake2.bytesAt s.mem (abiWord s 32) (abiWord s 40).toNat)
      (Spec.Blake2.bytesAt s.mem (abiWord s 48) (abiWord s 56).toNat) =
    Spec.Argon2.references (abiParams t)
      (Spec.Blake2.bytesAt t.mem (t.gpr .rsi) (t.gpr .rdx).toNat)
      (Spec.Blake2.bytesAt t.mem (t.gpr .rcx) (t.gpr .r8).toNat)
      (Spec.Blake2.bytesAt t.mem (abiWord t 32) (abiWord t 40).toNat)
      (Spec.Blake2.bytesAt t.mem (abiWord t 48) (abiWord t 56).toNat)

theorem abi_public (s t : State) (h : (Spec.Argon2.deriveContract X86_64.abi 344).pub s t) :
    VG.Proof.Argon2.X86_64.Derive.AbiPublic s t := by
  sig_pub [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  sig_split h
  constructor
  all_goals sig_eval [abiWord, abiParams]
  all_goals sig_and_intros
  all_goals sig_close
  all_goals with_reducible assumption

theorem AbiPublic.params {s t : State} (h : VG.Proof.Argon2.X86_64.Derive.AbiPublic s t) : abiParams s = abiParams t := by
  unfold abiParams
  rw [h.smallRegs .rdi (by simp), h.smallRegs .r9 (by simp),
    h.smallWords 8 (by simp), h.smallWords 16 (by simp), h.words 96 (by simp)]

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DerivePrivatePublic`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveParametersCT`. -/
section
/-! Parameter calculation followed by the complete body obeys the reviewed leakage. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64 VG.Spec.Argon2

structure ParametersRelated (p : Params) (s t : State) : Prop where
  left : Parameters.Ready p s
  right : Parameters.Ready p t
  body : InitialBody.ReviewedRelated p (VG.Proof.Argon2.X86_64.Derive.dimensionState s p) (VG.Proof.Argon2.X86_64.Derive.dimensionState t p)

theorem parameters_body_rel [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) (p : Params) :
    RelCT isa (VG.Proof.Argon2.X86_64.Derive.ParametersRelated p)
      (.seq Impl.Argon2.X86_64.Parameters.code
        (Impl.Argon2.X86_64.InitialBody.code name (HPrime.hash v))) (fun _ _ => True) := by
  have preparation := (Parameters.code_rel.mono (P' := VG.Proof.Argon2.X86_64.Derive.ParametersRelated p)
    (fun s t h => by
      have left := VG.Proof.Argon2.X86_64.Derive.dimension_frame s p
      have right := VG.Proof.Argon2.X86_64.Derive.dimension_frame t p
      exact left.bp.symm.trans (h.body.hashing.bp.trans right.bp))
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨Parameters.code_ok s p h.left, Parameters.code_ok t p h.right⟩)
  refine preparation.seq ((InitialBody.reviewed_rel v name p).mono ?_ (fun _ _ h => h))
  rintro a b ⟨_, s, t, h, ⟨length₁, keeps₁⟩, ⟨length₂, keeps₂⟩⟩
  exact h.body.of_state (VG.Proof.Argon2.X86_64.Derive.parameters_frame p keeps₁) (VG.Proof.Argon2.X86_64.Derive.parameters_frame p keeps₂) length₁ length₂

end VG.Proof.Argon2.X86_64.Derive
end

/-! Private argument copies retain exactly the reviewed public relation. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64
open VG.Proof.Argon2.X86_64.Initial (wordAt)

theorem DeriveWords.public_words {s₁ s₂ t₁ t₂ : State} (h : VG.Proof.Argon2.X86_64.Derive.AbiPublic s₁ s₂)
    (left : VG.Proof.Argon2.X86_64.Derive.DeriveWords s₁ t₁) (right : VG.Proof.Argon2.X86_64.Derive.DeriveWords s₂ t₂) :
    ∀ d ∈ Initial.slots, wordAt t₁ d = wordAt t₂ d := by
  intro d hd
  simp only [Initial.slots, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [left.passes, right.passes, h.params]
  · rw [left.saltLength, right.saltLength]; exact h.regs .r8 (by simp)
  · rw [left.salt, right.salt]; exact h.regs .rcx (by simp)
  · rw [left.passwordLength, right.passwordLength]; exact h.regs .rdx (by simp)
  · rw [left.password, right.password]; exact h.regs .rsi (by simp)
  · rw [left.kind, right.kind, h.params]
  · rw [left.memory, right.memory, h.params]
  · rw [left.lanes, right.lanes, h.params]
  · rw [left.secret, right.secret]; exact h.words 32 (by simp)
  · rw [left.secretLength, right.secretLength]; exact h.words 40 (by simp)
  · rw [left.ad, right.ad]; exact h.words 48 (by simp)
  · rw [left.adLength, right.adLength]; exact h.words 56 (by simp)
  · rw [left.tagLength, right.tagLength, h.params]

def abiReferences (s : State) : List Nat := Spec.Argon2.references (abiParams s)
  (Spec.Blake2.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
  (Spec.Blake2.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
  (Spec.Blake2.bytesAt s.mem (abiWord s 32) (abiWord s 40).toNat)
  (Spec.Blake2.bytesAt s.mem (abiWord s 48) (abiWord s 56).toNat)

theorem private_references {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    InitialBody.references (abiParams s) t = VG.Proof.Argon2.X86_64.Derive.abiReferences s := by
  have words := VG.Proof.Argon2.X86_64.Derive.private_words h prepared
  have password := VG.Proof.Argon2.X86_64.Derive.private_input_bytes h prepared (104, 96) (by decide)
  have salt := VG.Proof.Argon2.X86_64.Derive.private_input_bytes h prepared (88, 80) (by decide)
  have secret := VG.Proof.Argon2.X86_64.Derive.private_input_bytes h prepared (200, 208) (by decide)
  have ad := VG.Proof.Argon2.X86_64.Derive.private_input_bytes h prepared (216, 224) (by decide)
  simp only [Initial.inputRegion] at password salt secret ad
  rw [words.password, words.passwordLength] at password
  rw [words.salt, words.saltLength] at salt
  rw [words.secret, words.secretLength] at secret
  rw [words.ad, words.adLength] at ad
  unfold InitialBody.references VG.Proof.Argon2.X86_64.Derive.abiReferences
  change Spec.Argon2.references (abiParams s) (Initial.inputBytes t 104 96)
    (Initial.inputBytes t 88 80) (Initial.inputBytes t 200 208) (Initial.inputBytes t 216 224) = _
  rw [password, salt, secret, ad]

theorem private_parameters_related {s₁ s₂ t₁ t₂ : State}
    (left : AbiEnvironment s₁) (right : AbiEnvironment s₂) (h : VG.Proof.Argon2.X86_64.Derive.AbiPublic s₁ s₂)
    (prepared₁ : PrivatePrepared (prologueState s₁) t₁)
    (prepared₂ : PrivatePrepared (prologueState s₂) t₂) :
    VG.Proof.Argon2.X86_64.Derive.ParametersRelated (abiParams s₁) t₁ t₂ := by
  have same := h.params
  have ready₁ := VG.Proof.Argon2.X86_64.Derive.private_body_ready left prepared₁
  have ready₂ := VG.Proof.Argon2.X86_64.Derive.private_body_ready right prepared₂
  rw [← same] at ready₂
  have keeps₁ := VG.Proof.Argon2.X86_64.Derive.dimension_frame t₁ (abiParams s₁)
  have keeps₂ := VG.Proof.Argon2.X86_64.Derive.dimension_frame t₂ (abiParams s₁)
  have words₁ := (VG.Proof.Argon2.X86_64.Derive.private_words left prepared₁).of_state keeps₁
  have words₂ := (VG.Proof.Argon2.X86_64.Derive.private_words right prepared₂).of_state keeps₂
  have sp : t₁.gpr .rsp = t₂.gpr .rsp := by rw [prepared₁.sp, prepared₂.sp, prologue_sp, prologue_sp, h.sp]
  have bp : t₁.gpr .rbp = t₂.gpr .rbp := by rw [prepared₁.bp, prepared₂.bp, prologue_sp, prologue_sp, h.sp]
  have bx : t₁.gpr .rbx = t₂.gpr .rbx := by
    rw [VG.Proof.Argon2.X86_64.Derive.private_scratch left prepared₁, VG.Proof.Argon2.X86_64.Derive.private_scratch right prepared₂]
    exact h.words 80 (by simp)
  refine ⟨private_parameters left prepared₁, same.symm ▸ private_parameters right prepared₂, ?_⟩
  refine ⟨ready₁, ready₂, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨ready₁.hashSpace, ready₁.inputs⟩,
      ⟨ready₂.hashSpace, ready₂.inputs⟩, ?_, ?_, ?_, ?_⟩
    · rw [keeps₁.bp, keeps₂.bp]; exact bp
    · rw [keeps₁.bx, keeps₂.bx]; exact bx
    · rw [keeps₁.sp, keeps₂.sp]; exact sp
    · exact words₁.public_words h words₂
  · exact words₁.matrix.trans ((h.words 64 (by simp)).trans words₂.matrix.symm)
  · exact words₁.output.trans ((h.words 88 (by simp)).trans words₂.output.symm)
  · exact words₁.work.trans ((h.words 80 (by simp)).trans words₂.work.symm)
  · unfold InitialBody.references
    simp only [keeps₁.inputBytes, keeps₂.inputBytes]
    change InitialBody.references (abiParams s₁) t₁ = InitialBody.references (abiParams s₁) t₂
    rw [VG.Proof.Argon2.X86_64.Derive.private_references left prepared₁, same, VG.Proof.Argon2.X86_64.Derive.private_references right prepared₂]
    exact h.references

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DerivePrepareCT`. -/
section
/-! ABI argument preparation accesses only fixed offsets of the public stack. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem prepare_rel : RelCT isa (fun s t => s.gpr .rsp = t.gpr .rsp)
    Impl.Argon2.X86_64.Derive.prepare (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rsp]) (fun _ _ h =>
    Taint.agree_ofRegs (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h))
    (by taint_decide)

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveMxcsr`. -/
section
/-! The complete derivation preserves MXCSR for every BLAKE2b backend. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

local notation "property" => (fun i => !loadsMxcsr i)

theorem initial_mxcsr (v : Proof.Blake2.X86_64.Backend) :
    (Impl.Argon2.X86_64.Initial.code (HPrime.hash v)).allInstrs property = true := by
  have init : (HPrime.hash v).init.allInstrs property = true := by
    change (Impl.Blake2.X86_64.Stream.init Spec.Blake2.b).allInstrs _ = true
    lit_decide
  have update : (HPrime.hash v).update.allInstrs property = true := v.updateMxcsr
  have finalize : (HPrime.hash v).finalize.allInstrs property = true := v.finalizeMxcsr
  simp only [Impl.Argon2.X86_64.Initial.code, Impl.Argon2.X86_64.Initial.start,
    Impl.Argon2.X86_64.Initial.absorb, Impl.Argon2.X86_64.Initial.finish,
    Impl.Argon2.X86_64.HPrime.init, Impl.Argon2.X86_64.HPrime.absorbFixed,
    Impl.Argon2.X86_64.HPrime.update, Impl.Argon2.X86_64.HPrime.finalize, Code.allInstrs]
  rw [init, update, finalize]
  lit_decide

theorem memory_mxcsr (v : Proof.Blake2.X86_64.Backend) (name : String) :
    (Impl.Argon2.X86_64.MemoryInit.code name (HPrime.hash v)).allInstrs property = true := by
  simp only [Impl.Argon2.X86_64.MemoryInit.code, Impl.Argon2.X86_64.MemoryInit.clear,
    Impl.Argon2.X86_64.MemoryInit.lane, Impl.Argon2.X86_64.MemoryInit.block, Code.allInstrs]
  rw [HPrime.code_mxcsr v]
  lit_decide

theorem frame_ctlC (body : Prog isa) (rs : List Reg) (h : ctlC body = true) :
    ctlC (Impl.Argon2.X86_64.Derive.frame body rs) = true := by
  induction rs with
  | nil => simpa [Impl.Argon2.X86_64.Derive.frame, ctlC, loadsMxcsr] using h
  | cons r rs ih => simpa [Impl.Argon2.X86_64.Derive.frame, ctlC, loadsMxcsr] using ih

theorem finish_mxcsr (v : Proof.Blake2.X86_64.Backend) (name : String) :
    (Impl.Argon2.X86_64.Finish.code name (HPrime.hash v)).allInstrs property = true := by
  simp only [Impl.Argon2.X86_64.Finish.code, Impl.Argon2.X86_64.FinalOutput.code, Code.allInstrs]
  rw [HPrime.code_mxcsr v]
  lit_decide

/-- The filling passes keep MXCSR's control bits: their calls of G do
(`CompressImpl.ctl`), and they never load MXCSR themselves. -/
theorem fill_ctlC [CompressImpl] : ctlC Impl.Argon2.X86_64.FillIterations.loop = true := by
  simp only [Impl.Argon2.X86_64.FillIterations.loop, Impl.Argon2.X86_64.FillIterations.body,
    Impl.Argon2.X86_64.FillIteration.code, Impl.Argon2.X86_64.FillSlices.loop,
    Impl.Argon2.X86_64.FillSlices.body, Impl.Argon2.X86_64.FillSlice.code,
    Impl.Argon2.X86_64.FillLanes.loop, Impl.Argon2.X86_64.FillLanes.body,
    Impl.Argon2.X86_64.SegmentSetup.code, Impl.Argon2.X86_64.FillSegment.loop,
    Impl.Argon2.X86_64.FillSegment.body, Impl.Argon2.X86_64.FillBlock.code,
    Impl.Argon2.X86_64.RandomSource.code, Impl.Argon2.X86_64.AddressCache.code,
    Impl.Argon2.X86_64.AddressCache.select, Impl.Argon2.X86_64.AddressCalls.code,
    Impl.Argon2.X86_64.AddressCalls.calls, Impl.Argon2.X86_64.AddressCalls.stage,
    Impl.Argon2.X86_64.FillKernel.code, Impl.Argon2.X86_64.FillCompress.code,
    Impl.Argon2.X86_64.FillCompress.operation, ctlC]
  rw [compressor_ctl]
  lit_decide

theorem code_ctl [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) :
    ctlOk (Impl.Argon2.X86_64.Derive.code name (HPrime.hash v)) = true := by
  apply ctlOk_of_ctlC
  unfold Impl.Argon2.X86_64.Derive.code
  apply VG.Proof.Argon2.X86_64.Derive.frame_ctlC
  simp only [Impl.Argon2.X86_64.Derive.body, Impl.Argon2.X86_64.InitialBody.code,
    Impl.Argon2.X86_64.InitFill.code, Impl.Argon2.X86_64.FillFinish.code, ctlC]
  rw [ctlC_of_allInstrs (VG.Proof.Argon2.X86_64.Derive.initial_mxcsr v), ctlC_of_allInstrs (VG.Proof.Argon2.X86_64.Derive.memory_mxcsr v name),
    ctlC_of_allInstrs (VG.Proof.Argon2.X86_64.Derive.finish_mxcsr v name), VG.Proof.Argon2.X86_64.Derive.fill_ctlC]
  lit_decide

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveFrameCT`. -/
section
/-! Saving and restoring the ABI frame leaks only the public stack pointer. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem frame_rel (rs : List Reg) (body : Prog isa) (P : State → State → Prop)
    (sp : ∀ s t, P s t → s.gpr .rsp = t.gpr .rsp)
    (run : RelCT isa (fun a b => ∃ s t, P s t ∧ a = frameStart s rs ∧ b = frameStart t rs)
      body (fun _ _ => True)) :
    RelCT isa P (Impl.Argon2.X86_64.Derive.frame body rs) (fun _ _ => True) := by
  induction rs generalizing P with
  | nil => exact RelCT.frame sp run
  | cons r rs ih =>
    apply RelCT.frame sp
    apply ih (fun a b => ∃ s t, P s t ∧ a = pushed [r] s ∧ b = pushed [r] t) ?_ ?_
    · rintro a b ⟨s, t, hp, rfl, rfl⟩
      rw [pushed_rsp, pushed_rsp, sp s t hp]
    · apply run.mono ?_ (fun _ _ h => h)
      rintro a b ⟨u, v, ⟨s, t, hp, rfl, rfl⟩, rfl, rfl⟩
      exact ⟨s, t, hp, rfl, rfl⟩

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveCorrect`. -/
section
/-! Functional correctness, termination, memory safety, and the complete System V ABI. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem code_correct [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State)
    (pre : (Spec.Argon2.deriveContract X86_64.abi 344).pre s) :
    ∃ tr t, Exec isa (Impl.Argon2.X86_64.Derive.code name (HPrime.hash v)) s tr t ∧
      abiPreserved s t ∧ (Spec.Argon2.deriveContract X86_64.abi 344).post s t := by
  obtain ⟨tr, t, run, post, regs, frame⟩ := VG.Proof.Argon2.X86_64.Derive.code_wp v name s pre
  refine ⟨tr, t, run, abiPreserved_of_ctl (VG.Proof.Argon2.X86_64.Derive.code_ctl v name) run ⟨regs, ?_⟩, post⟩
  have h := abi_environment s pre
  apply frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [VG.Proof.Argon2.X86_64.Derive.wholeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.reserved _ (by simp) (abiMatrix s, true)
      (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  · exact h.reserved _ (by simp) (abiWork s, true)
      (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  · exact h.reserved _ (by simp) (abiOutput s, true)
      (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  · exact Offset.base_disjoint_below _ (by decide)

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveContract`. -/
section
/-! A concrete caller establishes satisfiability of the shared derivation contract. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def satArgs : List Nat := [8, 1, 1, 0, 0, 0, 0, 0x10000, 8, 0x20000, 0x30000, 4]

def satMem (a : Addr) : Byte :=
  let d := a.toNat - 0x40008
  if 0x40008 ≤ a.toNat ∧ a.toNat < 0x40068 then
    ((BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.satArgs[d / 8]?.getD 0)) >>> (8 * (d % 8))).setWidth 8
  else 0

def satState : State where
  gpr r := match r with
    | .rsp => 0x40000 | .r9 => 1 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Argon2.X86_64.Derive.satMem
  rd := [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x40008, 96⟩]
  wr := [⟨0x10000, 8192⟩, ⟨0x20000, 16384⟩, ⟨0x30000, 4⟩]

theorem contract_sat : ∃ s, (Spec.Argon2.deriveContract X86_64.abi 344).pre s := by
  refine ⟨VG.Proof.Argon2.X86_64.Derive.satState, ?_⟩
  sig_sat_check [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop,
    VG.Proof.Argon2.X86_64.Derive.satState, VG.Proof.Argon2.X86_64.Derive.satMem, VG.Proof.Argon2.X86_64.Derive.satArgs, Spec.Argon2.params, Spec.Argon2.valid,
    Spec.Argon2.Params.blocks, Spec.Argon2.Params.segmentLen]

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveCT`. -/
section
/-! The entire entry point leaks only the exact allowance of the shared contract. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def AbiRelated (s t : State) : Prop := AbiEnvironment s ∧ AbiEnvironment t ∧ VG.Proof.Argon2.X86_64.Derive.AbiPublic s t

def PrologueRelated (a b : State) : Prop := ∃ s t, VG.Proof.Argon2.X86_64.Derive.AbiRelated s t ∧ a = prologueState s ∧ b = prologueState t

theorem body_rel [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) :
    RelCT isa VG.Proof.Argon2.X86_64.Derive.PrologueRelated (Impl.Argon2.X86_64.Derive.body name (HPrime.hash v)) (fun _ _ => True) := by
  have preparation := (prepare_rel.mono (P' := VG.Proof.Argon2.X86_64.Derive.PrologueRelated) (by
      rintro a b ⟨s, t, h, rfl, rfl⟩
      rw [prologue_sp, prologue_sp, h.2.2.sp]) (fun _ _ h => h)).wpDep (F := fun a b =>
        ∃ s, a = prologueState s ∧ AbiEnvironment s ∧ PrivatePrepared a b) (by
      rintro a b ⟨s, t, h, rfl, rfl⟩
      exact ⟨(prologue_prepare s h.1).mono (fun _ prepared => ⟨s, rfl, h.1, prepared⟩),
        (prologue_prepare t h.2.1).mono (fun _ prepared => ⟨t, rfl, h.2.1, prepared⟩)⟩)
  unfold Impl.Argon2.X86_64.Derive.body
  apply preparation.seq
  apply (RelCT.exists_ (fun p => VG.Proof.Argon2.X86_64.Derive.parameters_body_rel v name p)).mono ?_ (fun _ _ h => h)
  rintro a b ⟨_, x, y, ⟨s, t, h, rfl, rfl⟩,
    ⟨u, hu, _, prepared₁⟩, ⟨w, hw, _, prepared₂⟩⟩
  have left : PrivatePrepared (prologueState s) a := prepared₁
  have right : PrivatePrepared (prologueState t) b := prepared₂
  exact ⟨abiParams s, VG.Proof.Argon2.X86_64.Derive.private_parameters_related h.1 h.2.1 h.2.2 left right⟩

theorem code_ct [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) :
    ConstantTime isa (Spec.Argon2.deriveContract X86_64.abi 344).pre
      (Spec.Argon2.deriveContract X86_64.abi 344).pub
      (Impl.Argon2.X86_64.Derive.code name (HPrime.hash v)) := by
  have full := VG.Proof.Argon2.X86_64.Derive.frame_rel Impl.Argon2.X86_64.Derive.saved _ VG.Proof.Argon2.X86_64.Derive.AbiRelated
    (fun _ _ h => h.2.2.sp) (VG.Proof.Argon2.X86_64.Derive.body_rel v name)
  exact (full.mono (fun s t h =>
    ⟨abi_environment s h.1, abi_environment t h.2.1, VG.Proof.Argon2.X86_64.Derive.abi_public s t h.2.2⟩)
    (fun _ _ h => h)).constantTime

end VG.Proof.Argon2.X86_64.Derive
end

/-! Complete Argon2 verification against the reviewed shared API contract. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem verified [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) :
    Verified X86_64.target (Impl.Argon2.X86_64.Derive.code name (HPrime.hash v))
      (Spec.Argon2.deriveContract X86_64.abi 344) :=
  ⟨VG.Proof.Argon2.X86_64.Derive.code_correct v name, VG.Proof.Argon2.X86_64.Derive.code_ct v name, VG.Proof.Argon2.X86_64.Derive.contract_sat⟩

end VG.Proof.Argon2.X86_64.Derive

end
