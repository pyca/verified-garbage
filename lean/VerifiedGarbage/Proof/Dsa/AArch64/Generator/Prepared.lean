module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Geometry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Entry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchMemory
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Spec.Dsa

/-! # The generator search's plan and memory, once the entry has filled the frame

The plan is the generation's: p and the exponent at their offsets of the
working space, the h tape, and q; it depends on nothing but the arguments
and these values, which are public. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.Dsa.AArch64.Generation (GeneratorSearchPlan GeneratorSearchMemory generatorSlots)

variable {pLen : Nat} {s : State}

/-- p's bytes. -/
abbrev pBytes (pLen : Nat) (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) VG.Impl.Dsa.Generation.Layout.p) pLen

/-- q's bytes. -/
abbrev qBytes (pLen : Nat) (s : State) : List Byte :=
  Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) VG.Impl.Dsa.Generation.Layout.q) (Impl.Dsa.AArch64.Generator.qLen pLen)

/-- The exponent's bytes. -/
abbrev eBytes (pLen : Nat) (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) VG.Impl.Dsa.Generation.Layout.exponent) pLen

/-- The h tape. -/
abbrev tape (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat

theorem Supported.pos {pLen : Nat} (hb : Supported pLen) : 0 < 8 * pLen := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem used_small (hb : Supported pLen) {d n : Nat} (hd : d ≤ domainCheck) (hn : n ≤ arithmeticBytes) :
    d + n ≤ usedBytes pLen := by
  rcases hb with rfl | rfl | rfl <;> unfold usedBytes domainCheck arithmeticBytes at * <;> omega

theorem used_parent (hb : Supported pLen) : 0 + Impl.Dsa.Layout.activeBytes ≤ usedBytes pLen := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem used_lt (hb : Supported pLen) : usedBytes pLen < 2 ^ 64 := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem pow256 (n : Nat) : 256 ^ n = 2 ^ (8 * n) := by
  rw [Nat.pow_mul]

theorem StageABI.p_bounds (hb : Supported pLen) (A : StageABI pLen s) :
    2 ^ (8 * pLen - 1) ≤ pOf pLen s.mem (s.gpr .x0) ∧ pOf pLen s.mem (s.gpr .x0) < 256 ^ pLen := by
  rw [pow256]
  exact (bitLength_iff_bounds hb.pos).mp A.bits

theorem StageABI.positive (hb : Supported pLen) (A : StageABI pLen s) : 1 < Spec.Dsa.decodeBE (pBytes pLen s) :=
  Nat.lt_of_lt_of_le (Nat.one_lt_two_pow (by rcases hb with rfl | rfl | rfl <;> decide)) (A.p_bounds hb).1

theorem StageABI.exponentValue (hb : Supported pLen) (A : StageABI pLen s) :
    Spec.Dsa.decodeBE (eBytes pLen s) = (Spec.Dsa.decodeBE (pBytes pLen s) - 1) / qOf pLen s.mem (s.gpr .x0) := by
  have e := A.exponent
  change Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) VG.Impl.Dsa.Generation.Layout.exponent) pLen = _ at e
  rw [eBytes, e, VG.Proof.Dsa.decodeBE_encodeBE]
  · rfl
  · exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)) (A.p_bounds hb).2

/-- The generator search's plan. -/
def plan (hb : Supported pLen) (A : StageABI pLen s) : GeneratorSearchPlan where
  core := (arena hb A).generatorPlan (pBytes pLen s) (eBytes pLen s) (bytesAt_length _ _ _) (bytesAt_length _ _ _)
    (A.positive hb) A.odd
  saved := entryWords (s.gpr .x0) (s.gpr .x2) (s.gpr .x3)
  tape := tape s
  tapePtr := s.gpr .x2
  tapeFits := by rw [bytesAt_length]; exact (s.gpr .x3).isLt
  tapeSeparate := by
    rw [bytesAt_length]
    have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
    intro r hr
    simp only [Generation.GeneratorPlan.changed, Arena.generatorPlan, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact A.wsTape.symm.sub_right (A.part_sub (used_small hb (by decide) (by rfl)))
    · have h := A.part_sub (used_parent hb)
      simp only [off, BitVec.add_zero] at h
      exact A.wsTape.symm.sub_right h
    · exact A.wsTape.symm.sub_right (A.part_sub (used_small hb (d := VG.Impl.Dsa.Generation.Layout.g) (n := pLen)
        (by decide) (by unfold arithmeticBytes; omega)))
    · exact A.stackTape.symm.sub_right (frame_sub0 s (by unfold frameBytes; omega))
  q := qOf pLen s.mem (s.gpr .x0)
  exponentValue := A.exponentValue hb

/-- The state the entry leaves: the frame words set, the memory changed in
the frame alone. -/
structure Entered (pLen : Nat) (s u : State) : Prop where
  sp : u.sp = frameBase s
  rd : u.rd = s.rd
  wr : u.wr = ⟨frameBase s, 272⟩ :: s.wr
  frame : Frame [⟨frameBase s, 272⟩, ⟨off (s.gpr .x0) Impl.Dsa.AArch64.Generator.spill,
    Impl.Dsa.AArch64.Generator.spillBytes⟩] s.mem u.mem
  words : ∀ k, (k = 5 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k ∈ Impl.Dsa.AArch64.Generator.zeroSlots) →
    word u.mem (frameBase s) (8 * k) = entryWords (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) k

/-- The frame words, as the generation's search reads them. -/
abbrev frameWords (s u : State) (k : Nat) : BitVec 64 := word u.mem (frameBase s) (8 * k)

theorem StageABI.scr (A : StageABI pLen s) {u : State} (E : Entered pLen s u) :
    Scr u (s.gpr .x0) (usedBytes pLen) := by
  refine ⟨⟨s.gpr .x0, 0, (s.gpr .x1).toNat * 8, ?_, by simp [off], by have := A.size; omega, ?_⟩, ?_⟩
  · rw [E.wr, A.wr]; simp
  · have := A.wsBound; omega
  · have := A.wsBound; have := A.size; omega

theorem spill_used (hb : Supported pLen) :
    Impl.Dsa.AArch64.Generator.spill + Impl.Dsa.AArch64.Generator.spillBytes ≤ usedBytes pLen := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem StageABI.ws_frame (hb : Supported pLen) (A : StageABI pLen s) {d n : Nat}
    (h : d + n ≤ Impl.Dsa.AArch64.Generator.spill) :
    ∀ r ∈ [(⟨frameBase s, 272⟩ : Region), ⟨off (s.gpr .x0) Impl.Dsa.AArch64.Generator.spill,
      Impl.Dsa.AArch64.Generator.spillBytes⟩], Region.Disjoint ⟨off (s.gpr .x0) d, n⟩ r := by
  have hs := spill_used hb
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (A.stackWs.sub_left (frame_sub0 s (Nat.le_refl _))).symm.sub_left (A.part_sub (by omega))
  · exact (arena hb A).parts_disjoint (d := d) (n := n) (show d + n ≤ usedBytes pLen by omega) hs (Or.inl h)

/-- Bytes of the working space below the saved registers are as they were. -/
theorem StageABI.bytes_entered (hb : Supported pLen) (A : StageABI pLen s) {u : State} (E : Entered pLen s u)
    {d n : Nat} (h : d + n ≤ Impl.Dsa.AArch64.Generator.spill) :
    Spec.Rsa.bytesAt u.mem (off (s.gpr .x0) d) n = Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) d) n :=
  VG.Proof.Dsa.Generation.frame_bytesAt E.frame (A.ws_frame hb h)
    (by have := spill_used hb; have := A.wsBound; have := A.size; omega)

theorem StageABI.arenaSrc (hb : Supported pLen) (A : StageABI pLen s) {u : State} (E : Entered pLen s u)
    {d n : Nat} (h : d + n ≤ Impl.Dsa.AArch64.Generator.spill) {work : Addr} {Z : Nat}
    (sep : (⟨off (s.gpr .x0) d, n⟩ : Region).Disjoint ⟨work, Z⟩) :
    Src u work Z (off (s.gpr .x0) d) (Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) d) n) := by
  have hl := bytesAt_length s.mem (off (s.gpr .x0) d) n
  have hs := spill_used hb
  apply VG.Proof.Dsa.AArch64.Generation.arena_source (A.scr E) (by rw [hl]; omega)
    (by rw [hl]; have := used_lt hb; omega)
  · rw [hl, A.bytes_entered hb E h]
  · rw [hl]; exact sep

theorem StageABI.tapeSrc (hb : Supported pLen) (A : StageABI pLen s) {u : State} (E : Entered pLen s u) {work : Addr} {Z : Nat}
    (sep : (tapeRegion s).Disjoint ⟨work, Z⟩) : Src u work Z (s.gpr .x2) (tape s) := by
  have hl := bytesAt_length s.mem (s.gpr .x2) (s.gpr .x3).toNat
  have tf : ∀ r ∈ [(⟨frameBase s, 272⟩ : Region), ⟨off (s.gpr .x0) Impl.Dsa.AArch64.Generator.spill,
      Impl.Dsa.AArch64.Generator.spillBytes⟩], (tapeRegion s).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (A.stackTape.sub_left (frame_sub0 s (Nat.le_refl _))).symm
    · exact A.wsTape.symm.sub_right (A.part_sub (spill_used hb))
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hl] at hi
    exact ⟨_, List.mem_append_left _ (by rw [E.rd, A.rd]; exact List.mem_singleton_self _),
      contains_byte _ hi (by have := A.tapeBound; omega)⟩
  · have hi' : i < (s.gpr .x3).toNat := by rw [hl] at hi; exact hi
    rw [E.frame.bytes tf (R := tapeRegion s) (by change (s.gpr .x3).toNat ≤ 2 ^ 64; have := A.tapeBound; omega) hi']
    simp only [bytesAt_eq, List.getElem_map, List.getElem_range]
  · rw [hl] at hi
    exact out_scr sep (contains_byte _ hi (by have := A.tapeBound; omega))

/-- The search's memory, once the entry has filled the frame. -/
theorem prepared (hb : Supported pLen) (A : StageABI pLen s) {u : State} (E : Entered pLen s u) :
    GeneratorSearchMemory (plan hb A) (frameWords s u) u := by
  have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
  have ha := used_small hb (d := arithmetic) (n := arithmeticBytes) (by decide) (by rfl)
  have hp : VG.Impl.Dsa.Generation.Layout.p + pLen ≤ Impl.Dsa.AArch64.Generator.spill := by
    unfold VG.Impl.Dsa.Generation.Layout.p Impl.Dsa.AArch64.Generator.spill VG.Impl.Dsa.Generation.Layout.control; omega
  have he : VG.Impl.Dsa.Generation.Layout.exponent + pLen ≤ Impl.Dsa.AArch64.Generator.spill := by
    unfold VG.Impl.Dsa.Generation.Layout.exponent Impl.Dsa.AArch64.Generator.spill VG.Impl.Dsa.Generation.Layout.control; omega
  have ps := (plan hb A).core.pSeparate
  have es := (plan hb A).core.eSeparate
  have ts := (plan hb A).tapeSeparate
  simp only [plan, Arena.generatorPlan, arena, bytesAt_length] at ps es ts
  have w := fun k hk => E.words k hk
  refine {
    layout := ⟨E.sp, ?_, ?_, ?_, A.geo hb⟩
    rep := ⟨fun o => u.mem (off (hashBase s) o), fun o _ => rfl, fun k _ => rfl⟩
    base := w 5 (by decide)
    tapeBase := w 11 (by decide)
    tapeLength := ?_
    slots := ?_
    arithmetic := by
      change Scr u (off (s.gpr .x0) arithmetic) arithmeticBytes
      exact (A.scr E).sub ha (by decide)
    parent := by
      change Scr u (s.gpr .x0) Impl.Dsa.Layout.activeBytes
      simpa [off] using (A.scr E).sub (used_parent hb) (by decide)
    pArithmetic := A.arenaSrc hb E hp (ps _ List.mem_cons_self)
    tapeArithmetic := A.tapeSrc hb E (ts _ List.mem_cons_self)
    eArithmetic := A.arenaSrc hb E he (es _ List.mem_cons_self)
    pParent := A.arenaSrc hb E hp (ps _ (List.mem_cons_of_mem _ List.mem_cons_self))
    tapeParent := A.tapeSrc hb E (ts _ (List.mem_cons_of_mem _ List.mem_cons_self))
    eParent := A.arenaSrc hb E he (es _ (List.mem_cons_of_mem _ List.mem_cons_self))
    gWrite := fun i hi => by
      rw [off_off]
      have hg := used_small hb (d := VG.Impl.Dsa.Generation.Layout.g) (n := pLen) (by decide) (by unfold arithmeticBytes; omega)
      exact (A.scr E).region (by change i < pLen at hi; omega) (by decide) }
  · rw [E.wr]
    exact Covers.of_sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_self, 0, by simp; rfl, by unfold frameBytes; simp⟩
  · rw [E.wr]
    show Covers _ ([⟨frameBase s, 272⟩] ++ s.wr)
    refine Covers.right (Covers.of_sub fun r hr => ?_)
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨wsRegion s, by rw [A.wr]; exact List.mem_singleton_self _, Impl.Dsa.Generation.Layout.hash, rfl, ?_⟩
    have := A.size; have := used_small hb (d := Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
    simp only; omega
  · exact w 12 (by decide)
  · change frameWords s u 13 = BitVec.ofNat 64 (tape s).length
    rw [bytesAt_length, ofNat_toNat64]; exact w 13 (by decide)
  · intro k hk
    apply w k
    simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    simp only [Impl.Dsa.AArch64.Generator.zeroSlots, List.mem_cons, List.not_mem_nil, or_false]
    omega

end VG.Proof.Dsa.AArch64.Generator
