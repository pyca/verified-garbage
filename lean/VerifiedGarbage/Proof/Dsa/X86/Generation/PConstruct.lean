module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PAttempt
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Framework.Offset
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArenaReady
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashPrefix
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateFinish
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashesShape

/-! # Compose seed hashing, candidate reduction, and exact persistent outputs -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation.Layout

structure PConstructInputs {H : Hash} (K : HashOK H) (G : GenerationGeometry)
    (C : ContributionPlan) (qvalue : Nat) (s : State) : Prop where
  arena : ArenaReady G s
  contributions : ContributionReady K C s
  layout : ContributionLayout K C
  frame : C.frame = G.frameBase
  seedLength : C.seed.length = G.qLen
  count : C.count = (8 * G.pLen - 1) / (8 * G.qLen)
  parent : s.mem.readW (off G.frameBase 20) 32 = G.parent
  qval : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off G.base q) G.qLen) = qvalue
  qPositive : 0 < qvalue
  qBound : 2 * qvalue < 2 ^ (32 * (2 * (G.pLen / 8)))
  hashRoom : G.pLen ≤ (C.count + 1) * C.seed.length
  hashFit : C.hashes.toNat + (C.count + 1) * C.seed.length ≤ 2 ^ 32
  shapeApart : Region.Disjoint
    ⟨(C.hashes + BitVec.ofNat 32 ((C.count + 1) * C.seed.length - G.pLen)).setWidth 64, G.pLen⟩
    (G.part shaped G.pLen)
  shapeRead : ∀ i < G.pLen, InRegions (s.rd ++ s.wr)
    (off ((C.hashes + BitVec.ofNat 32 ((C.count + 1) * C.seed.length - G.pLen)).setWidth 64) i) 1
  qApart : ∀ r ∈ C.allWrites K, (G.part q G.qLen).Disjoint r

theorem pConstruct_ok {H : Hash} {K : HashOK H} {G : GenerationGeometry}
    {C : ContributionPlan} {qvalue : Nat} {s : State}
    (R : PConstructInputs K G C qvalue s)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * C.seed.length) bs)
    (hashSize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * C.seed.length) bs).length = 8 * C.seed.length) :
    WP isa (pConstruct H G.pLen G.qLen) s fun t =>
      let value := Spec.Dsa.pCandidate (8 * G.pLen) (8 * G.qLen) qvalue C.seed C.offset
      Spec.Rsa.bytesAt t.mem (off G.base p) G.pLen = Spec.Dsa.encodeBE G.pLen value ∧
      Spec.Rsa.bytesAt t.mem (off G.base exponent) G.pLen = Spec.Dsa.encodeBE G.pLen ((value - 1) / qvalue) ∧
      ArenaReady G t ∧
      Frame (C.allWrites K ++ [G.part shaped G.pLen, G.part arithmetic arithmeticBytes,
        G.part p G.pLen, G.part exponent G.pLen]) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  have pw := G.width
  have qw := G.qWidth
  have sr : shaped + G.pLen ≤ usedBytes G.pLen := by unfold shaped usedBytes domainCheck; omega
  have qr : q + G.qLen ≤ usedBytes G.pLen := by unfold q usedBytes domainCheck; omega
  have ss : shaped < usedBytes G.pLen := by omega
  have sa : (G.parent + BitVec.ofNat 32 shaped).setWidth 64 = off G.base shaped := G.pointer_addr ss
  have parent : s.mem.readW (off C.frame 20) 32 = G.parent := by rw [R.frame]; exact R.parent
  have build := pHashesShape_ok R.layout R.contributions parent
    (by omega : 2 ≤ G.pLen) (by omega : G.pLen < 2 ^ 32) R.hashRoom R.hashFit (G.pointer_fit ss sr)
    (by rw [sa]; exact R.shapeApart) R.shapeRead
    (by intro i hi; exact R.arena.writePointer ss sr i 1 (by omega))
  rw [R.seedLength, R.count] at build
  unfold pConstruct
  refine WP.seq (WP.mono build fun a ⟨value, Oa, Ka⟩ => ?_)
  rw [sa] at value Oa
  have frameApart : ∀ r ∈ C.allWrites K ++ [G.part shaped G.pLen],
      (⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨j, hj, h⟩ := List.mem_flatMap.mp hr
      rw [← R.frame]
      exact R.layout.frameApart j (by have := List.mem_range.mp hj; omega) r h
    · obtain rfl := List.mem_singleton.mp hr
      exact G.frame_part sr
  have parentA : a.mem.readW (off G.frameBase 20) 32 = G.parent := by
    rw [Oa.readW (r := ⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩)
      (Offset.contains_base _ (by unfold VG.Impl.Dsa.X86.Generation.frameBytes; decide) (by decide))
      frameApart (by decide), R.parent]
  have qA : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt a.mem (off G.base q) G.qLen) = qvalue := by
    rw [drawFrame_bytes Oa (by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact R.qApart r hr
      · obtain rfl := List.mem_singleton.mp hr
        exact G.parts_disjoint qr sr (.inr (by unfold shaped q; omega))) (by omega), R.qval]
  refine WP.mono (candidateFinish_ok (R.arena.keep Ka (by decide)) parentA qA R.qPositive R.qBound)
    fun t ⟨pb, eb, Rt, Ot, Kt⟩ => ?_
  have candidate := shapedValue_candidate (K := K) (G := C) (by omega : 0 < G.pLen)
    (by rw [R.seedLength]; exact R.count) hash hashSize qvalue
  rw [R.seedLength] at candidate
  rw [value, candidate] at pb eb
  refine ⟨pb, eb, Rt, ?_, Ka.trans Kt⟩
  exact (Oa.mono (by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (by obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_self))).trans
    (Ot.mono (by intro r hr; exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)))
end VG.Proof.Dsa.X86.Generation
