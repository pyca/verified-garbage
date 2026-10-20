module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PConstruct
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateFinishCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashesShape
import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashesShapeCT

/-! # Hash contributions and fixed-width arithmetic compose without private control flow -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Pbkdf2.Stream.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation.Layout

theorem pHashes_candidateReady {H : Hash} {K : HashOK H} {G : GenerationGeometry}
    {C : ContributionPlan} {qvalue : Nat} {s : State} (R : PConstructInputs K G C qvalue s) :
    WP isa (pHashesShape H G.qLen ((8 * G.pLen - 1) / (8 * G.qLen)) G.pLen) s
      (CandidateFinishAt G qvalue) := by
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
  refine WP.mono build fun a ⟨_, Oa, Ka⟩ => ?_
  rw [sa] at Oa
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
  exact ⟨R.arena.keep Ka (by decide), parentA, qA⟩

theorem pConstruct_ct {H : Hash} (K : HashOK H) (G : GenerationGeometry)
    (C : ContributionPlan) (qvalue : Nat) :
    RelCT isa (Two fun (_ : Unit) => PConstructInputs K G C qvalue)
      (pConstruct H G.pLen G.qLen) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨u, hs, ht⟩ es et
  have width : C.seed.length = 20 ∨ C.seed.length = 32 := by rw [hs.seedLength]; exact G.qWidth
  have hashes := pHashesShape_ct hs.layout width G.parent G.pLen
  rw [hs.seedLength, hs.count] at hashes
  have first := two_post (Φ := fun (_ : Unit) => PConstructInputs K G C qvalue)
    (Ψ := fun (_ : Unit) => CandidateFinishAt G qvalue)
    (hashes.mono (fun _ _ => two_mono (fun _ _ R => ⟨R.contributions, by rw [R.frame]; exact R.parent⟩))
      (fun _ _ h => h)) (fun _ _ R => pHashes_candidateReady R)
  exact (RelCT.seq first (candidateFinish_ct G qvalue hs.qPositive hs.qBound))
    s t ts tt s' t' ⟨u, hs, ht⟩ es et
end VG.Proof.Dsa.X86.Generation
