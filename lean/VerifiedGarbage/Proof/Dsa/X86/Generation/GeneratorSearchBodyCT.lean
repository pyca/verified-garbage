module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorSearchCTState
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorBodyCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeSlice

/-! # Map the current public h-tape chunk to the generator body -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def generatorSearchCandidate (p : GeneratorSearchPublic) : GeneratorCandidatePublic :=
  ⟨⟨p.plan.frame, frameUpdate p.plan.saved 21 (p.plan.tapePtr + BitVec.ofNat 32 p.used)⟩,
    p.plan.tapePtr + BitVec.ofNat 32 p.used, p.plan.candidate p.used, (p.plan.core.modulus - 1) / p.plan.q⟩

theorem generatorSearch_bodyAt {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (H : GeneratorSearchTaken len p s) : GeneratorBodyAt p.plan.core (generatorSearchCandidate p) s := by
  obtain ⟨⟨W, R, _, pointer⟩, _, room⟩ := H
  have positive : 0 < p.plan.core.len := by have := p.plan.core.lenMin; omega
  have parent : (generatorSearchCandidate p).frame.words 5 = p.plan.parent := p.plan.savedParent
  refine ⟨?_, R.prepared, ⟨R.layout, ?_⟩, rfl, ?_, ?_, ?_,
    tape_pointer_fit p.plan.tapeBounds room positive, ?_, ?_, ?_, ?_⟩
  · rw [parent]; exact p.plan.layout
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact (R.representation 5 (by decide)).trans (R.fixed 5 (by decide) (by decide))
    · exact (R.representation 21 (by decide)).trans pointer
  · rw [parent]; exact p.plan.base
  · change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((p.plan.tapePtr + BitVec.ofNat 32 p.used).setWidth 64) p.plan.core.len) = _
    rw [tape_slice p.plan.tapeBounds room positive, R.tapeValue]
    rfl
  · rw [parent]; exact R.exponentValue
  · intro d hd
    exact tape_slice_read p.plan.tapeBounds room positive R.tapeRead hd
  · exact (p.plan.tapeSeparate ⟨p.plan.core.base, p.plan.core.size⟩ (by simp [generatorSearchWrites])).sub_left
      (tape_slice_sub p.plan.tapeBounds room positive)
  · rw [parent]; exact R.exponentRead
  · rw [parent]; exact R.outputWrite

theorem generatorSearch_body_ct (len : Nat) : RelCT isa (Two (GeneratorSearchTaken len))
    (generatorBody len) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨p, hs, ht⟩ es et
  have CT := generatorBody_ct p.plan.core
  rw [hs.2.1] at CT
  exact CT s t ts tt s' t' ⟨generatorSearchCandidate p, generatorSearch_bodyAt hs, generatorSearch_bodyAt ht⟩ es et
end VG.Proof.Dsa.X86.Generation
