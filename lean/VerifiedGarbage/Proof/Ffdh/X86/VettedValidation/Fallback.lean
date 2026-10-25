module

import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Geometry
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.X86.CheckDomainVerified

/-! Read-only recognition constants do not alter the selected general validator. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86

theorem fallback_run {s : State}
    (h : (Spec.Ffdh.checkDomainContract abi 172).pre (plain s)) :
    ∃ trace t, Exec isa VG.Impl.Ffdh.X86.CheckDomain.code s trace t ∧
      abiPreserved s t ∧ (Spec.Ffdh.checkDomainContract abi 172).post s t := by
  obtain ⟨trace, t, run, preserved, post⟩ := CheckDomain.verified.1 (plain s) h
  have wide := VG.X86.Exec.widen run (rd := s.rd) (wr := s.wr)
    (plain_covers s) (Covers.refl _)
  refine ⟨trace, t.withRegions s.rd s.wr, ?_, preserved, post⟩
  simpa only [plain, stripConsts, State.withRegions_withRegions, State.withRegions_self] using wide

theorem fallback_ct :
    RelCT isa (fun s t =>
      (Spec.Ffdh.checkDomainContract abi 172).pre (plain s) ∧
      (Spec.Ffdh.checkDomainContract abi 172).pre (plain t) ∧
      (Spec.Ffdh.checkDomainContract abi 172).pub s t)
      VG.Impl.Ffdh.X86.CheckDomain.code (fun _ _ => True) := by
  intro s t ts tt u w ⟨hs, ht, hp⟩ es et
  obtain ⟨ts', u', eu, _, _⟩ := CheckDomain.verified.1 (plain s) hs
  obtain ⟨tt', w', ew, _, _⟩ := CheckDomain.verified.1 (plain t) ht
  have eus : Exec isa VG.Impl.Ffdh.X86.CheckDomain.code s ts' (u'.withRegions s.rd s.wr) := by
    simpa only [plain, stripConsts, State.withRegions_withRegions, State.withRegions_self] using
      (VG.X86.Exec.widen eu (rd := s.rd) (wr := s.wr) (plain_covers s) (Covers.refl _))
  have ewt : Exec isa VG.Impl.Ffdh.X86.CheckDomain.code t tt' (w'.withRegions t.rd t.wr) := by
    simpa only [plain, stripConsts, State.withRegions_withRegions, State.withRegions_self] using
      (VG.X86.Exec.widen ew (rd := t.rd) (wr := t.wr) (plain_covers t) (Covers.refl _))
  have sameS := (Exec.det es eus).1
  have sameT := (Exec.det et ewt).1
  refine ⟨?_, True.intro⟩
  rw [sameS, sameT]
  exact CheckDomain.verified.2.1 _ _ _ _ _ _ hs ht hp eu ew

end VG.Proof.Ffdh.X86.VettedValidation
