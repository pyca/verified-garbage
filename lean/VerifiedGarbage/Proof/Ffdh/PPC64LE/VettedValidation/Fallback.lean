module

import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Geometry
public import VerifiedGarbage.Proof.Framework.RelCT

/-! Read-only recognition constants do not alter the selected general validator. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE

theorem plain_covers (s : State) : Covers ((plain s).rd ++ (plain s).wr) (s.rd ++ s.wr) :=
  (Covers.of_mem (fun _ h => List.mem_of_mem_take h)).append (Covers.refl _)

theorem fallback_run {s : State}
    (h : (Spec.Ffdh.checkDomainContract abi).pre (plain s)) :
    ∃ trace t, Exec isa VG.Impl.Ffdh.PPC64LE.Domain.checkDomain s trace t ∧
      abiPreserved s t ∧ (Spec.Ffdh.checkDomainContract abi).post s t := by
  obtain ⟨trace, t, run, preserved, post⟩ := Domain.cd_verified.1 (plain s) h
  have wide := VG.PPC64LE.Exec.widen run (rd := s.rd) (wr := s.wr)
    (plain_covers s) (Covers.refl _)
  refine ⟨trace, t.withRegions s.rd s.wr, ?_, preserved, post⟩
  simpa only [plain, stripConsts, State.withRegions_withRegions, State.withRegions_self] using wide

theorem fallback_ct :
    RelCT isa (fun s t =>
      (Spec.Ffdh.checkDomainContract abi).pre (plain s) ∧
      (Spec.Ffdh.checkDomainContract abi).pre (plain t) ∧
      (Spec.Ffdh.checkDomainContract abi).pub s t)
      VG.Impl.Ffdh.PPC64LE.Domain.checkDomain (fun _ _ => True) := by
  intro s t ts tt u w ⟨hs, ht, hp⟩ es et
  obtain ⟨ts', u', eu, _, _⟩ := Domain.cd_verified.1 (plain s) hs
  obtain ⟨tt', w', ew, _, _⟩ := Domain.cd_verified.1 (plain t) ht
  have eus : Exec isa VG.Impl.Ffdh.PPC64LE.Domain.checkDomain s ts' (u'.withRegions s.rd s.wr) := by
    simpa only [plain, stripConsts, State.withRegions_withRegions, State.withRegions_self] using
      (VG.PPC64LE.Exec.widen eu (rd := s.rd) (wr := s.wr) (plain_covers s) (Covers.refl _))
  have ewt : Exec isa VG.Impl.Ffdh.PPC64LE.Domain.checkDomain t tt' (w'.withRegions t.rd t.wr) := by
    simpa only [plain, stripConsts, State.withRegions_withRegions, State.withRegions_self] using
      (VG.PPC64LE.Exec.widen ew (rd := t.rd) (wr := t.wr) (plain_covers t) (Covers.refl _))
  have sameS := (Exec.det es eus).1
  have sameT := (Exec.det et ewt).1
  refine ⟨?_, True.intro⟩
  rw [sameS, sameT]
  exact Domain.cd_verified.2.1 _ _ _ _ _ _ hs ht hp eu ew

end VG.Proof.Ffdh.PPC64LE.VettedValidation
