module

import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Restore
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Backend
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Geometry

/-! Read-only recognition constants do not alter the selected general validator. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

theorem plain_covers (s : State) : Covers ((plain s).rd ++ (plain s).wr) (s.rd ++ s.wr) :=
  (Covers.of_mem (fun _ h => List.mem_of_mem_take h)).append (Covers.refl _)

theorem fallback_run (v : RoundImpl) {s : State}
    (h : (Spec.Ffdh.checkDomainContract abi 8).pre (plain s)) :
    ∃ trace t, Exec isa (CheckDomain.domainCode v) s trace t ∧
      abiPreserved s t ∧ (Spec.Ffdh.checkDomainContract abi 8).post s t := by
  obtain ⟨trace, t, run, preserved, post⟩ := (CheckDomain.domainCode_verified v).1 (plain s) h
  have wide := VG.X86_64.Exec.widen run (rd := s.rd) (wr := s.wr)
    (plain_covers s) (Covers.refl _)
  refine ⟨trace, t.withRegions s.rd s.wr, ?_, preserved, post⟩
  simpa only [plain, stripConsts, State.withRegions_withRegions, State.withRegions_self] using wide

theorem fallback_ct (v : RoundImpl) :
    RelCT isa (fun s t =>
      (Spec.Ffdh.checkDomainContract abi 8).pre (plain s) ∧
      (Spec.Ffdh.checkDomainContract abi 8).pre (plain t) ∧
      (Spec.Ffdh.checkDomainContract abi 8).pub s t)
      (CheckDomain.domainCode v) (fun _ _ => True) := by
  intro s t ts tt u w ⟨hs, ht, hp⟩ es et
  obtain ⟨ts', u', eu, _, _⟩ := (CheckDomain.domainCode_verified v).1 (plain s) hs
  obtain ⟨tt', w', ew, _, _⟩ := (CheckDomain.domainCode_verified v).1 (plain t) ht
  have eus : Exec isa (CheckDomain.domainCode v) s ts' (u'.withRegions s.rd s.wr) := by
    simpa only [plain, stripConsts, State.withRegions_withRegions, State.withRegions_self] using
      (VG.X86_64.Exec.widen eu (rd := s.rd) (wr := s.wr) (plain_covers s) (Covers.refl _))
  have ewt : Exec isa (CheckDomain.domainCode v) t tt' (w'.withRegions t.rd t.wr) := by
    simpa only [plain, stripConsts, State.withRegions_withRegions, State.withRegions_self] using
      (VG.X86_64.Exec.widen ew (rd := t.rd) (wr := t.wr) (plain_covers t) (Covers.refl _))
  have sameS := (Exec.det es eus).1
  have sameT := (Exec.det et ewt).1
  refine ⟨?_, True.intro⟩
  rw [sameS, sameT]
  exact (CheckDomain.domainCode_verified v).2.1 _ _ _ _ _ _ hs ht hp eu ew

end VG.Proof.Ffdh.X86_64.VettedValidation
