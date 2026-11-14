module

import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Geometry
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Recognize
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Facts
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-! ### `Ffdh.PPC64LE.VettedValidation.Fallback`, which only this module used -/

section

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

end

end


/-! Certified recognition success, with the complete original validator on every miss. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation VG.Impl.Ffdh.VettedGroups

theorem Result.pre {s t : State} (h : Result s t) (pre : contract.pre s) :
    (Spec.Ffdh.checkDomainContract abi).pre (plain t) := by
  have base := (pre_plain pre).1
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs] at base ⊢
  rw [h.keep.gpr (r := .r3) (by decide), h.keep.gpr (r := .r4) (by decide),
    h.keep.gpr (r := .r5) (by decide), h.keep.gpr (r := .r6) (by decide),
    h.keep.gpr (r := .r7) (by decide), h.keep.2.1, h.keep.2.2]
  exact base

private theorem post_shared {s t : State} (h : Domain.cdContract.post s t) : contract.post s t := by
  change (Spec.Ffdh.checkDomainContract abi).post s t
  sig_post [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs]
  exact h

theorem correct (s : State) (pre : contract.pre s) :
    WP isa code s fun t => abiPreserved s t ∧ contract.post s t := by
  rw [code, WP.seq_iff]
  obtain ⟨tr, u, run, result⟩ := recognize_ok pre
  refine ⟨tr, u, run, ?_⟩
  have sp : u.sp = s.sp := Exec.sp run
  have preserved : abiPreserved s u := ⟨fun r hr => result.keep.gpr (by revert r; decide), sp, result.lr⟩
  refine WP.ite (recognized s != 0) (by
    rw [VG.Proof.RsaPkcs1Sig.PPC64LE.eval_nonzero, result.value]) ?_ ?_
  · intro hit
    have nonzero : recognized s ≠ 0 := by simpa only [bne_iff_ne] using hit
    have raw : recognizeList groups (s.gpr .r5).toNat (domain s) ≠ 0 := by
      intro bad
      exact nonzero (by unfold recognized; rw [bad]; rfl)
    have valid := VG.Proof.Ffdh.VettedValidation.recognized_domain_valid groups
      (fun _ hg => hg) (context pre).shape raw
    refine VG.Proof.RsaPkcs1Sig.PPC64LE.wp_li (by decide) fun t only value =>
      VG.Proof.RsaPkcs1Sig.PPC64LE.wp_nil ⟨?_, post_shared ?_⟩
    · exact ⟨fun r hr => (only.gpr r (by revert r; decide)).trans (preserved.1 r hr),
        only.sp.trans preserved.2.1, only.lr.trans preserved.2.2⟩
    · change ((t.gpr .r3).setWidth 32).toNat = if Spec.Ffdh.domainValid
        (s.gpr .r5).toNat (domain s) then 1 else 0
      rw [value, valid]
      rfl
  · intro _
    obtain ⟨tr, t, run, kept, post⟩ := fallback_run (result.pre pre)
    refine ⟨tr, t, run, ⟨fun r hr => (kept.1 r hr).trans (preserved.1 r hr),
      kept.2.1.trans preserved.2.1, kept.2.2.trans preserved.2.2⟩, ?_⟩
    change (Spec.Ffdh.checkDomainContract abi).post s t
    change (Spec.Ffdh.checkDomainContract abi).post u t at post
    sig_post [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs] at post ⊢
    rw [result.keep.gpr (r := .r3) (by decide), result.keep.gpr (r := .r4) (by decide),
      result.keep.gpr (r := .r5) (by decide), result.mem] at post
    exact post

end VG.Proof.Ffdh.PPC64LE.VettedValidation
