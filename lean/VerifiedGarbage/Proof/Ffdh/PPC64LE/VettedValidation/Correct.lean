module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Fallback
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Recognize
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Facts
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

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
