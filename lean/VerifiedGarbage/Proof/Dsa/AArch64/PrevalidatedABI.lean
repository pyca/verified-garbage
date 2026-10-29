module

public import VerifiedGarbage.Impl.Dsa.AArch64.Prevalidated
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.AArch64.CallHeadCT
public import VerifiedGarbage.Proof.Dsa.AArch64.CoreSign
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState
public import VerifiedGarbage.Proof.Dsa.AArch64.SignReleaseCT
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingABI
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingPublic
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingReturn
public import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceBridge
public import VerifiedGarbage.Spec.Dsa.Prevalidated

import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedCT
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingABIPost
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingAgreement
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedBody
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.DomainWidths
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingShape
/-! # The prevalidated verifier meets its shared ABI and leakage contract -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/PrevalidatedReturn.lean`, which only this module imported.
section

/-! # Both verifying branches return the packed byte specification -/

section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem prevalidatedAccepted_ok (M : Mont) {p : VerifyingInput} {original s : State} (h : VerifyingPre p original)
    (hi : VerifyingInitialized p original h.pLength h.qLength s) (ha : p.accepted = true)
    (hv : Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key = true) :
    WP isa (prevalidatedBody M.mm) s (VerifyingPost p original) := by
  obtain ⟨pi, qi, hr, ho, hm, hf, hk⟩ := hi
  let L := (p.layout original h.pLength h.qLength).withInverses pi qi
  obtain ⟨hsize, hpodd, hqodd⟩ := p.shapeFacts ha
  have hpf : L.modulus ≤ 256 ^ L.pLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.components.p
    rw [p.components.pLength] at hh
    exact Nat.le_of_lt hh
  have hqf : L.subgroup ≤ 256 ^ L.qLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.components.q
    rw [p.components.qLength] at hh
    exact Nat.le_of_lt hh
  have hqn := VG.Proof.Dsa.subgroup_scan_width hsize
  have hkey : Spec.Dsa.publicKeyBytes L.pLen L.qLen p.key = p.values.key L := rfl
  refine WP.mono (prevalidatedBody_spec M (L := L) hr p.values ho hsize hpodd hqodd hpf hqf
    p.keyLength p.signatureLength hkey rfl rfl hqn rfl hv hm)
    fun t ⟨hret, hframe, hkeep⟩ => ?_
  exact ⟨hret,
    hf.trans (InScr.of_outside hframe (by decide)), (hk.trans hkeep).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/PrevalidatedMain.lean`, which only this module imported.
section

/-! # Functional correctness of the complete AArch64 DSA verification program -/

section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem prevalidatedSuccess_ok (M : Mont) {p : VerifyingInput} {original st : State} (h : VerifyingPre p original)
    (hs : VerifyingShapePost p original h.pLength h.qLength st) (ha : p.accepted = true)
    (hv : Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key = true) :
    WP isa (seqs [SignVerify.workspaces, Prevalidated.compute M.mm, .block SignVerify.result]) st
      (VerifyingPost p original) := by
  refine WP.seq (WP.mono (verifyingInitialize_ok h hs ha) fun t ht => ?_)
  exact prevalidatedAccepted_ok M h ht ha hv

theorem prevalidatedMain_ok (M : Mont) {p : VerifyingInput} {s0 : State} (h : VerifyingPre p s0)
    (hv : Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key = true) :
    WP isa (Prevalidated.verify M.mm) s0 (VerifyingPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (verifyingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => verifyingRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change some (s.gpr .x3 == (0#64)) = some true
    simp only [hs.branch, ha, Bool.not_false]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => prevalidatedSuccess_ok M h hs ha hv)
    change some (s.gpr .x3 == (0#64)) = some false
    simp only [hs.branch, ha, Bool.not_true]

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64 VG.Proof.Bignum.AArch64

theorem prevalidatedABI_of {s : State} (h : (Spec.Dsa.verifyPrevalidatedContract abi).pre s) :
    VerifyingABI s ∧ Spec.Dsa.validatePublicKeyBytes (s.gpr .x2).toNat (s.gpr .x3).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) = true := by
  sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs] at h
  sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs] at h
  sig_split h
  exact ⟨by constructor <;> with_reducible assumption, by assumption⟩

theorem prevalidatedPre_of {s : State} (h : (Spec.Dsa.verifyContract abi).pre s)
    (hv : Spec.Dsa.validatePublicKeyBytes (s.gpr .x2).toNat (s.gpr .x3).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) = true) :
    (Spec.Dsa.verifyPrevalidatedContract abi).pre s := by
  sig_pre [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs] at h
  sig_pre [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs] at h
  sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs]
  sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs]
  sig_split h
  sig_and_intros <;> with_reducible assumption

theorem prevalidatedSharedPost {s t : State} (h : VerifyingABI s) (hp : VerifyingPost h.input s t) :
    (Spec.Dsa.verifyPrevalidatedContract abi).post s t := by
  sig_post [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs]
  sig_post [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs]
  rw [hp.1, verifyStatus_u32]
  rfl

theorem prevalidatedCorrect (M : Mont)
    (s : State) (h : (Spec.Dsa.verifyPrevalidatedContract abi).pre s) :
    ∃ trace t, Exec isa (Prevalidated.verify M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.verifyPrevalidatedContract abi).post s t := by
  obtain ⟨ha, hv⟩ := prevalidatedABI_of h
  obtain ⟨trace, t, he, hp⟩ := prevalidatedMain_ok M ha.pre hv
  exact ⟨trace, t, he, abiPreserved_of_keep hp.2.2, prevalidatedSharedPost ha hp⟩

theorem prevalidatedConstantTime (M : Mont) : ConstantTime isa (Spec.Dsa.verifyPrevalidatedContract abi).pre
    (Spec.Dsa.verifyPrevalidatedContract abi).pub (Prevalidated.verify M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  change (Spec.Dsa.verifyContract abi).pub s₁ s₂ at hp
  exact (prevalidatedMain_ct M _ _ _ _ _ _
    (verifyingPublicRelated (prevalidatedABI_of h₁).1 (prevalidatedABI_of h₂).1 hp) e₁ e₂).1

end VG.Proof.Dsa.AArch64
