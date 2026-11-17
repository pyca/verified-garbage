module

public import VerifiedGarbage.Proof.Dsa.AArch64.Backend
public import VerifiedGarbage.Proof.Bignum.AArch64.MulFixedCallMont
public import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedSignVerified
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingVerified
public import VerifiedGarbage.Impl.Dsa.AArch64.Prevalidated
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.AArch64.CallHeadCT
public import VerifiedGarbage.Proof.Dsa.AArch64.CoreSign
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState
public import VerifiedGarbage.Proof.Dsa.AArch64.SignReleaseCT
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingABI
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingPublic
public import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceBridge
public import VerifiedGarbage.Spec.Dsa.Prevalidated
import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedBody
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.DomainWidths
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingInitialize
public import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCheckedVerified
import Mathlib.Data.Nat.Basic
public import VerifiedGarbage.Proof.Dsa.AArch64.ValidateCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ParametersVerified
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.ABIRegions
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.AArch64.ValidateMain
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingInput
public import VerifiedGarbage.Proof.Dsa.AArch64.ValidatePrivateCT
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.AArch64.PublicSlices
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightGuard
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightGuardCT
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMont

/-! ### `Dsa.AArch64.PrevalidatedVerified`, which only this module used -/

section

/-! ### `Dsa.AArch64.PrevalidatedABI`, which only this module used -/

section

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

end

end


/-! # Verified DSA signature checking under the merged immutable-key precondition -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64 VG.Proof.Bignum.AArch64

def prevalidatedSatState : State where
  gpr := (verifyingSatState).gpr
  sp := (verifyingSatState).sp
  rd := (verifyingSatState).rd
  wr := (verifyingSatState).wr
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x2194 then
    validatedSatKey[a.toNat - 0x2000]?.getD 0 else (verifyingSatState).mem a

theorem prevalidatedSatisfiable : ∃ s, (Spec.Dsa.verifyPrevalidatedContract abi).pre s := by
  have hb : Spec.Rsa.bytesAt (prevalidatedSatState).mem 0x2000 404 = validatedSatKey :=
    VG.Proof.Dsa.bytesAt_of_list (lo := 0x2000) (by decide +kernel) (by decide) fun a h1 h2 => by
      have h : 0x2000 ≤ a.toNat ∧ a.toNat < 0x2194 := ⟨h1, h2⟩
      simp only [prevalidatedSatState, h, and_self, ↓reduceIte]
  have hv : Spec.Dsa.validatePublicKeyBytes 128 20
      (Spec.Rsa.bytesAt (prevalidatedSatState).mem 0x2000 404) = true := by
    rw [hb]; exact validatedSatKey_valid
  have ho : ∃ s, (Spec.Dsa.verifyContract abi).pre s ∧ s = prevalidatedSatState := by
    refine ⟨prevalidatedSatState, ?_, rfl⟩
    sig_pre [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs]
    sig_and_intros
    all_goals first
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
      | (intro a h₁ h₂
         sig_simp_only [Region.Contains, prevalidatedSatState, verifyingSatState,
           stackArg, stackArgAddr, Mem.readW, Mem.read] at h₁ h₂
         bv_omega)
  refine ⟨prevalidatedSatState, prevalidatedPre_of ?_ hv⟩
  obtain ⟨s, h, rfl⟩ := ho
  exact h

theorem prevalidated_verified (M : Mont) :
    Verified target (Prevalidated.verify M.mm) (Spec.Dsa.verifyPrevalidatedContract abi) :=
  ⟨prevalidatedCorrect M, prevalidatedConstantTime M, prevalidatedSatisfiable⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.ValidateVerified`, which only this module used -/

section

/-! # The AArch64 DSA domain check verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64


structure ValidatingABI (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩]
  wr : s.wr = [⟨s.gpr .x4, (s.gpr .x5).toNat * 8⟩]
  keyScratch : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x4, (s.gpr .x5).toNat * 8⟩
  keyBound : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  scratchBound : (s.gpr .x4).toNat + (s.gpr .x5).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .x2).toNat (s.gpr .x3).toNat
  keyLength : (s.gpr .x1).toNat = 3 * (s.gpr .x2).toNat + (s.gpr .x3).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .x2).toNat ≤ (s.gpr .x5).toNat

theorem validatingABI_of {s : State} (h : (Spec.Dsa.validatePublicKeyContract abi).pre s) : ValidatingABI s := by
  sig_pre [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argRegs, stackArgs_zero] at h
  sig_split h
  constructor <;> with_reducible assumption

def ValidatingABI.input {s : State} (h : ValidatingABI s) : VerifyingInput where
  base := s.gpr .x4
  digestPointer := 0
  signature := List.replicate (2 * (s.gpr .x3).toNat) 0
  digest := []
  signatureLength := List.length_replicate
  digestBound := by decide
  pLen := (s.gpr .x2).toNat
  qLen := (s.gpr .x3).toNat
  key := Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat
  lengths := h.lengths
  keyLength := (bytesAt_length _ _ _).trans h.keyLength

theorem ValidatingABI.used {s : State} (h : ValidatingABI s) : usedBytes ≤ (s.gpr .x5).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 15712 ≤ _
  omega_using [hl, hs]

theorem ValidatingABI.pre {s : State} (h : ValidatingABI s) : ValidatingPre h.input s := by
  have hs : Scr s (s.gpr .x4) ((s.gpr .x5).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  exact ⟨scratch_prefix hs h.used (by decide), (ofNat_toNat64 _).symm, (ofNat_toNat64 _).symm, rfl,
    source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x1).isLt) h.keyScratch) h.used, rfl, rfl⟩

def ValidatingABI.call {s : State} (h : ValidatingABI s) : ValidatingCall := ⟨h.input, s, h.pre⟩

theorem validatingPreserved {s t : State} (h : ValidatingABI s) (hp : ValidatingPost h.input s t) :
    abiPreserved s t := by
  exact abiPreserved_of_keep hp.2.2

theorem validatingSharedPost {s t : State} (h : ValidatingABI s) (hp : ValidatingPost h.input s t) :
    (Spec.Dsa.validatePublicKeyContract abi).post s t := by
  sig_post [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argRegs, stackArgs_zero]
  rw [hp.1]
  change _ = if Spec.Dsa.validatePublicKeyBytes h.input.pLen h.input.qLen h.input.key = true then 1 else 0
  cases Spec.Dsa.validatePublicKeyBytes h.input.pLen h.input.qLen h.input.key <;> rfl

theorem validatingCorrect (M : Mont)
    (s : State) (h : (Spec.Dsa.validatePublicKeyContract abi).pre s) :
    ∃ trace t, Exec isa (Prevalidated.validate M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.validatePublicKeyContract abi).post s t := by
  have ha := validatingABI_of h
  obtain ⟨trace, t, he, hp⟩ := validatingMain_ok M ha.pre
  exact ⟨trace, t, he, validatingPreserved ha hp, validatingSharedPost ha hp⟩

theorem validatingPublicRelated {s₁ s₂ : State} (h₁ : ValidatingABI s₁) (h₂ : ValidatingABI s₂)
    (h : (Spec.Dsa.validatePublicKeyContract abi).pub s₁ s₂) : Two ValidatingStart s₁ s₂ := by
  sig_pub [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argRegs, stackArgs_zero] at h
  obtain ⟨hsp, hl, hdi, _, hdx, hcx, h8, _⟩ := h
  have hb := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl
  have hp : h₁.input.pLen = h₂.input.pLen := congrArg BitVec.toNat hdx
  have hq : h₁.input.qLen = h₂.input.qLen := congrArg BitVec.toNat hcx
  have hkey : h₁.input.key = h₂.input.key := by
    change (h₁.input.key.take (3 * h₁.input.pLen + h₁.input.qLen)) =
      (h₂.input.key.take (3 * h₂.input.pLen + h₂.input.qLen)) at hb
    simpa only [← h₁.input.keyLength, ← h₂.input.keyLength, List.take_length] using hb
  have hpb : h₁.input.components.p = h₂.input.components.p := by
    change h₁.input.key.take h₁.input.pLen = h₂.input.key.take h₂.input.pLen
    rw [hkey, hp]
  have hqb : h₁.input.components.q = h₂.input.components.q := by
    change (h₁.input.key.drop h₁.input.pLen).take h₁.input.qLen =
      (h₂.input.key.drop h₂.input.pLen).take h₂.input.qLen
    rw [hkey, hp, hq]
  have hlayout : h₁.call.layout = h₂.call.layout :=
    verifyingLayout_eq h8 hp hq rfl rfl hpb hqb hdi hdx h8 hcx
  exact ⟨h₂.call, ⟨h₁.call, ⟨hlayout, hkey⟩, rfl⟩, ⟨h₂.call, ⟨rfl, rfl⟩, rfl⟩, hsp⟩

theorem validatingConstantTime (M : Mont) :
    ConstantTime isa (Spec.Dsa.validatePublicKeyContract abi).pre
      (Spec.Dsa.validatePublicKeyContract abi).pub (Prevalidated.validate M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (validatingMain_ct M _ _ _ _ _ _
    (validatingPublicRelated (validatingABI_of h₁) (validatingABI_of h₂) hp) e₁ e₂).1

/-- An ordinary 1024/160 call with disjoint buffers. The all-zero domain is
allowed by the contract and rejected by the program. -/
def validatingSatState : State where
  gpr r := match r with
    | .x0 => 0x2000 | .x1 => 404 | .x2 => 128 | .x3 => 20
    | .x4 => 0x8000 | .x5 => 2048 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 404⟩]
  wr := [⟨0x8000, 16384⟩]

theorem validatingSatisfiable : ∃ s, (Spec.Dsa.validatePublicKeyContract abi).pre s := by
  sig_implies_sat [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argRegs, stackArgs_zero]
    [validatingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using validatingSatState

theorem validating_verified (M : Mont)
    :
    Verified target (Prevalidated.validate M.mm) (Spec.Dsa.validatePublicKeyContract abi) :=
  ⟨validatingCorrect M, validatingConstantTime M, validatingSatisfiable⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.ValidatePrivateVerified`, which only this module used -/

section

/-! # The AArch64 DSA private-key validator verified against its contract -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure PrivateABI (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩]
  wr : s.wr = [⟨s.gpr .x4, (s.gpr .x5).toNat * 8⟩]
  keyScratch : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x4, (s.gpr .x5).toNat * 8⟩
  keyBound : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  scratchBound : (s.gpr .x4).toNat + (s.gpr .x5).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .x2).toNat (s.gpr .x3).toNat
  keyLength : (s.gpr .x1).toNat = 3 * (s.gpr .x2).toNat + 2 * (s.gpr .x3).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .x2).toNat ≤ (s.gpr .x5).toNat

theorem privateABI_of {s : State} (h : (Spec.Dsa.validatePrivateKeyContract abi).pre s) : PrivateABI s := by
  sig_pre [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs, stackArgs_zero] at h
  sig_split h
  constructor <;> with_reducible assumption

def PrivateABI.input {s : State} (h : PrivateABI s) : PrivateInput where
  base := s.gpr .x4
  pLen := (s.gpr .x2).toNat
  qLen := (s.gpr .x3).toNat
  key := Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat
  lengths := h.lengths
  keyLength := (bytesAt_length _ _ _).trans h.keyLength

theorem PrivateABI.used {s : State} (h : PrivateABI s) : usedBytes ≤ (s.gpr .x5).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 15712 ≤ _
  omega_using [hl, hs]

theorem PrivateABI.pre {s : State} (h : PrivateABI s) : PrivatePre h.input s := by
  have hs : Scr s (s.gpr .x4) ((s.gpr .x5).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  exact ⟨scratch_prefix hs h.used (by decide), rfl, (ofNat_toNat64 _).symm, (ofNat_toNat64 _).symm,
    source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x1).isLt) h.keyScratch) h.used⟩

def PrivateABI.call {s : State} (h : PrivateABI s) : PrivateCall := ⟨h.input, s, h.pre⟩

theorem privateSharedPost {s t : State} (h : PrivateABI s) (hp : PrivatePost h.input s t) :
    (Spec.Dsa.validatePrivateKeyContract abi).post s t := by
  sig_post [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs, stackArgs_zero]
  rw [hp.1]
  change _ = if Spec.Dsa.validatePrivateKeyBytes h.input.pLen h.input.qLen h.input.key = true then 1 else 0
  cases Spec.Dsa.validatePrivateKeyBytes h.input.pLen h.input.qLen h.input.key <;> rfl

theorem validatingPrivateCorrect (M : Mont)
    (s : State) (h : (Spec.Dsa.validatePrivateKeyContract abi).pre s) :
    ∃ trace t, Exec isa (PrevalidatedSign.validate M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.validatePrivateKeyContract abi).post s t := by
  have ha := privateABI_of h
  obtain ⟨trace, t, he, hp⟩ := privateMain_ok M ha.pre
  exact ⟨trace, t, he, abiPreserved_of_keep hp.2.2, privateSharedPost ha hp⟩

theorem privatePublicRelated {s₁ s₂ : State} (h₁ : PrivateABI s₁) (h₂ : PrivateABI s₂)
    (h : (Spec.Dsa.validatePrivateKeyContract abi).pub s₁ s₂) : Two PrivateStart s₁ s₂ := by
  sig_pub [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs,
    stackArgs_zero] at h
  obtain ⟨hsp, hl, hdi, _, hdx, hcx, h8, _⟩ := h
  have hpubl := (List.append_inj' hl (List.length_singleton.trans List.length_singleton.symm)).1
  have hb := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hpubl
  have hp : h₁.input.pLen = h₂.input.pLen := congrArg BitVec.toNat hdx
  have hq : h₁.input.qLen = h₂.input.qLen := congrArg BitVec.toNat hcx
  have hpub : h₁.input.key.take (3 * h₁.input.pLen + h₁.input.qLen) =
      h₂.input.key.take (3 * h₁.input.pLen + h₁.input.qLen) := by
    have hb' : h₁.input.key.take (3 * h₁.input.pLen + h₁.input.qLen) =
        h₂.input.key.take (3 * h₂.input.pLen + h₂.input.qLen) := hb
    rw [← hp, ← hq] at hb'
    exact hb'
  have hpb : h₁.input.components.p = h₂.input.components.p := by
    have he := prefix_component_eq (offset := 0) (len := h₁.input.pLen) hpub (by omega_using [])
    simp only [List.drop_zero] at he
    change h₁.input.key.take h₁.input.pLen = h₂.input.key.take h₂.input.pLen
    rw [← hp]
    exact he
  have hqb : h₁.input.components.q = h₂.input.components.q := by
    have he := prefix_component_eq (offset := h₁.input.pLen) (len := h₁.input.qLen) hpub (by omega_using [])
    change (h₁.input.key.drop h₁.input.pLen).take h₁.input.qLen =
      (h₂.input.key.drop h₂.input.pLen).take h₂.input.qLen
    rw [← hp, ← hq]
    exact he
  have hac : h₁.input.accepted = h₂.input.accepted := by
    unfold PrivateInput.accepted
    congr 1
  have hlayout : h₁.call.layout = h₂.call.layout := by
    change h₁.input.layout s₁ _ _ = h₂.input.layout s₂ _ _
    unfold PrivateInput.layout
    have hf : privateFieldValues s₁ h₁.input.accepted = privateFieldValues s₂ h₂.input.accepted := by
      funext f
      cases f <;> simp only [privateFieldValues, hdi, hdx, hcx, hac]
    congr 1
    · exact congrArg Spec.Dsa.decodeBE hpb
    · exact congrArg Spec.Dsa.decodeBE hqb
  exact ⟨h₂.call, ⟨h₁.call, ⟨hlayout, hpb, hqb⟩, rfl⟩, ⟨h₂.call, ⟨rfl, rfl, rfl⟩, rfl⟩, hsp⟩

theorem validatingPrivateConstantTime (M : Mont) :
    ConstantTime isa (Spec.Dsa.validatePrivateKeyContract abi).pre
      (Spec.Dsa.validatePrivateKeyContract abi).pub (PrevalidatedSign.validate M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (privateMain_ct M _ _ _ _ _ _
    (privatePublicRelated (privateABI_of h₁) (privateABI_of h₂) hp) e₁ e₂).1

/-- An ordinary 1024/160 call with disjoint buffers. The all-zero key is
allowed by the contract and rejected by the program. -/
def privateSatState : State where
  gpr r := match r with
    | .x0 => 0x2000 | .x1 => 424 | .x2 => 128 | .x3 => 20
    | .x4 => 0x8000 | .x5 => 2048 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 424⟩]
  wr := [⟨0x8000, 16384⟩]

theorem validatingPrivateSatisfiable : ∃ s, (Spec.Dsa.validatePrivateKeyContract abi).pre s := by
  sig_implies_sat [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs,
    stackArgs_zero] [privateSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using privateSatState

theorem validating_private_verified (M : Mont) :
    Verified target (PrevalidatedSign.validate M.mm) (Spec.Dsa.validatePrivateKeyContract abi) :=
  ⟨validatingPrivateCorrect M, validatingPrivateConstantTime M, validatingPrivateSatisfiable⟩

end VG.Proof.Dsa.AArch64

end

end


/-!
# DSA with the shared AArch64 Montgomery arithmetic backend: the variant's code and proofs

The variant `VG.Variants.DsaArithmetic.AArch64.Base.variant`
(`Variants/DsaArithmetic/AArch64/Base.lean`), with the proofs its interface
asks for. Its repeated products call their fixed-index helpers
(`vg_rsa_mul_{o}_{a}_{b}`, `Mont.calledProductEight`) rather than each
inlining the eight-limb kernel.
-/

@[expose] public section

namespace VG.Proof.Variants.DsaArithmetic.AArch64.Base

open VG VG.AArch64 VG.Proof.Dsa.AArch64 VG.Proof.Bignum.AArch64

open VG.Impl.Dsa.AArch64 in
/-- What the kernel evaluates of the eight entry points: that none writes the
stack pointer, the stack of those that call, and that those that run under
DIT do not touch it. One declaration states it of all of them, since the
kernel remembers what it has evaluated only within a declaration, and they
are built of the same code (the arithmetic they call, and most of what is
around it). -/
theorem checks :
    (([Prevalidated.validate Mont.calledProductEight.mm, Prevalidated.verify Mont.calledProductEight.mm,
      Generate.checkParameters Mont.calledProductEight.mm, Generate.deriveKey Mont.calledProductEight.mm,
      SignVerify.sign Mont.calledProductEight.mm, PrevalidatedSign.sign Mont.calledProductEight.mm,
      PrevalidatedSign.validate Mont.calledProductEight.mm,
      Generate.deriveChecked Mont.calledProductEight.mm].all fun c => c.all (fun i => !isa.writesSp i)) &&
    (([Generate.checkParameters Mont.calledProductEight.mm, Generate.deriveKey Mont.calledProductEight.mm,
      SignVerify.sign Mont.calledProductEight.mm, PrevalidatedSign.sign Mont.calledProductEight.mm,
      Generate.deriveChecked Mont.calledProductEight.mm].all fun c => Nat.ble (16 * c.aarch64Depth) 0) &&
    ([Generate.checkParameters Mont.calledProductEight.mm, SignVerify.sign Mont.calledProductEight.mm,
      PrevalidatedSign.sign Mont.calledProductEight.mm,
      Generate.deriveChecked Mont.calledProductEight.mm].all fun c => c.all (fun i => !i.touchesDit)))) = true := by
  decide +kernel

/-- Entry point `k` of `checks` does not write the stack pointer. -/
theorem checks_sp {l l' l'' : List (Prog isa)}
    (h : ((l.all fun c => c.all (fun i => !isa.writesSp i)) &&
      ((l'.all fun c => Nat.ble (16 * c.aarch64Depth) 0) &&
      (l''.all fun c => c.all (fun i => !i.touchesDit)))) = true)
    (k : Nat) (hk : k < l.length) : (l[k]'hk).all (fun i => !isa.writesSp i) = true :=
  List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1 _ (List.getElem_mem hk)

/-- The stack of entry point `k` of those of `checks` that call. -/
theorem checks_depth {l l' l'' : List (Prog isa)}
    (h : ((l.all fun c => c.all (fun i => !isa.writesSp i)) &&
      ((l'.all fun c => Nat.ble (16 * c.aarch64Depth) 0) &&
      (l''.all fun c => c.all (fun i => !i.touchesDit)))) = true)
    (k : Nat) (hk : k < l'.length) : 16 * (l'[k]'hk).aarch64Depth ≤ 0 :=
  Nat.le_of_ble_eq_true (List.all_eq_true.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1 _ (List.getElem_mem hk))

/-- Entry point `k` of those of `checks` that run under DIT does not touch it. -/
theorem checks_dit {l l' l'' : List (Prog isa)}
    (h : ((l.all fun c => c.all (fun i => !isa.writesSp i)) &&
      ((l'.all fun c => Nat.ble (16 * c.aarch64Depth) 0) &&
      (l''.all fun c => c.all (fun i => !i.touchesDit)))) = true)
    (k : Nat) (hk : k < l''.length) : (l''[k]'hk).all (fun i => !i.touchesDit) = true :=
  List.all_eq_true.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2 _ (List.getElem_mem hk)

def variant : Backend where
  mul := Mont.calledProductEight.mm
  suffix := ""
  features := []
  signVerified := signing_verified Mont.calledProductEight
  validateVerified := validating_verified Mont.calledProductEight
  prevalidatedVerified := prevalidated_verified Mont.calledProductEight
  validateSp := checks_sp checks 0 (by decide)
  prevalidatedSp := checks_sp checks 1 (by decide)
  parametersVerified := parameters_verified Mont.calledProductEight
  deriveVerified := derive_verified Mont.calledProductEight
  parametersSp := checks_sp checks 2 (by decide)
  parametersNoDit := checks_dit checks 0 (by decide)
  parametersDepth := checks_depth checks 0 (by decide)
  deriveSp := checks_sp checks 3 (by decide)
  deriveDepth := checks_depth checks 1 (by decide)
  signSp := checks_sp checks 4 (by decide)
  signNoDit := checks_dit checks 1 (by decide)
  signDepth := checks_depth checks 2 (by decide)
  prevalidatedSignVerified := prevalidated_sign_verified Mont.calledProductEight
  prevalidatedSignSp := checks_sp checks 5 (by decide)
  prevalidatedSignNoDit := checks_dit checks 2 (by decide)
  prevalidatedSignDepth := checks_depth checks 3 (by decide)
  validatePrivateVerified := validating_private_verified Mont.calledProductEight
  validatePrivateSp := checks_sp checks 6 (by decide)
  deriveCheckedVerified := derive_checked_verified Mont.calledProductEight
  deriveCheckedSp := checks_sp checks 7 (by decide)
  deriveCheckedNoDit := checks_dit checks 3 (by decide)
  deriveCheckedDepth := checks_depth checks 4 (by decide)
  stackBound := by decide

end VG.Proof.Variants.DsaArithmetic.AArch64.Base
