module

public import VerifiedGarbage.Proof.Dsa.AArch64.ValidateCT
import VerifiedGarbage.Proof.Dsa.AArch64.ParametersVerified
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingAgreement
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.ABIRegions
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
public import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.ValidateMain
public import VerifiedGarbage.Impl.Dsa.AArch64.Prevalidated
public import VerifiedGarbage.Proof.Dsa.AArch64.CoreSign
public import VerifiedGarbage.Proof.Dsa.AArch64.SignReleaseCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ValidateBody
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingInput
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingPublic
public import VerifiedGarbage.Spec.Dsa.Prevalidated

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
  omega

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
