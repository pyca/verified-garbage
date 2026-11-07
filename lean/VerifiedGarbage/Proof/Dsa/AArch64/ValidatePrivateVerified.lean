module

public import VerifiedGarbage.Proof.Dsa.AArch64.ValidatePrivateCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.AArch64.ABIRegions
import VerifiedGarbage.Proof.Dsa.AArch64.ParametersVerified
import VerifiedGarbage.Proof.Dsa.AArch64.PublicSlices
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode

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
  omega

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
    have he := prefix_component_eq (offset := 0) (len := h₁.input.pLen) hpub (by omega)
    simp only [List.drop_zero] at he
    change h₁.input.key.take h₁.input.pLen = h₂.input.key.take h₂.input.pLen
    rw [← hp]
    exact he
  have hqb : h₁.input.components.q = h₂.input.components.q := by
    have he := prefix_component_eq (offset := h₁.input.pLen) (len := h₁.input.qLen) hpub (by omega)
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
