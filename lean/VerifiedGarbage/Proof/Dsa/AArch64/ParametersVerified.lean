module

public import VerifiedGarbage.Proof.Dsa.AArch64.ParametersCT
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.ABIRegions
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.Contract

/-! # The AArch64 DSA domain check verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem stackArgs_zero (s : State) : List.map (stackArg s) (List.range 0) = [] := rfl

structure ParametersABI (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩]
  wr : s.wr = [⟨s.gpr .x4, (s.gpr .x5).toNat * 8⟩]
  paramsScratch : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x4, (s.gpr .x5).toNat * 8⟩
  paramsBound : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  scratchBound : (s.gpr .x4).toNat + (s.gpr .x5).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .x2).toNat (s.gpr .x3).toNat
  paramsLength : (s.gpr .x1).toNat = 2 * (s.gpr .x2).toNat + (s.gpr .x3).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .x2).toNat ≤ (s.gpr .x5).toNat

theorem parametersABI_of {s : State} (h : (Proof.Dsa.checkParametersContract abi).pre s) : ParametersABI s := by
  sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero] at h
  sig_split h
  constructor <;> with_reducible assumption

def ParametersABI.input {s : State} (h : ParametersABI s) : ParametersInput where
  base := s.gpr .x4
  pLen := (s.gpr .x2).toNat
  qLen := (s.gpr .x3).toNat
  params := Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat
  lengths := h.lengths
  paramsLength := (bytesAt_length _ _ _).trans h.paramsLength

theorem ParametersABI.used {s : State} (h : ParametersABI s) : usedBytes ≤ (s.gpr .x5).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 15712 ≤ _
  omega

theorem ParametersABI.pre {s : State} (h : ParametersABI s) : ParametersPre h.input s := by
  have hs : Scr s (s.gpr .x4) ((s.gpr .x5).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  exact ⟨scratch_prefix hs h.used (by decide), rfl, (ofNat_toNat64 _).symm, (ofNat_toNat64 _).symm,
    source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x1).isLt) h.paramsScratch) h.used⟩

def ParametersABI.call {s : State} (h : ParametersABI s) : ParametersCall := ⟨h.input, s, h.pre⟩

theorem parametersPreserved {s t : State} (h : ParametersABI s) (hp : ParametersPost h.input s t) :
    abiPreserved s t := by
  exact abiPreserved_of_keep hp.2.2

theorem parametersSharedPost {s t : State} (h : ParametersABI s) (hp : ParametersPost h.input s t) :
    (Proof.Dsa.checkParametersContract abi).post s t := by
  sig_post [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero]
  rw [hp.1]
  change _ = if Spec.Dsa.checkParametersBytes h.input.pLen h.input.qLen h.input.params = true then 1 else 0
  cases Spec.Dsa.checkParametersBytes h.input.pLen h.input.qLen h.input.params <;> rfl

theorem parametersCorrect (M : Mont)
    (s : State) (h : (Proof.Dsa.checkParametersContract abi).pre s) :
    ∃ trace t, Exec isa (Generate.checkParameters M.mm) s trace t ∧ abiPreserved s t ∧
      (Proof.Dsa.checkParametersContract abi).post s t := by
  have ha := parametersABI_of h
  obtain ⟨trace, t, he, hp⟩ := parametersMain_ok M ha.pre
  exact ⟨trace, t, he, parametersPreserved ha hp, parametersSharedPost ha hp⟩

theorem parametersPublicRelated {s₁ s₂ : State} (h₁ : ParametersABI s₁) (h₂ : ParametersABI s₂)
    (h : (Proof.Dsa.checkParametersContract abi).pub s₁ s₂) : Two ParametersStart s₁ s₂ := by
  sig_pub [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero] at h
  obtain ⟨hsp, hl, hdi, _, hdx, hcx, h8, _⟩ := h
  have hb := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl
  have hp : h₁.input.pLen = h₂.input.pLen := congrArg BitVec.toNat hdx
  have hq : h₁.input.qLen = h₂.input.qLen := congrArg BitVec.toNat hcx
  have hpb : h₁.input.params = h₂.input.params := hb
  have hpb' : h₁.input.pb = h₂.input.pb := by
    change h₁.input.params.take h₁.input.pLen = h₂.input.params.take h₂.input.pLen
    rw [hpb, hp]
  have hqb' : h₁.input.qb = h₂.input.qb := by
    change (h₁.input.params.drop h₁.input.pLen).take h₁.input.qLen =
      (h₂.input.params.drop h₂.input.pLen).take h₂.input.qLen
    rw [hpb, hp, hq]
  have hac : h₁.input.accepted = h₂.input.accepted := by
    unfold ParametersInput.accepted
    congr 1
  have hlayout : h₁.call.layout = h₂.call.layout := by
    change h₁.input.layout s₁ _ _ = h₂.input.layout s₂ _ _
    unfold ParametersInput.layout
    have hf : checkFieldValues s₁ h₁.input.accepted = checkFieldValues s₂ h₂.input.accepted := by
      funext f
      cases f <;> simp only [checkFieldValues, hdi, hdx, hcx, hac]
    congr 1
    · exact congrArg Spec.Dsa.decodeBE hpb'
    · exact congrArg Spec.Dsa.decodeBE hqb'
  exact ⟨h₂.call, ⟨h₁.call, ⟨hlayout, hpb⟩, rfl⟩, ⟨h₂.call, ⟨rfl, rfl⟩, rfl⟩, hsp⟩

theorem parametersConstantTime (M : Mont) :
    ConstantTime isa (Proof.Dsa.checkParametersContract abi).pre
      (Proof.Dsa.checkParametersContract abi).pub (Generate.checkParameters M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (parametersMain_ct M _ _ _ _ _ _
    (parametersPublicRelated (parametersABI_of h₁) (parametersABI_of h₂) hp) e₁ e₂).1

/-- An ordinary 1024/160 call with disjoint buffers. The all-zero domain is
allowed by the contract and rejected by the program. -/
def parametersSatState : State where
  gpr r := match r with
    | .x0 => 0x2000 | .x1 => 276 | .x2 => 128 | .x3 => 20
    | .x4 => 0x8000 | .x5 => 2048 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 276⟩]
  wr := [⟨0x8000, 16384⟩]

theorem parametersSatisfiable : ∃ s, (Proof.Dsa.checkParametersContract abi).pre s := by
  sig_implies_sat [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero]
    [parametersSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using parametersSatState

theorem parameters_verified (M : Mont)
    :
    Verified target (Generate.checkParameters M.mm) (Proof.Dsa.checkParametersContract abi) :=
  ⟨parametersCorrect M, parametersConstantTime M, parametersSatisfiable⟩

end VG.Proof.Dsa.AArch64
