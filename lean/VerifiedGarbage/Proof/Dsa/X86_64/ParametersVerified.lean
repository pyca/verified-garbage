module

public import VerifiedGarbage.Proof.Dsa.X86_64.ParametersCT
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.X86_64.ABIRegions
-- Proofs inside exposed definitions (structure values) use these: Lean needs them public.
public import VerifiedGarbage.Proof.Bignum.Octets -- shake: keep
public import VerifiedGarbage.Proof.Dsa.Contract

/-! # The x86-64 DSA domain check verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem stackArgs_zero (s : State) : List.map (stackArg s) (List.range 0) = [] := rfl

structure ParametersABI (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩]
  wr : s.wr = [⟨s.gpr .r8, (s.gpr .r9).toNat * 8⟩]
  paramsScratch : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat * 8⟩
  retParams : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  retScratch : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat * 8⟩
  paramsBound : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  scratchBound : (s.gpr .r8).toNat + (s.gpr .r9).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .rdx).toNat (s.gpr .rcx).toNat
  paramsLength : (s.gpr .rsi).toNat = 2 * (s.gpr .rdx).toNat + (s.gpr .rcx).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .rdx).toNat ≤ (s.gpr .r9).toNat

theorem parametersABI_of {s : State} (h : (Proof.Dsa.checkParametersContract abi).pre s) : ParametersABI s := by
  sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero] at h
  sig_split h
  constructor <;> with_reducible assumption

def ParametersABI.input {s : State} (h : ParametersABI s) : ParametersInput where
  base := s.gpr .r8
  pLen := (s.gpr .rdx).toNat
  qLen := (s.gpr .rcx).toNat
  params := Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
  lengths := h.lengths
  paramsLength := (bytesAt_length _ _ _).trans h.paramsLength

theorem ParametersABI.used {s : State} (h : ParametersABI s) : usedBytes ≤ (s.gpr .r9).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 15712 ≤ _
  omega

theorem ParametersABI.pre {s : State} (h : ParametersABI s) : ParametersPre h.input s := by
  have hs : Scr s (s.gpr .r8) ((s.gpr .r9).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  exact ⟨scratch_prefix hs h.used (by decide), rfl, (ofNat_toNat64 _).symm, (ofNat_toNat64 _).symm,
    source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .rsi).isLt) h.paramsScratch) h.used⟩

def ParametersABI.call {s : State} (h : ParametersABI s) : ParametersCall := ⟨h.input, s, h.pre⟩

theorem parametersGprPreserved {s t : State} (h : ParametersABI s) (hp : ParametersPost h.input s t) :
    gprPreserved s t := by
  obtain ⟨_, hsaved, hf, hk⟩ := hp
  refine ⟨?_, Mem.readW_congr fun i hi => ?_⟩
  · intro reg hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved 0 (by decide)
    · exact hsaved 1 (by decide)
    · exact hk.gpr (by decide)
    · exact hsaved 2 (by decide)
    · exact hsaved 3 (by decide)
    · exact hsaved 4 (by decide)
    · exact hsaved 5 (by decide)
  · exact hf _ (Nat.le_trans h.used (out_scr h.retScratch
      (contains_byte (s.gpr .rsp) (i := i) (len := 8) hi (by decide))))

theorem parametersSharedPost {s t : State} (h : ParametersABI s) (hp : ParametersPost h.input s t) :
    (Proof.Dsa.checkParametersContract abi).post s t := by
  sig_post [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero]
  rw [hp.1]
  change _ = if Spec.Dsa.checkParametersBytes h.input.pLen h.input.qLen h.input.params = true then 1 else 0
  cases Spec.Dsa.checkParametersBytes h.input.pLen h.input.qLen h.input.params <;> rfl

theorem parametersCorrect (M : Mont) (Sq : MontS)
    (hmx : (Generate.checkParameters Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : (Proof.Dsa.checkParametersContract abi).pre s) :
    ∃ trace t, Exec isa (Generate.checkParameters Sq.mm M.mm) s trace t ∧ abiPreserved s t ∧
      (Proof.Dsa.checkParametersContract abi).post s t := by
  have ha := parametersABI_of h
  obtain ⟨trace, t, he, hp⟩ := parametersMain_ok M Sq ha.pre
  exact ⟨trace, t, he, abiPreserved_of_exec hmx he (parametersGprPreserved ha hp), parametersSharedPost ha hp⟩

theorem parametersPublicRelated {s₁ s₂ : State} (h₁ : ParametersABI s₁) (h₂ : ParametersABI s₂)
    (h : (Proof.Dsa.checkParametersContract abi).pub s₁ s₂) : Two ParametersStart s₁ s₂ := by
  sig_pub [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero] at h
  obtain ⟨_, hl, hdi, _, hdx, hcx, h8, _⟩ := h
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
  exact ⟨h₂.call, ⟨h₁.call, ⟨hlayout, hpb⟩, rfl⟩, ⟨h₂.call, ⟨rfl, rfl⟩, rfl⟩⟩

theorem parametersConstantTime (M : Mont) (Sq : MontS) :
    ConstantTime isa (Proof.Dsa.checkParametersContract abi).pre
      (Proof.Dsa.checkParametersContract abi).pub (Generate.checkParameters Sq.mm M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (parametersMain_ct M Sq _ _ _ _ _ _
    (parametersPublicRelated (parametersABI_of h₁) (parametersABI_of h₂) hp) e₁ e₂).1

/-- An ordinary 1024/160 call with disjoint buffers. The all-zero domain is
allowed by the contract and rejected by the program. -/
def parametersSatState : State where
  gpr r := match r with
    | .rdi => 0x2000 | .rsi => 276 | .rdx => 128 | .rcx => 20
    | .r8 => 0x8000 | .r9 => 2048 | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 276⟩]
  wr := [⟨0x8000, 16384⟩]

theorem parametersSatisfiable : ∃ s, (Proof.Dsa.checkParametersContract abi).pre s := by
  sig_implies_sat [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero]
    [parametersSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using parametersSatState

theorem parameters_verified (M : Mont) (Sq : MontS)
    (hmx : (Generate.checkParameters Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (Generate.checkParameters Sq.mm M.mm) (Proof.Dsa.checkParametersContract abi) :=
  ⟨parametersCorrect M Sq hmx, parametersConstantTime M Sq, parametersSatisfiable⟩

end VG.Proof.Dsa.X86_64
