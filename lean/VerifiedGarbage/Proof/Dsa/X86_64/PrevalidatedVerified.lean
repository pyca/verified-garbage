module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Impl.Dsa.X86_64.Prevalidated
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Spec.Dsa.Prevalidated
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
public import VerifiedGarbage.Proof.Dsa.Validation
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Spec.Dsa.SignVerify
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86_64.PublicSlices
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingCT
public import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
public import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT
import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningInput
public import VerifiedGarbage.Proof.Dsa.X86_64.EntryFields
import VerifiedGarbage.Proof.Dsa.X86_64.Save
import VerifiedGarbage.Proof.Dsa.X86_64.Parameters
import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
import VerifiedGarbage.Proof.Dsa.X86_64.SigningShape
import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.X86_64.Result
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Impl.Dsa.X86_64.Prevalidated
meta import VerifiedGarbage.Proof.Dsa.X86_64.SigningInput
meta import VerifiedGarbage.Spec.Dsa.Prevalidated
meta import VerifiedGarbage.Proof.Dsa.X86_64.EntryFields
meta import VerifiedGarbage.Proof.Dsa.X86_64.Save
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parameters
meta import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
meta import VerifiedGarbage.Proof.Dsa.X86_64.SigningShape
meta import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
meta import VerifiedGarbage.Proof.Dsa.X86_64.Result
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState
import VerifiedGarbage.Proof.Dsa.X86_64.CheckOperands
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
import VerifiedGarbage.Proof.Dsa.DomainWidths
meta import VerifiedGarbage.Proof.Dsa.X86_64.CheckOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
meta import VerifiedGarbage.Proof.Dsa.DomainWidths
public import VerifiedGarbage.Proof.Dsa.X86_64.ParametersCT
-- Proofs inside exposed definitions (structure values) use these: Lean needs them public.
public import VerifiedGarbage.Proof.Dsa.Contract

/-! ### `Dsa.X86_64.ParametersVerified`, which this module and modules that import it used -/

section

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
  omega_using [hl, hs]

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

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.PrevalidatedCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.Prevalidated`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.VerifyingReturn`, which this module and modules that import it used -/

section

/-! # Both verifying branches return the packed byte specification -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def VerifyingPost (p : VerifyingInput) (original t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (Spec.Dsa.verifyBytes p.pLen p.qLen p.key p.signature p.digest).toNat ∧
  (∀ i < 6, t.gpr (saved.getD i .rax) = original.gpr (saved.getD i .rax)) ∧
  InScr p.base usedBytes original.mem t.mem ∧ Keep coreRegs original t

theorem verifyingAccepted_ok (M : Mont) (Sq : MontS) {p : VerifyingInput} {original s : State} (h : VerifyingPre p original)
    (hi : VerifyingInitialized p original h.pLength h.qLength s) (ha : p.accepted = true) :
    WP isa (verifyBody Sq.mm M.mm) s (VerifyingPost p original) := by
  obtain ⟨pi, qi, hr, ho, hm, hsave, hf, hk⟩ := hi
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
  refine WP.mono (verifyBody_spec M Sq (L := L) hr p.values ho hsize hpodd hqodd hpf hqf
    p.keyLength p.signatureLength hkey rfl rfl hqn rfl hm)
    fun t ⟨hret, hsaved, hframe, hkeep⟩ => ?_
  exact ⟨hret, fun i hi => (hsaved i hi).trans (hsave i hi),
    hf.trans (InScr.of_outside hframe (by decide)), (hk.trans hkeep).mono (by decide)⟩

theorem verifyingRejected_ok {p : VerifyingInput} {original s : State} (h : VerifyingPre p original)
    (hs : VerifyingShapePost p original h.pLength h.qLength s) (ha : p.accepted = false) :
    WP isa (.block (([.mov32 .rax (.imm 0)] : List Instr) ++ VG.Impl.Bignum.X86_64.Public.exit)) s
      (VerifyingPost p original) := by
  have hparams : ¬ Spec.Dsa.parametersValid (Spec.Dsa.publicKeyBytes p.pLen p.qLen p.key).params :=
    shapeAccepted_false ha (Spec.Dsa.decodeBE p.components.g)
  have hfalse := verifyBytes_invalid_shape (signature := p.signature) (digest := p.digest) hparams
  refine WP.mono (verifyFailure_ok hs.scratch hs.rdi (by decide))
    fun t ⟨hret, hsave, hmem, hk⟩ => ?_
  unfold VerifyingPost
  rw [hfalse]
  exact ⟨hret, fun i hi => (hsave i hi).trans (hs.saved i hi),
    by rw [hmem]; exact hs.frame, (hs.keep.trans hk).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # Functional correctness of x86-64 DSA verification for a validated public key

The program is the verifier's, with the domain and public-value checks
replaced by rebuilding q−2: the precondition that the exact key bytes
validate makes those checks' mask true. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def prevalidatedAccepted (L : ExecutionLayout) (data : VerifyValues) (valid : Bool) : Bool :=
  decide (Spec.Dsa.encodeBE L.qLen (data.value L) = data.signatureR) &&
  (decide (0 < Spec.Dsa.decodeBE data.signatureS ∧ Spec.Dsa.decodeBE data.signatureS < L.subgroup) &&
  (decide (0 < Spec.Dsa.decodeBE data.signatureR ∧ Spec.Dsa.decodeBE data.signatureR < L.subgroup) &&
    valid))

theorem prevalidatedCompute_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : VerifyValues)
    (hg : OperandBytes s0 L.base usedBytes Core.generator data.generator)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue data.publicValue)
    (hr : OperandBytes s0 L.base usedBytes Core.signatureR data.signatureR)
    (hs : OperandBytes s0 L.base usedBytes Core.signatureS data.signatureS)
    (hz : OperandBytes s0 L.base usedBytes Core.digest data.digest)
    (hgl : data.generator.length = L.pLen) (hyl : data.publicValue.length = L.pLen)
    (hrl : data.signatureR.length = L.qLen) (hsl : data.signatureS.length = L.qLen)
    (hzl : data.digest.length < 2 ^ 64)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (Prevalidated.compute Sq.mm M.mm) s0 fun s5 =>
      Ready L s5 ∧ word s5.mem L.base Field.mask.offset = mask (prevalidatedAccepted L data valid) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s5.mem ∧ Keep coreRegs s0 s5 := by
  obtain ⟨hql, hqu, _, _⟩ := L.widths
  obtain hu : u + L.qLen ≤ usedBytes := by unfold u usedBytes; omega_using [hqu]
  obtain hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega_using [hqu]
  unfold Prevalidated.compute
  refine WP.seq (WP.mono (readyMinus_ok h0 .q 2 (by decide)
    (by change 2 ≤ L.subgroup; omega_using [hq]) qMinusTwo (by decide) hqm) fun s1 h1 => ?_)
  obtain hg1 := h1.external (by decide) hqm hg
  obtain hy1 := h1.external (by decide) hqm hy
  obtain hr1 := h1.external (by decide) hqm hr
  obtain hs1 := h1.external (by decide) hqm hs
  obtain hz1 := h1.external (by decide) hqm hz
  obtain hm1 := (h1.fields (by decide) hqm .mask).trans hm
  obtain hqm1 := h1.output (by decide) hqm
  refine WP.seq (WP.mono (readyRange_ok h1.ready .q Core.signatureR (by trivial) hr1.active
    (by rw [hrl]; omega_using [hql]) (by simp only [hrl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false hm1) fun s2 h2 => ?_)
  obtain hg2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg1
  obtain hy2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy1
  obtain hr2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.signatureR]) hr1
  obtain hs2 := h2.preserve h1.ready (by decide) (by decide) (by trivial) hs1
  obtain hz2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.digest]) hz1
  obtain hqm2 := h2.preserve h1.ready (Nat.le_refl _) (by decide) (by trivial) hqm1
  refine WP.seq (WP.mono (readyRange_ok h2.ready .q Core.signatureS (by trivial) hs2.active
    (by rw [hsl]; omega_using [hql]) (by simp only [hsl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false h2.mask) fun s3 h3 => ?_)
  obtain hg3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg2
  obtain hy3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy2
  obtain hr3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.signatureR]) hr2
  obtain hs3 := h3.preserve h2.ready (by decide) (by decide) (by trivial) hs2
  obtain hz3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.digest]) hz2
  obtain hqm3 := h3.preserve h2.ready (Nat.le_refl _) (by decide) (by trivial) hqm2
  refine WP.seq (WP.mono (coreVerify_ok M Sq h3.ready hp hq hop hoq hpf hqf data hg3 hy3 hr3 hs3 hz3
    hgl hyl hrl hsl hzl hqm3) fun s4 ⟨h4, hu4bytes, hf4, hm4eq, hk4⟩ => ?_)
  obtain hr4 := h3.ready.preserveExternal h4 hf4 hk4 (by decide) (by simp [stablePointer, Core.signatureR]) hr3
  obtain hm4 := hm4eq.trans h3.mask
  obtain hu4 := h4.encodedLocal .q u (data.value L) (by decide) hu hu4bytes
  refine WP.mono (readyEqual_ok h4 (Core.scalar u) Core.signatureR
    (by change u < 2 ^ 31; decide) (by trivial) hu4 hr4.active
    (by simp only [encodeBE_length, ModulusSide.length, hrl])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hqu]) false hm4) fun s5 h5 => ?_
  refine ⟨h5.ready, ?_, ((((h1.scheduleFrame (by decide) hqm).trans h2.scheduleFrame).trans
      h3.scheduleFrame).trans hf4).trans h5.scheduleFrame,
    ((((h1.keep.trans h2.keep).trans h3.keep).trans hk4).trans h5.keep).mono (by decide)⟩
  have hm5 := h5.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.length, ModulusSide.value] at hm5
  exact hm5

def prevalidatedBody (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (Prevalidated.compute sq mul) (.block SignVerify.result)

theorem prevalidatedBody_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : VerifyValues) {qb : List Byte} (h : VerificationOperands L data qb s0)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (prevalidatedBody Sq.mm M.mm) s0 fun t =>
      t.gpr .rax = BitVec.ofNat 64 (prevalidatedAccepted L data valid).toNat ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s0.mem L.base (8 * i)) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem t.mem ∧ Keep coreRegs s0 t := by
  unfold prevalidatedBody
  refine WP.seq (WP.mono (prevalidatedCompute_ok M Sq h0 hp hq hop hoq hpf hqf data h.generator
    h.publicValue h.signatureR h.signatureS h.digest h.generatorLength h.publicLength
    h.rLength h.sLength h.digestBound hm)
    fun s1 ⟨h1, hm1, hf1, hk1⟩ => ?_)
  refine WP.mono (result_ok h1.scratch h1.parent.rdi (by decide) hm1)
    fun t ⟨ha, hsave, hmem, hk⟩ => ?_
  exact ⟨ha, fun i hi => (hsave i hi).trans (hf1.word (Or.inl (by omega_using [hi])) (by omega_using [hi])),
    by rw [hmem]; exact hf1, (hk1.trans hk).mono (by decide)⟩

theorem prevalidatedBody_spec (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (data : VerifyValues) {qb key signature digest : List Byte} {n : Nat}
    (h : VerificationOperands L data qb s0)
    (hsize : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength L.modulus) (Spec.Dsa.bitLength L.subgroup))
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (hkl : key.length = 3 * L.pLen + L.qLen) (hsl : signature.length = 2 * L.qLen)
    (hk : Spec.Dsa.publicKeyBytes L.pLen L.qLen key = data.key L)
    (hr : signature.take L.qLen = data.signatureR) (hs : signature.drop L.qLen = data.signatureS)
    (hqn : Spec.Dsa.bitLength L.subgroup = 8 * n) (hz : data.digest = digest.take n)
    (hv : Spec.Dsa.validatePublicKeyBytes L.pLen L.qLen key = true)
    (hm : word s0.mem L.base Field.mask.offset = mask true) :
    WP isa (prevalidatedBody Sq.mm M.mm) s0 fun t =>
      t.gpr .rax = BitVec.ofNat 64 (Spec.Dsa.verifyBytes L.pLen L.qLen key signature digest).toNat ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s0.mem L.base (8 * i)) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem t.mem ∧ Keep coreRegs s0 t := by
  obtain ⟨hp, hq, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  obtain hv' : publicAccepted L data.generator data.publicValue true = true := by
    rw [publicAccepted_spec L data.generator data.publicValue hsize hop hoq]
    simpa only [Spec.Dsa.validatePublicKeyBytes, L.lengths, decide_true, Bool.not_true,
      hkl, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte, hk,
      VerifyValues.key] using hv
  obtain he : verifyAccepted L data true = prevalidatedAccepted L data true := by
    simp only [verifyAccepted, prevalidatedAccepted, hv']
  rw [verifyBytes_compute L data key signature digest n hsize hop hoq hqf h.rLength hkl hsl hk hr hs hqn hz, he]
  exact prevalidatedBody_ok M Sq h0 hp hq hop hoq hpf hqf data h hm

theorem prevalidatedAccepted_ok (M : Mont) (Sq : MontS) {p : VerifyingInput} {original s : State}
    (h : VerifyingPre p original)
    (hi : VerifyingInitialized p original h.pLength h.qLength s) (ha : p.accepted = true)
    (hv : Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key = true) :
    WP isa (prevalidatedBody Sq.mm M.mm) s (VerifyingPost p original) := by
  obtain ⟨pi, qi, hr, ho, hm, hsave, hf, hk⟩ := hi
  let L := (p.layout original h.pLength h.qLength).withInverses pi qi
  obtain ⟨hsize, hpodd, hqodd⟩ := p.shapeFacts ha
  obtain hpf : L.modulus ≤ 256 ^ L.pLen := by
    obtain hh := VG.Proof.Dsa.decodeBE_lt p.components.p
    rw [p.components.pLength] at hh
    exact Nat.le_of_lt hh
  obtain hqf : L.subgroup ≤ 256 ^ L.qLen := by
    obtain hh := VG.Proof.Dsa.decodeBE_lt p.components.q
    rw [p.components.qLength] at hh
    exact Nat.le_of_lt hh
  obtain hqn := VG.Proof.Dsa.subgroup_scan_width hsize
  have hkey : Spec.Dsa.publicKeyBytes L.pLen L.qLen p.key = p.values.key L := rfl
  refine WP.mono (prevalidatedBody_spec M Sq (L := L) hr p.values ho hsize hpodd hqodd hpf hqf
    p.keyLength p.signatureLength hkey rfl rfl hqn rfl hv hm)
    fun t ⟨hret, hsaved, hframe, hkeep⟩ => ?_
  exact ⟨hret, fun i hi => (hsaved i hi).trans (hsave i hi),
    hf.trans (InScr.of_outside hframe (by decide)), (hk.trans hkeep).mono (by decide)⟩

theorem prevalidatedMain_ok (M : Mont) (Sq : MontS) {p : VerifyingInput} {s0 : State} (h : VerifyingPre p s0)
    (hv : Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key = true) :
    WP isa (Prevalidated.verify Sq.mm M.mm) s0 (VerifyingPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (verifyingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => verifyingRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change eval .e s = some true
    simp only [eval, hs.branch, ha, Bool.not_false]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
    · change eval .e s = some false
      simp only [eval, hs.branch, ha, Bool.not_true]
    · refine WP.seq (WP.mono (verifyingInitialize_ok h hs ha) fun t ht => ?_)
      exact prevalidatedAccepted_ok M Sq h ht ha hv

end VG.Proof.Dsa.X86_64

end

end

/-! # Constant time of x86-64 DSA verification for a validated public key -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem prevalidatedCompute_ct (M : Mont) (Sq : MontS) : RelCT isa (Two (ScheduleState verifyComputeInputs))
    (Prevalidated.compute Sq.mm M.mm) (Two (ScheduleState verifyComputeInputs)) := by
  have h1 := scheduleMinus_ct verifyComputeInputs verifyComputeInputs_stable .q 2 qMinusTwo (by decide)
    (by intro p; have := p.qGreater; change 2 ≤ p.layout.subgroup; omega_using [this])
    (by decide) (by decide) (scalar_space (by decide)) (by taint_decide) (by taint_decide)
  have h2 := scheduleRange_ct verifyComputeInputs verifyComputeInputs_stable .q Core.signatureR
    (fun p => p.layout.qLen) false (by trivial) (by simp [stablePointer, Core.signatureR])
    (fun p => p.layout.widths.1) (fun _ => Nat.le_refl _) (by taint_decide)
  have h3 := scheduleRange_ct verifyComputeInputs verifyComputeInputs_stable .q Core.signatureS
    (fun p => p.layout.qLen) false (by trivial) (by trivial)
    (fun p => p.layout.widths.1) (fun _ => Nat.le_refl _) (by taint_decide)
  have h4 := coreVerifySchedule_ct M Sq verifyComputeInputs verifyComputeInputs_stable
    (by intro p a ha; simp [verifyComputeInputs, ha])
  have h5 := scheduleEqual_ct verifyComputeInputs verifyComputeInputs_stable (Core.scalar u) Core.signatureR
    (fun p => p.layout.qLen) false (by change u < 2 ^ 31; decide) (by trivial) (by trivial)
    (by simp [stablePointer, Core.signatureR]) (by decide)
    (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega_using [this]) (by taint_decide)
  unfold Prevalidated.compute seqs
  refine RelCT.seq h1 (RelCT.seq (R := Two (ScheduleState verifyComputeInputs)) ?_
    (RelCT.seq (R := Two (ScheduleState verifyComputeInputs)) ?_ (RelCT.seq h4 ?_)))
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, (h.2.1 (Core.signatureR, p.layout.qLen) (by simp [verifyComputeInputs, verifyInputs])).active⟩) h2
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, (h.2.1 (Core.signatureS, p.layout.qLen) (by simp [verifyComputeInputs, verifyInputs])).active⟩) h3
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, h.1.availableLocal .q u (by decide) (scalar_space (by decide) p),
        (h.2.1 (Core.signatureR, p.layout.qLen) (by simp [verifyComputeInputs, verifyInputs])).active⟩) h5

theorem prevalidatedComputeReturn_ok (M : Mont) (Sq : MontS) {p : SchedulePublic} {s : State}
    (h : VerifyingBodyPre p s) :
    WP isa (Prevalidated.compute Sq.mm M.mm) s (fun t => t.gpr .rdi = p.layout.base) := by
  obtain ⟨hr, ⟨data, qb, ho, _⟩, ⟨valid, hm⟩⟩ := h
  refine WP.mono (prevalidatedCompute_ok M Sq hr p.pGreater p.qGreater p.pOdd p.qOdd p.pFits p.qFits data
    ho.generator ho.publicValue ho.signatureR ho.signatureS ho.digest
    ho.generatorLength ho.publicLength ho.rLength ho.sLength
    ho.digestBound hm) fun _ h => h.1.parent.rdi

theorem prevalidatedBody_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two VerifyingBodyPre) (prevalidatedBody Sq.mm M.mm) (fun _ _ => True) := by
  refine RelCT.seq (R := Two (fun p : SchedulePublic => fun t => t.gpr .rdi = p.layout.base)) ?_ ?_
  · refine two_post ((two_map (fun p => p) (fun _ _ h => h.schedule.1) (prevalidatedCompute_ct M Sq)).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
    exact fun _ _ h => prevalidatedComputeReturn_ok M Sq h
  · exact two_map (fun p => p.layout.base) (fun _ _ h => h) result_ct

theorem prevalidatedSuccess_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two (fun c : AcceptedVerifyingCall => VerifyingShaped c.val))
      (seqs [SignVerify.workspaces, Prevalidated.compute Sq.mm M.mm, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq verifyingWorkspaces_ct ?_
  exact (prevalidatedBody_ct M Sq).mono (fun _ _ h => verifyingReady_related h) (fun _ _ h => h)

theorem prevalidatedMain_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two VerifyingStart) (Prevalidated.verify Sq.mm M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq verifyingShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map (fun c : VerifyingCall => c.layout.base) (fun _ _ h => h.rdi) verifyFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (prevalidatedSuccess_ct M Sq).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval .e s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.ValidateCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.Validate`, which only this module used -/

section

/-! # Functional correctness of the x86-64 DSA public-key validator

The entry stores verification's fields with no digest, so the verifier's
shape checks and workspaces apply unchanged; only the domain and public
value are then checked. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def validateFields : List Instr :=
  [.mov32 .rax (.imm 0), .store (SignVerify.initial .out) .rax, .store (SignVerify.initial .nonce) .rax,
    .store (SignVerify.initial .p) .rdi, .store (SignVerify.initial .pLen) .rdx,
    .store (SignVerify.initial .qLen) .rcx, .store (SignVerify.initial .signature) .r8,
    .store (SignVerify.initial .digest) .rax, .store (SignVerify.initial .digestLen) .rax]

theorem validateFields_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .r11 = B) (hZ : pWorkspace ≤ Z) :
    WP isa (.block validateFields) s fun t =>
      t.mem = verifyFieldMem s.mem B (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) 0 0 ∧
      Keep [.rax] s t := by
  refine WP.keep [.rax] ?_ rfl
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  unfold validateFields
  xrun [State.ea, SignVerify.initial, h11, fieldAddress,
    hw .out, hw .nonce, hw .p, hw .pLen, hw .qLen, hw .signature, hw .digest, hw .digestLen]
  rfl

theorem validateEntry_ok {s0 : State} {B digest digestLen : Addr} {Z : Nat}
    (hs : Scr s0 B Z) (h8 : s0.gpr .r8 = B) (hZ : pWorkspace ≤ Z)
    (hd : digest = 0) (hdl : digestLen = 0) :
    WP isa (.block Prevalidated.validateEntry) s0 (VerifyEntryPost s0 B digest digestLen) := by
  subst hd hdl
  change WP isa (.block (([.mov .r11 (.reg .r8)] : List Instr) ++ SignVerify.save ++ validateFields ++
    SignVerify.keyPointers)) s0 _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (moveScratch_ok s0) fun s1 ⟨h11, hmem1, hk1⟩ => ?_
  rw [h8] at h11
  rw [WP.block_append_iff]
  refine WP.mono (save_ok (hs.congr hk1.2.2) h11 (Nat.le_trans (by decide) hZ)) fun s2 ⟨hsaved, hf2, hk2⟩ => ?_
  have hk12 := hk1.trans hk2
  have hreg (reg : Reg) (hne : reg ≠ .r11) : s2.gpr reg = s0.gpr reg := hk12.gpr (by simpa using hne)
  rw [WP.block_append_iff]
  refine WP.mono (validateFields_ok (hs.congr hk12.2.2) ((hk2.gpr (by decide)).trans h11) hZ)
    fun s3 ⟨hmem3, hk3⟩ => ?_
  rw [hreg .rdi (by decide), hreg .rdx (by decide), hreg .rcx (by decide), hreg .r8 (by decide)] at hmem3
  have hfields := verifyFieldMem_fields s2.mem B (s0.gpr .rdi) (s0.gpr .rdx) (s0.gpr .rcx) (s0.gpr .r8) 0 0
  rw [← hmem3] at hfields
  have hunused := verifyFieldMem_unused s2.mem B (s0.gpr .rdi) (s0.gpr .rdx) (s0.gpr .rcx) (s0.gpr .r8) 0 0
  rw [← hmem3] at hunused
  have hf3 : Outside B 256 (pWorkspace - 256) s2.mem s3.mem := by rw [hmem3]; exact verifyFieldMem_frame _ _ _ _ _ _ _ _
  have hk123 := hk12.trans hk3
  have h113 : s3.gpr .r11 = B := (hk3.gpr (by decide)).trans ((hk2.gpr (by decide)).trans h11)
  refine WP.mono (keyPointers_ok (hs.congr hk123.2.2) h113 hZ hfields.1 hfields.2.1 hfields.2.2.1)
    fun s4 ⟨hmem4, hdi4, hk4⟩ => ?_
  have hptr := keyPointerMem_fields s3.mem B (s0.gpr .rdi) (s0.gpr .rdx) (s0.gpr .rcx)
  rw [← hmem4] at hptr
  have hf4 : Outside B 264 32 s3.mem s4.mem := by rw [hmem4]; exact keyPointerMem_frame _ _ _ _ _
  have hsame (f : Field) (hsep : f.offset + 8 ≤ 264 ∨ 296 ≤ f.offset) :
      word s4.mem B f.offset = word s3.mem B f.offset :=
    hf4.word hsep (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))
  refine ⟨hdi4, (hsame .p (by decide)).trans hfields.1, (hsame .pLen (by decide)).trans hfields.2.1,
    (hsame .qLen (by decide)).trans hfields.2.2.1, (hsame .signature (by decide)).trans hfields.2.2.2.1,
    (hsame .digest (by decide)).trans hfields.2.2.2.2.1, (hsame .digestLen (by decide)).trans hfields.2.2.2.2.2,
    hptr.1, hptr.2.1, hptr.2.2.1, hptr.2.2.2, ?_, ?_, ?_, (hk123.trans hk4).mono (by decide)⟩
  · exact ⟨(hsame .out (by decide)).trans hunused.1, (hsame .nonce (by decide)).trans hunused.2⟩
  · intro i hi
    exact ((hf4.word (Or.inl (by omega_using [hi])) (by omega_using [hi])).trans (entry_saved_frame hf3 hi)).trans
      ((hsaved i hi).trans (hk1.gpr (by simpa using saved_ne_r11 hi)))
  · have hwide2 : Outside B 0 pWorkspace s0.mem s2.mem := by
      rw [← hmem1]
      exact hf2.mono (Nat.le_refl _) (by decide)
    exact (hwide2.trans (hf3.mono (by decide) (by decide))).trans (hf4.mono (by decide) (by decide))

structure ValidatingPre (p : VerifyingInput) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  pLength : s.gpr .rdx = BitVec.ofNat 64 p.pLen
  qLength : s.gpr .rcx = BitVec.ofNat 64 p.qLen
  base : s.gpr .r8 = p.base
  keySource : Src s p.base usedBytes (s.gpr .rdi) p.key
  digestNil : p.digest = []
  digestPointer : p.digestPointer = 0

theorem validatingShape_ok {p : VerifyingInput} {s0 : State} (h : ValidatingPre p s0) :
    WP isa (.seq (.block Prevalidated.validateEntry) Checks.domainShape) s0
      (VerifyingShapePost p s0 h.pLength h.qLength) := by
  refine WP.seq (WP.mono (validateEntry_ok (digest := p.digestPointer)
    (digestLen := BitVec.ofNat 64 p.digest.length) h.scratch h.base (by decide) h.digestPointer
    (by rw [h.digestNil]; rfl)) fun s1 he => ?_)
  have hinside : InScr p.base usedBytes s0.mem s1.mem := InScr.of_outside he.frame (by decide)
  have hkey := h.keySource.congrK hinside he.keep
  have hps : Src s1 p.base usedBytes (s0.gpr .rdi) p.components.p := source_take hkey
  have hqs : Src s1 p.base usedBytes (s0.gpr .rdi + BitVec.ofNat 64 p.pLen) p.components.q :=
    source_slice hkey (by rw [p.keyLength]; omega_using [])
  have hp1 : 0 < p.components.p.length := by
    rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  have hq1 : 0 < p.components.q.length := by
    rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  have hp64 : p.components.p.length < 2 ^ 64 := by
    rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  have hq64 : p.components.q.length < 2 ^ 64 := by
    rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  refine WP.mono (domainShape_ok (h.scratch.congr he.keep.2.2) he.base (by decide) he.p
    (by rw [he.q, h.pLength]) (by rw [he.pLen, h.pLength, p.components.pLength])
    (by rw [he.qLen, h.qLength, p.components.qLength]) hps hqs hp1 hp64 hq1 hq64 rfl rfl
    p.digestBound he.digestLen) fun s2 ⟨hprefix, hmask, hbranch, hf, hk⟩ => ?_
  have hall := he.keep.trans hk
  have hft : InScr p.base usedBytes s1.mem s2.mem := by
    apply InScr.of_frm hf
    intro range hr
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  exact ⟨h.scratch.congr hall.2.2, (hk.gpr (by decide)).trans he.base,
    he.shapeFields hf hprefix hmask, hbranch,
    fun i hi => (shape_saved hf hi).trans (he.saved i hi), hinside.trans hft,
    hall.mono (by decide)⟩

theorem validatingOperands {p : VerifyingInput} {original s : State}
    {hp : original.gpr .rdx = BitVec.ofNat 64 p.pLen}
    {hq : original.gpr .rcx = BitVec.ofNat 64 p.qLen} {pi qi : BitVec 64}
    (h : Ready ((p.layout original hp hq).withInverses pi qi) s)
    (hkey : Src s p.base usedBytes (original.gpr .rdi) p.key) :
    OperandBytes s p.base usedBytes Core.generator p.components.g ∧
    OperandBytes s p.base usedBytes Core.publicValue p.components.y ∧
    OperandBytes s p.base usedBytes ⟨.input .q, .qLen⟩ p.components.q := by
  let L := (p.layout original hp hq).withInverses pi qi
  have hqlen : p.components.q.length = p.qLen := p.components.qLength
  have hglen : p.components.g.length = p.pLen := p.components.gLength
  have hylen : p.components.y.length = p.pLen := p.components.yLength
  have qptr : L.fields .q = original.gpr .rdi + BitVec.ofNat 64 p.pLen := by
    change original.gpr .rdi + original.gpr .rdx = _
    rw [hp]
  have gptr : L.fields .g = original.gpr .rdi + BitVec.ofNat 64 (p.pLen + p.qLen) := by
    change original.gpr .rdi + original.gpr .rdx + original.gpr .rcx = _
    rw [hp, hq, Offset.add_add]
  have yptr : L.fields .y = original.gpr .rdi + BitVec.ofNat 64 (2 * p.pLen + p.qLen) := by
    change original.gpr .rdi + original.gpr .rdx + original.gpr .rcx + original.gpr .rdx = _
    rw [hp, hq, Offset.add_add, Offset.add_add, show p.pLen + (p.qLen + p.pLen) = 2 * p.pLen + p.qLen by omega_using []]
  have hqsrc : Src s p.base usedBytes (L.fields .q) p.components.q := by
    rw [qptr]; exact source_slice hkey (by rw [p.keyLength]; omega_using [])
  have hgsrc : Src s p.base usedBytes (L.fields .g) p.components.g := by
    rw [gptr]; exact source_slice hkey (by rw [p.keyLength]; omega_using [])
  have hysrc : Src s p.base usedBytes (L.fields .y) p.components.y := by
    rw [yptr]; exact source_slice hkey (by rw [p.keyLength]; omega_using [])
  have hpfield : L.fields .pLen = BitVec.ofNat 64 p.pLen := hp
  have hqfield : L.fields .qLen = BitVec.ofNat 64 p.qLen := hq
  exact ⟨h.inputOperand .g .pLen (by decide) (by decide) hgsrc
      (by change L.fields .pLen = BitVec.ofNat 64 p.components.g.length; rw [hglen]; exact hpfield),
    h.inputOperand .y .pLen (by decide) (by decide) hysrc
      (by change L.fields .pLen = BitVec.ofNat 64 p.components.y.length; rw [hylen]; exact hpfield),
    h.inputOperand .q .qLen (by decide) (by decide) hqsrc (by rw [hqlen]; exact hqfield)⟩

def ValidatingInitialized (p : VerifyingInput) (original : State)
    (hp : original.gpr .rdx = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .rcx = BitVec.ofNat 64 p.qLen) (s : State) : Prop :=
  ∃ pi qi,
    Ready ((p.layout original hp hq).withInverses pi qi) s ∧
    (OperandBytes s p.base usedBytes Core.generator p.components.g ∧
      OperandBytes s p.base usedBytes Core.publicValue p.components.y ∧
      OperandBytes s p.base usedBytes ⟨.input .q, .qLen⟩ p.components.q) ∧
    word s.mem p.base Field.mask.offset = mask true ∧
    (∀ i < 6, word s.mem p.base (8 * i) = original.gpr (saved.getD i .rax)) ∧
    InScr p.base usedBytes original.mem s.mem ∧ Keep coreRegs original s

theorem validatingInitialize_ok {p : VerifyingInput} {original s : State} (h : ValidatingPre p original)
    (hs : VerifyingShapePost p original h.pLength h.qLength s) (ha : p.accepted = true) :
    WP isa SignVerify.workspaces s (ValidatingInitialized p original h.pLength h.qLength) := by
  let L := p.layout original h.pLength h.qLength
  have hkey := h.keySource.congrK hs.frame hs.keep
  have hps : Src s L.base usedBytes (L.fields .p) p.components.p := source_take hkey
  have hqs : Src s L.base usedBytes (L.fields .q) p.components.q := by
    change Src s p.base usedBytes (original.gpr .rdi + original.gpr .rdx) p.components.q
    rw [h.pLength]
    exact source_slice hkey (by rw [p.keyLength]; omega_using [])
  obtain ⟨_, hpo, hqo⟩ := p.shapeFacts ha
  refine WP.mono (workspacesReady_ok (L := L) hs.scratch hs.rdi hs.fields hps hqs p.components.pLength
    p.components.qLength rfl rfl hpo hqo) fun t ⟨pi, qi, hr, hf, hm, hk⟩ => ?_
  have hframe : InScr p.base usedBytes s.mem t.mem := InScr.of_outside hf (by decide)
  have hfull := hs.frame.trans hframe
  have hkeep := hs.keep.trans hk
  refine ⟨pi, qi, hr, validatingOperands hr (h.keySource.congrK hfull hkeep), ?_, ?_, hfull,
    hkeep.mono (by decide)⟩
  · exact hm.trans ((hs.fields .mask).trans (congrArg mask ha))
  · intro i hi
    exact (hf.word (Or.inl (by omega_using [hi])) (by omega_using [hi])).trans (hs.saved i hi)

def ValidatingPost (p : VerifyingInput) (original t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key).toNat ∧
  (∀ i < 6, t.gpr (saved.getD i .rax) = original.gpr (saved.getD i .rax)) ∧
  InScr p.base usedBytes original.mem t.mem ∧ Keep coreRegs original t

theorem validatingBody_ok (M : Mont) (Sq : MontS) {p : VerifyingInput} {original s : State}
    (h : ValidatingPre p original)
    (hi : ValidatingInitialized p original h.pLength h.qLength s) (ha : p.accepted = true) :
    WP isa (seqs [Checks.publicKey Sq.mm M.mm, .block SignVerify.result]) s (ValidatingPost p original) := by
  obtain ⟨pi, qi, hr, ⟨hg, hy, hqb⟩, hm, hsave, hf, hk⟩ := hi
  let L := (p.layout original h.pLength h.qLength).withInverses pi qi
  obtain ⟨hsize, hpodd, hqodd⟩ := p.shapeFacts ha
  obtain ⟨hp, hq, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  have hpf : L.modulus ≤ 256 ^ L.pLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.components.p
    rw [p.components.pLength] at hh
    exact Nat.le_of_lt hh
  have hqf : L.subgroup ≤ 256 ^ L.qLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.components.q
    rw [p.components.qLength] at hh
    exact Nat.le_of_lt hh
  have he : Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key =
      publicAccepted L p.components.g p.components.y true := by
    rw [publicAccepted_spec L p.components.g p.components.y hsize hpodd hqodd]
    simp only [Spec.Dsa.validatePublicKeyBytes, p.lengths, decide_true, Bool.not_true,
      p.keyLength, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    rfl
  refine WP.seq (WP.mono (publicKey_ok M Sq hr hp hq hpodd hqodd hpf hqf hg hy hqb
    p.components.gLength p.components.yLength p.components.qLength rfl hm)
    fun t ⟨ht, hmask, _, hframe, hkeep⟩ => ?_)
  refine WP.mono (result_ok ht.scratch ht.parent.rdi (by decide) hmask) fun u ⟨hret, hsaved, hmem, hku⟩ => ?_
  refine ⟨?_, fun i hi => ?_, ?_, ((hk.trans hkeep).trans hku).mono (by decide)⟩
  · rw [he]; exact hret
  · exact ((hsaved i hi).trans (hframe.word (Or.inl (by omega_using [hi])) (by omega_using [hi]))).trans (hsave i hi)
  · rw [hmem]
    exact hf.trans (InScr.of_outside hframe (by decide))

theorem validatingMain_ok (M : Mont) (Sq : MontS) {p : VerifyingInput} {s0 : State} (h : ValidatingPre p s0) :
    WP isa (Prevalidated.validate Sq.mm M.mm) s0 (ValidatingPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (validatingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
    · change eval .e s = some true
      simp only [eval, hs.branch, ha, Bool.not_false]
    · have hp := shapeAccepted_false ha (Spec.Dsa.decodeBE p.components.g)
      change ¬ Spec.Dsa.parametersValid (Spec.Dsa.publicKeyBytes p.pLen p.qLen p.key).params at hp
      have hv : Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key = false := by
        simp only [Spec.Dsa.validatePublicKeyBytes, p.lengths, decide_true, Bool.not_true,
          p.keyLength, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        simp only [hp, decide_false, Bool.false_and]
      refine WP.mono (verifyFailure_ok hs.scratch hs.rdi (by decide))
        fun t ⟨hret, hsave, hmem, hk⟩ => ?_
      exact ⟨by rw [hv]; exact hret, fun i hi => (hsave i hi).trans (hs.saved i hi),
        by rw [hmem]; exact hs.frame, (hs.keep.trans hk).mono (by decide)⟩
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
    · change eval .e s = some false
      simp only [eval, hs.branch, ha, Bool.not_true]
    · refine WP.seq (WP.mono (validatingInitialize_ok h hs ha) fun t ht => ?_)
      exact validatingBody_ok M Sq h ht ha

end VG.Proof.Dsa.X86_64

end

end

/-! # Constant time of the x86-64 DSA public-key validator

Every input is public: two calls with the same pointers, lengths and key
bytes take the same path, whatever their scratch holds. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure ValidatingCall where
  input : VerifyingInput
  original : State
  pre : ValidatingPre input original

abbrev ValidatingCall.layout (c : ValidatingCall) : ExecutionLayout :=
  c.input.layout c.original c.pre.pLength c.pre.qLength

structure ValidatingAgrees (reference c : ValidatingCall) : Prop where
  layout : c.layout = reference.layout
  key : c.input.key = reference.input.key

def ValidatingStart (reference : ValidatingCall) (s : State) : Prop :=
  ∃ c : ValidatingCall, ValidatingAgrees reference c ∧ c.original = s

def ValidatingEntered (reference : ValidatingCall) (s : State) : Prop :=
  ∃ c : ValidatingCall, ValidatingAgrees reference c ∧
    VerifyEntryPost c.original c.input.base c.input.digestPointer
      (BitVec.ofNat 64 c.input.digest.length) s

def ValidatingShaped (reference : ValidatingCall) (s : State) : Prop :=
  ∃ c : ValidatingCall, ValidatingAgrees reference c ∧
    VerifyingShapePost c.input c.original c.pre.pLength c.pre.qLength s

def ValidatingReady (reference : ValidatingCall) (s : State) : Prop :=
  ∃ c : ValidatingCall, ValidatingAgrees reference c ∧
    ValidatingInitialized c.input c.original c.pre.pLength c.pre.qLength s

theorem ValidatingAgrees.pLen {reference c : ValidatingCall} (h : ValidatingAgrees reference c) :
    c.input.pLen = reference.input.pLen := congrArg ExecutionLayout.pLen h.layout

theorem ValidatingAgrees.qLen {reference c : ValidatingCall} (h : ValidatingAgrees reference c) :
    c.input.qLen = reference.input.qLen := congrArg ExecutionLayout.qLen h.layout

theorem ValidatingAgrees.pb {reference c : ValidatingCall} (h : ValidatingAgrees reference c) :
    c.input.components.p = reference.input.components.p := by
  change c.input.key.take c.input.pLen = reference.input.key.take reference.input.pLen
  rw [h.key, h.pLen]

theorem ValidatingAgrees.qb {reference c : ValidatingCall} (h : ValidatingAgrees reference c) :
    c.input.components.q = reference.input.components.q := by
  change (c.input.key.drop c.input.pLen).take c.input.qLen =
    (reference.input.key.drop reference.input.pLen).take reference.input.qLen
  rw [h.key, h.pLen, h.qLen]

theorem ValidatingAgrees.accepted {reference c : ValidatingCall} (h : ValidatingAgrees reference c) :
    c.input.accepted = reference.input.accepted := by
  unfold VerifyingInput.accepted
  congr 1
  · exact h.pb
  · exact h.qb

theorem validateEntry_ct : RelCT isa (Two (fun B : Addr => fun s => s.gpr .r8 = B))
    (.block Prevalidated.validateEntry) (fun _ _ => True) :=
  two_taint [.r8] (pins_of (fun B _ => B) (by
    intro B s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h)) (by taint_decide)

theorem validatingEntered_ct : RelCT isa (Two ValidatingStart) (.block Prevalidated.validateEntry)
    (Two ValidatingEntered) := by
  refine two_post (two_map (fun c : ValidatingCall => c.layout.base) ?_ validateEntry_ct) ?_
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact c.pre.base.trans (congrArg ExecutionLayout.base ha.layout)
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact WP.mono (validateEntry_ok c.pre.scratch c.pre.base (by decide) c.pre.digestPointer
      (by rw [c.pre.digestNil]; rfl)) fun t ht => ⟨c, ha, ht⟩

def ValidatingCall.shape (c : ValidatingCall) : ShapePublic where
  base := c.layout.base
  extent := usedBytes
  pPointer := c.layout.fields .p
  qPointer := c.layout.fields .q
  pBytes := c.input.components.p
  qBytes := c.input.components.q
  digestLen := 0
  extentBound := by decide
  pPositive := by rw [c.input.components.pLength]; have := c.layout.widths; change 0 < c.layout.pLen; omega_using [this]
  qPositive := by rw [c.input.components.qLength]; exact c.layout.widths.1
  pBound := by rw [c.input.components.pLength]; have := c.layout.widths; change c.layout.pLen < 2 ^ 64; omega_using [this]
  qBound := by rw [c.input.components.qLength]; have := c.layout.widths; change c.layout.qLen < 2 ^ 64; omega_using [this]
  digestBound := by decide

theorem ValidatingAgrees.shape {reference c : ValidatingCall} (h : ValidatingAgrees reference c) :
    c.shape = reference.shape := by
  unfold ValidatingCall.shape
  congr 1
  · exact congrArg ExecutionLayout.base h.layout
  · exact congrArg (fun L => L.fields .p) h.layout
  · exact congrArg (fun L => L.fields .q) h.layout
  · exact h.pb
  · exact h.qb

theorem ValidatingEntered.context {reference : ValidatingCall} {s : State} (h : ValidatingEntered reference s) :
    ShapeContext reference.shape s := by
  obtain ⟨c, ha, he⟩ := h
  rw [← ha.shape]
  have hf : InScr c.input.base usedBytes c.original.mem s.mem := InScr.of_outside he.frame (by decide)
  have hkey := c.pre.keySource.congrK hf he.keep
  refine ⟨c.pre.scratch.congr he.keep.2.2, he.base, he.p, he.q, ?_, ?_, ?_, source_take hkey, ?_⟩
  · change word s.mem c.input.base Field.pLen.offset = BitVec.ofNat 64 c.input.components.p.length
    rw [c.input.components.pLength]
    exact he.pLen.trans c.pre.pLength
  · change word s.mem c.input.base Field.qLen.offset = BitVec.ofNat 64 c.input.components.q.length
    rw [c.input.components.qLength]
    exact he.qLen.trans c.pre.qLength
  · change word s.mem c.input.base Field.digestLen.offset = BitVec.ofNat 64 0
    rw [he.digestLen, c.pre.digestNil]; rfl
  · change Src s c.input.base usedBytes (c.original.gpr .rdi + c.original.gpr .rdx) c.input.components.q
    rw [c.pre.pLength]
    exact source_slice hkey (by rw [c.input.keyLength]; omega_using [])

theorem validatingShape_ct : RelCT isa (Two ValidatingStart)
    (.seq (.block Prevalidated.validateEntry) Checks.domainShape) (Two ValidatingShaped) := by
  refine two_post (RelCT.seq validatingEntered_ct
    (two_map ValidatingCall.shape (fun _ _ h => h.context) domainShape_ct)) ?_
  intro reference s ⟨c, ha, hs⟩
  subst s
  exact WP.mono (validatingShape_ok c.pre) fun t ht => ⟨c, ha, ht⟩

theorem ValidatingShaped.branch {reference : ValidatingCall} {s : State} (h : ValidatingShaped reference s) :
    eval .e s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  change s.zf = _
  rw [hs.branch, ha.accepted]

theorem ValidatingShaped.rdi {reference : ValidatingCall} {s : State} (h : ValidatingShaped reference s) :
    s.gpr .rdi = reference.layout.base := by
  obtain ⟨c, ha, hs⟩ := h
  exact hs.rdi.trans (congrArg ExecutionLayout.base ha.layout)

def ValidatingCall.initialization (c : ValidatingCall) (ha : c.input.accepted = true) : InitializationPublic where
  layout := c.layout
  pBytes := c.input.components.p
  qBytes := c.input.components.q
  pLength := c.input.components.pLength
  qLength := c.input.components.qLength
  pValue := rfl
  qValue := rfl
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2

theorem ValidatingShaped.initialization {reference : ValidatingCall} {s : State}
    (h : ValidatingShaped reference s) (ha : reference.input.accepted = true) :
    InitializationPre (reference.initialization ha) s := by
  obtain ⟨c, hag, hs⟩ := h
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  have hr : s.gpr .rdi = c.layout.base := hs.rdi
  have hscr : Scr s c.layout.base usedBytes := hs.scratch
  have hkey := c.pre.keySource.congrK hs.frame hs.keep
  have hps : Src s c.layout.base usedBytes (c.layout.fields .p) c.input.components.p := source_take hkey
  have hqs : Src s c.layout.base usedBytes (c.layout.fields .q) c.input.components.q := by
    change Src s c.input.base usedBytes (c.original.gpr .rdi + c.original.gpr .rdx) c.input.components.q
    rw [c.pre.pLength]
    exact source_slice hkey (by rw [c.input.keyLength]; omega_using [])
  rw [hag.layout] at hf hr hscr hps hqs
  rw [hag.pb] at hps
  rw [hag.qb] at hqs
  exact ⟨hscr, hr, hf, hps, hqs⟩

abbrev AcceptedValidatingCall := {c : ValidatingCall // c.input.accepted = true}

theorem validatingWorkspaces_ct : RelCT isa (Two (fun c : AcceptedValidatingCall => ValidatingShaped c.val))
    SignVerify.workspaces (Two (fun c : AcceptedValidatingCall => ValidatingReady c.val)) := by
  refine two_post ((two_map (fun c : AcceptedValidatingCall => c.val.initialization c.property)
    (fun c _ h => h.initialization c.property) initialization_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro reference s ⟨c, ha, hs⟩
  have hac : c.input.accepted = true := ha.accepted.trans reference.property
  exact WP.mono (validatingInitialize_ok c.pre hs hac) fun t ht => ⟨c, ha, ht⟩

/-- The domain's operands, as the schedule reads them. -/
def validatingInputs (p : SchedulePublic) : List (Operand × Nat) :=
  [(Core.publicValue, p.layout.pLen), (⟨.input .q, .qLen⟩, p.layout.qLen), (Core.generator, p.layout.pLen)]

theorem validatingInputs_stable (p : SchedulePublic) (a : Operand × Nat)
    (ha : a ∈ validatingInputs p) : a.1.length ≠ .mask ∧ stablePointer a.1.pointer := by
  simp only [validatingInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · simp [Core.publicValue, stablePointer]
  · change Field.qLen ≠ .mask ∧ Field.q ≠ .mask
    decide
  · simp [Core.generator, stablePointer]

def ValidatingCall.schedule (c : ValidatingCall) (ha : c.input.accepted = true) (pi qi : BitVec 64) :
    SchedulePublic where
  layout := c.layout.withInverses pi qi
  digestLen := 0
  pGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).1
  qGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).2.1
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2
  pFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.components.p
    rw [c.input.components.pLength] at h
    exact Nat.le_of_lt h
  qFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.components.q
    rw [c.input.components.qLength] at h
    exact Nat.le_of_lt h
  digestBound := by decide

theorem ValidatingReady.body {reference : ValidatingCall} {s : State} (ha : reference.input.accepted = true)
    (h : ValidatingReady reference s) :
    ∃ pi qi, PublicKeyPre validatingInputs (reference.schedule ha pi qi) s := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, _, _, _⟩ := h
  have hmask : word s.mem c.layout.base Field.mask.offset = mask true := hm
  change Ready (c.layout.withInverses pi qi) s at hr
  change (OperandBytes s c.layout.base usedBytes Core.generator c.input.components.g ∧
    OperandBytes s c.layout.base usedBytes Core.publicValue c.input.components.y ∧
    OperandBytes s c.layout.base usedBytes ⟨.input .q, .qLen⟩ c.input.components.q) at ho
  rw [hag.layout] at hr ho hmask
  have hgl : c.input.components.g.length = reference.layout.pLen := c.input.components.gLength.trans hag.pLen
  have hyl : c.input.components.y.length = reference.layout.pLen := c.input.components.yLength.trans hag.pLen
  have hql : c.input.components.q.length = reference.layout.qLen := c.input.components.qLength.trans hag.qLen
  refine ⟨pi, qi, ⟨hr, ?_, ⟨true, hmask⟩⟩, c.input.components.q, ho.2.2, hql, ?_⟩
  · intro a ha
    simp only [validatingInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨_, ho.2.1, hyl⟩
    · exact ⟨_, ho.2.2, hql⟩
    · exact ⟨_, ho.1, hgl⟩
  · change Spec.Dsa.decodeBE c.input.components.q = Spec.Dsa.decodeBE reference.input.components.q
    rw [hag.qb]

theorem validatingReady_related {s₁ s₂ : State}
    (h : Two (fun c : AcceptedValidatingCall => ValidatingReady c.val) s₁ s₂) :
    Two (PublicKeyPre validatingInputs) s₁ s₂ := by
  obtain ⟨reference, h₁, h₂⟩ := h
  obtain ⟨pi₁, qi₁, h₁⟩ := h₁.body reference.property
  obtain ⟨pi₂, qi₂, h₂⟩ := h₂.body reference.property
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁.1.1 h₂.1.1
    (reference.val.input.shapeFacts reference.property).2.1
    (reference.val.input.shapeFacts reference.property).2.2
  exact ⟨_, h₁, h₂⟩

theorem validatingBody_ct (M : Mont) (Sq : MontS) : RelCT isa (Two (PublicKeyPre validatingInputs))
    (seqs [Checks.publicKey Sq.mm M.mm, .block SignVerify.result]) (fun _ _ => True) := by
  have h1 := publicKey_ct M Sq validatingInputs (fun p => validatingInputs_stable p)
    (by intro p; simp [validatingInputs]) (by intro p; simp [validatingInputs])
    (by intro p; simp [validatingInputs])
  unfold seqs
  refine RelCT.seq h1 ?_
  exact two_map (fun p => p.layout.base) (fun _ _ h => h.1.parent.rdi) result_ct

theorem validatingSuccess_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two (fun c : AcceptedValidatingCall => ValidatingShaped c.val))
      (seqs [SignVerify.workspaces, Checks.publicKey Sq.mm M.mm, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq validatingWorkspaces_ct ?_
  exact (validatingBody_ct M Sq).mono (fun _ _ h => validatingReady_related h) (fun _ _ h => h)

theorem validatingMain_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two ValidatingStart) (Prevalidated.validate Sq.mm M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq validatingShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map (fun c : ValidatingCall => c.layout.base) (fun _ _ h => h.rdi) verifyFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (validatingSuccess_ct M Sq).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval .e s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.VerifyingABIPre`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.VerifyingABI`, which this module and modules that import it used -/

section

/-! # The shared verification contract as machine-level resources -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem stackArgs_four (s : State) : List.map (stackArg s) (List.range 4) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

structure VerifyingABI (s : State) : Prop where
  stackBound : (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
    ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArgAddr s 0, 32⟩]
  wr : s.wr = [⟨stackArg s 2, (stackArg s 3).toNat * 8⟩]
  keyScratch : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
  signatureScratch : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
  digestScratch : (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
  scratchArgs : (⟨stackArg s 2, (stackArg s 3).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 32⟩
  retScratch : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
  keyBound : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  signatureBound : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  digestBound : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  scratchBound : (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .rdx).toNat (s.gpr .rcx).toNat
  keyLength : (s.gpr .rsi).toNat = 3 * (s.gpr .rdx).toNat + (s.gpr .rcx).toNat
  signatureLength : (s.gpr .r9).toNat = 2 * (s.gpr .rcx).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .rdx).toNat ≤ (stackArg s 3).toNat

def VerifyingABI.input {s : State} (h : VerifyingABI s) : VerifyingInput where
  base := stackArg s 2
  digestPointer := stackArg s 0
  pLen := (s.gpr .rdx).toNat
  qLen := (s.gpr .rcx).toNat
  key := Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
  signature := Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
  digest := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
  lengths := h.lengths
  keyLength := (bytesAt_length _ _ _).trans h.keyLength
  signatureLength := (bytesAt_length _ _ _).trans h.signatureLength
  digestBound := by rw [bytesAt_length]; exact (stackArg s 1).isLt

theorem VerifyingABI.used {s : State} (h : VerifyingABI s) : usedBytes ≤ (stackArg s 3).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 15712 ≤ _
  omega_using [hl, hs]

end VG.Proof.Dsa.X86_64

end

end

/-! # Buffer and stack resources for a complete verification call -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem VerifyingABI.pre {s : State} (h : VerifyingABI s) : VerifyingPre h.input s := by
  have hs : Scr s (stackArg s 2) ((stackArg s 3).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  have hargs : (⟨stackArgAddr s 0, 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine ⟨scratch_prefix hs h.used (by decide), ?_, ?_, ?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · exact (ofNat_toNat64 _).symm
  · intro j hj hb
    exact stackWord_read (count := 4) hargs hj (by omega_using [hb]) (by decide)
  · intro j hj hb i hi
    exact Nat.le_trans h.used (stackWord_separate (count := 4) h.scratchArgs hj (by omega_using [hb]) (by decide) i hi)
  · exact (ofNat_toNat64 _).symm
  · change stackArg s 1 = BitVec.ofNat 64 (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat).length
    rw [bytesAt_length, ofNat_toNat64]
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .rsi).isLt) h.keyScratch) h.used
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .r9).isLt) h.signatureScratch) h.used
  · exact source_shrink (src_of_region (p := stackArg s 0) (by rw [h.rd]; simp)
      (Nat.le_of_lt (stackArg s 1).isLt) h.digestScratch) h.used

def VerifyingABI.call {s : State} (h : VerifyingABI s) : VerifyingCall := ⟨h.input, s, h.pre⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.VerifyingVerified`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.VerifyingAgreement`, which this module and modules that import it used -/

section

/-! # Only the verifying ABI's declared public observations determine its schedule -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem verifyingLayout_eq {p₁ p₂ : VerifyingInput} {s₁ s₂ : State}
    {hp₁ : s₁.gpr .rdx = BitVec.ofNat 64 p₁.pLen} {hp₂ : s₂.gpr .rdx = BitVec.ofNat 64 p₂.pLen}
    {hq₁ : s₁.gpr .rcx = BitVec.ofNat 64 p₁.qLen} {hq₂ : s₂.gpr .rcx = BitVec.ofNat 64 p₂.qLen}
    (hb : p₁.base = p₂.base) (hp : p₁.pLen = p₂.pLen) (hq : p₁.qLen = p₂.qLen)
    (hd : p₁.digestPointer = p₂.digestPointer) (hdl : p₁.digest.length = p₂.digest.length)
    (hpb : p₁.components.p = p₂.components.p) (hqb : p₁.components.q = p₂.components.q)
    (hdi : s₁.gpr .rdi = s₂.gpr .rdi) (hdx : s₁.gpr .rdx = s₂.gpr .rdx)
    (h8 : s₁.gpr .r8 = s₂.gpr .r8) (hcx : s₁.gpr .rcx = s₂.gpr .rcx) :
    p₁.layout s₁ hp₁ hq₁ = p₂.layout s₂ hp₂ hq₂ := by
  have hac : p₁.accepted = p₂.accepted := by
    unfold VerifyingInput.accepted
    congr 1
  have hprefix : p₁.prefixLength = p₂.prefixLength := by
    unfold VerifyingInput.prefixLength
    rw [hdl, hqb]
  have hfields : verifyFieldValues s₁ p₁.digestPointer
      (BitVec.ofNat 64 p₁.digest.length) (BitVec.ofNat 64 p₁.prefixLength) p₁.accepted =
      verifyFieldValues s₂ p₂.digestPointer
      (BitVec.ofNat 64 p₂.digest.length) (BitVec.ofNat 64 p₂.prefixLength) p₂.accepted := by
    funext f
    cases f <;> simp only [verifyFieldValues, hd, hdl, hprefix, hac, hdi, hdx, h8, hcx]
  unfold VerifyingInput.layout
  congr 1
  · exact congrArg Spec.Dsa.decodeBE hpb
  · exact congrArg Spec.Dsa.decodeBE hqb

theorem verifyingAgreement {s₁ s₂ : State} (h₁ : VerifyingABI s₁) (h₂ : VerifyingABI s₂)
    (hdi : s₁.gpr .rdi = s₂.gpr .rdi) (hdx : s₁.gpr .rdx = s₂.gpr .rdx)
    (h8 : s₁.gpr .r8 = s₂.gpr .r8) (hcx : s₁.gpr .rcx = s₂.gpr .rcx)
    (hsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (a0 : stackArg s₁ 0 = stackArg s₂ 0) (a1 : stackArg s₁ 1 = stackArg s₂ 1)
    (a2 : stackArg s₁ 2 = stackArg s₂ 2)
    (hpub : h₁.input.key.take (3 * h₁.input.pLen + h₁.input.qLen) =
      h₂.input.key.take (3 * h₂.input.pLen + h₂.input.qLen)) : VerifyingAgrees h₂.call h₁.call := by
  have hp : h₁.input.pLen = h₂.input.pLen := congrArg BitVec.toNat hdx
  have hq : h₁.input.qLen = h₂.input.qLen := congrArg BitVec.toNat hcx
  have hdl : h₁.input.digest.length = h₂.input.digest.length := by
    change (Spec.Rsa.bytesAt _ _ _).length = (Spec.Rsa.bytesAt _ _ _).length
    rw [bytesAt_length, bytesAt_length, a1]
  rw [← hp, ← hq] at hpub
  have hpb : h₁.input.components.p = h₂.input.components.p := by
    have he := prefix_component_eq (offset := 0) (len := h₁.input.pLen) hpub (by omega_using [])
    simp only [List.drop_zero] at he
    change h₁.input.key.take h₁.input.pLen = h₂.input.key.take h₂.input.pLen
    rw [← hp]
    exact he
  have hqb : h₁.input.components.q = h₂.input.components.q := by
    have he := prefix_component_eq (offset := h₁.input.pLen) (len := h₁.input.qLen) hpub (by omega_using [])
    change (h₁.input.key.drop h₁.input.pLen).take h₁.input.qLen = (h₂.input.key.drop h₂.input.pLen).take h₂.input.qLen
    rw [← hp, ← hq]
    exact he
  exact ⟨verifyingLayout_eq a2 hp hq a0 hdl hpb hqb hdi hdx h8 hcx, hpb, hqb, hdl, hsp⟩

theorem verifyingPublicRelated {s₁ s₂ : State} (h₁ : VerifyingABI s₁) (h₂ : VerifyingABI s₂)
    (h : (Spec.Dsa.verifyContract abi).pub s₁ s₂) : Two VerifyingStart s₁ s₂ := by
  sig_pub [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, hdi, _, hdx, hcx, h8, _, a0, a1, a2, _⟩ := h
  have hpub := (List.append_inj' hl (List.length_singleton.trans List.length_singleton.symm)).1
  have hb := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hpub
  exact ⟨h₂.call, ⟨h₁.call, verifyingAgreement h₁ h₂ hdi hdx h8 hcx hsp a0 a1 a2 hb, rfl⟩,
    ⟨h₂.call, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.VerifyingABIPost`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.VerifyingMain`, which only this module used -/

section

/-! # Functional correctness of the complete x86-64 DSA verification program -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem verifyingSuccess_ok (M : Mont) (Sq : MontS) {p : VerifyingInput} {original st : State} (h : VerifyingPre p original)
    (hs : VerifyingShapePost p original h.pLength h.qLength st) (ha : p.accepted = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.publicKey Sq.mm M.mm,
      Checks.range qWorkspace Core.signatureR, Checks.range qWorkspace Core.signatureS,
      Core.verify Sq.mm M.mm, Checks.equal (Core.scalar u) Core.signatureR, .block SignVerify.result]) st
      (VerifyingPost p original) := by
  refine WP.seq (WP.mono (verifyingInitialize_ok h hs ha) fun t ht => ?_)
  have hb := verifyingAccepted_ok M Sq h ht ha
  apply wpAppendSequences (a := [Checks.publicKey Sq.mm M.mm,
    Checks.range qWorkspace Core.signatureR, Checks.range qWorkspace Core.signatureS,
    Core.verify Sq.mm M.mm, Checks.equal (Core.scalar u) Core.signatureR])
    (b := [.block SignVerify.result]) (by simp) (by simp)
  exact WP.seq_iff.mp hb

theorem verifyingMain_ok (M : Mont) (Sq : MontS) {p : VerifyingInput} {s0 : State} (h : VerifyingPre p s0) :
    WP isa (SignVerify.verify Sq.mm M.mm) s0 (VerifyingPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (verifyingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => verifyingRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change eval .e s = some true
    simp only [eval, hs.branch, ha, Bool.not_false]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => verifyingSuccess_ok M Sq h hs ha)
    change eval .e s = some false
    simp only [eval, hs.branch, ha, Bool.not_true]

end VG.Proof.Dsa.X86_64

end

end

/-! # Verification correctness and ABI preservation against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem verifyingGprPreserved {s t : State} (h : VerifyingABI s) (hp : VerifyingPost h.input s t) :
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

theorem verifyStatus_u32 (result : Bool) :
    ((BitVec.ofNat 64 result.toNat).setWidth 32).toNat = if result then 1 else 0 := by
  cases result <;> rfl

end VG.Proof.Dsa.X86_64

end

end

/-! # DSA verifying verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum.X86_64

/-- An ordinary 1024/160 call with disjoint buffers and an empty digest.
The all-zero key is allowed by the contract and is rejected by the program. -/
def verifyingSatState : State where
  gpr r := match r with
    | .rdi => 0x2000 | .rsi => 404 | .rdx => 128 | .rcx => 20
    | .r8 => 0x4000 | .r9 => 40 | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10009 then 0x50 else if a = 0x10019 then 0x80
    else if a = 0x10021 then 8 else 0
  rd := [⟨0x2000, 404⟩, ⟨0x4000, 40⟩, ⟨0x5000, 0⟩, ⟨0x10008, 32⟩]
  wr := [⟨0x8000, 16384⟩]

end VG.Proof.Dsa.X86_64

end

end

/-! # x86-64 DSA public-key validation and prevalidated verification against the shared contracts

`validating_verified` and `prevalidated_verified` are the programs' proofs;
`validating_call_verified` and `prevalidated_call_verified` are those of
the code that calls the Montgomery kernels, whose return addresses take
eight bytes of stack. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Rsa.X86_64

structure ValidatingABI (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩]
  wr : s.wr = [⟨s.gpr .r8, (s.gpr .r9).toNat * 8⟩]
  keyScratch : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat * 8⟩
  retKey : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  retScratch : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat * 8⟩
  keyBound : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  scratchBound : (s.gpr .r8).toNat + (s.gpr .r9).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .rdx).toNat (s.gpr .rcx).toNat
  keyLength : (s.gpr .rsi).toNat = 3 * (s.gpr .rdx).toNat + (s.gpr .rcx).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .rdx).toNat ≤ (s.gpr .r9).toNat

theorem validatingABI_of {s : State} (h : (Spec.Dsa.validatePublicKeyContract abi).pre s) : ValidatingABI s := by
  sig_pre [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argRegs, stackArgs_zero] at h
  sig_split h
  constructor <;> with_reducible assumption

def ValidatingABI.input {s : State} (h : ValidatingABI s) : VerifyingInput where
  base := s.gpr .r8
  digestPointer := 0
  pLen := (s.gpr .rdx).toNat
  qLen := (s.gpr .rcx).toNat
  key := Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
  signature := List.replicate (2 * (s.gpr .rcx).toNat) 0
  digest := []
  lengths := h.lengths
  keyLength := (bytesAt_length _ _ _).trans h.keyLength
  signatureLength := List.length_replicate
  digestBound := by decide

theorem ValidatingABI.used {s : State} (h : ValidatingABI s) : usedBytes ≤ (s.gpr .r9).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 15712 ≤ _
  omega_using [hl, hs]

theorem ValidatingABI.pre {s : State} (h : ValidatingABI s) : ValidatingPre h.input s := by
  have hs : Scr s (s.gpr .r8) ((s.gpr .r9).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  exact ⟨scratch_prefix hs h.used (by decide), (ofNat_toNat64 _).symm, (ofNat_toNat64 _).symm, rfl,
    source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .rsi).isLt) h.keyScratch) h.used,
    rfl, rfl⟩

def ValidatingABI.call {s : State} (h : ValidatingABI s) : ValidatingCall := ⟨h.input, s, h.pre⟩

theorem validatingGprPreserved {s t : State} (h : ValidatingABI s) (hp : ValidatingPost h.input s t) :
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

theorem validatingSharedPost {s t : State} (h : ValidatingABI s) (hp : ValidatingPost h.input s t) :
    (Spec.Dsa.validatePublicKeyContract abi).post s t := by
  sig_post [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argRegs, stackArgs_zero]
  rw [hp.1]
  change _ = if Spec.Dsa.validatePublicKeyBytes h.input.pLen h.input.qLen h.input.key = true then 1 else 0
  cases Spec.Dsa.validatePublicKeyBytes h.input.pLen h.input.qLen h.input.key <;> rfl

theorem validatingCorrect (M : Mont) (Sq : MontS)
    (hmx : (Prevalidated.validate Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : (Spec.Dsa.validatePublicKeyContract abi).pre s) :
    ∃ trace t, Exec isa (Prevalidated.validate Sq.mm M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.validatePublicKeyContract abi).post s t := by
  have ha := validatingABI_of h
  obtain ⟨trace, t, he, hp⟩ := validatingMain_ok M Sq ha.pre
  exact ⟨trace, t, he, abiPreserved_of_exec hmx he (validatingGprPreserved ha hp), validatingSharedPost ha hp⟩

theorem validatingPublicRelated {s₁ s₂ : State} (h₁ : ValidatingABI s₁) (h₂ : ValidatingABI s₂)
    (h : (Spec.Dsa.validatePublicKeyContract abi).pub s₁ s₂) : Two ValidatingStart s₁ s₂ := by
  sig_pub [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argRegs, stackArgs_zero] at h
  obtain ⟨_, hl, hdi, _, hdx, hcx, h8, _⟩ := h
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
  exact ⟨h₂.call, ⟨h₁.call, ⟨hlayout, hkey⟩, rfl⟩, ⟨h₂.call, ⟨rfl, rfl⟩, rfl⟩⟩

theorem validatingConstantTime (M : Mont) (Sq : MontS) :
    ConstantTime isa (Spec.Dsa.validatePublicKeyContract abi).pre
      (Spec.Dsa.validatePublicKeyContract abi).pub (Prevalidated.validate Sq.mm M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (validatingMain_ct M Sq _ _ _ _ _ _
    (validatingPublicRelated (validatingABI_of h₁) (validatingABI_of h₂) hp) e₁ e₂).1

/-- An ordinary 1024/160 call with disjoint buffers. The all-zero domain is
allowed by the contract and rejected by the program. -/
def validatingSatState : State where
  gpr r := match r with
    | .rdi => 0x2000 | .rsi => 404 | .rdx => 128 | .rcx => 20
    | .r8 => 0x8000 | .r9 => 2048 | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 404⟩]
  wr := [⟨0x8000, 16384⟩]

theorem validatingSatisfiable : ∃ s, (Spec.Dsa.validatePublicKeyContract abi).pre s := by
  sig_implies_sat [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argRegs, stackArgs_zero]
    [validatingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using validatingSatState

theorem validating_verified (M : Mont) (Sq : MontS)
    (hmx : (Prevalidated.validate Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (Prevalidated.validate Sq.mm M.mm) (Spec.Dsa.validatePublicKeyContract abi) :=
  ⟨validatingCorrect M Sq hmx, validatingConstantTime M Sq, validatingSatisfiable⟩

theorem prevalidatedABI_of {s : State} (h : (Spec.Dsa.verifyPrevalidatedContract abi).pre s) :
    VerifyingABI s ∧ Spec.Dsa.validatePublicKeyBytes (s.gpr .rdx).toNat (s.gpr .rcx).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) = true := by
  sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four, List.range,
    List.range.loop] at h
  sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four, List.range,
    List.range.loop] at h
  sig_split h
  exact ⟨by constructor <;> with_reducible assumption, by assumption⟩

theorem prevalidatedPre_of {s : State} {stack : Nat} (h : (Spec.Dsa.verifyContract abi stack).pre s)
    (hv : Spec.Dsa.validatePublicKeyBytes (s.gpr .rdx).toNat (s.gpr .rcx).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) = true) :
    (Spec.Dsa.verifyPrevalidatedContract abi stack).pre s := by
  sig_pre [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four, List.range,
    List.range.loop] at h
  sig_pre [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four, List.range,
    List.range.loop] at h
  sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four, List.range,
    List.range.loop]
  sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four, List.range,
    List.range.loop]
  sig_split h
  sig_and_intros <;> with_reducible assumption

theorem prevalidatedSharedPost {s t : State} (h : VerifyingABI s) (hp : VerifyingPost h.input s t) :
    (Spec.Dsa.verifyPrevalidatedContract abi).post s t := by
  sig_post [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four]
  sig_post [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four]
  rw [hp.1, verifyStatus_u32]
  rfl

theorem prevalidatedCorrect (M : Mont) (Sq : MontS)
    (hmx : (Prevalidated.verify Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : (Spec.Dsa.verifyPrevalidatedContract abi).pre s) :
    ∃ trace t, Exec isa (Prevalidated.verify Sq.mm M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.verifyPrevalidatedContract abi).post s t := by
  obtain ⟨ha, hv⟩ := prevalidatedABI_of h
  obtain ⟨trace, t, he, hp⟩ := prevalidatedMain_ok M Sq ha.pre hv
  exact ⟨trace, t, he, abiPreserved_of_exec hmx he (verifyingGprPreserved ha hp), prevalidatedSharedPost ha hp⟩

theorem prevalidatedConstantTime (M : Mont) (Sq : MontS) :
    ConstantTime isa (Spec.Dsa.verifyPrevalidatedContract abi).pre
      (Spec.Dsa.verifyPrevalidatedContract abi).pub (Prevalidated.verify Sq.mm M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  change (Spec.Dsa.verifyContract abi).pub s₁ s₂ at hp
  exact (prevalidatedMain_ct M Sq _ _ _ _ _ _
    (verifyingPublicRelated (prevalidatedABI_of h₁).1 (prevalidatedABI_of h₂).1 hp) e₁ e₂).1

/-- `verifyingSatState` with `validKeyWitness` at `0x2000`. -/
def prevalidatedSatState : State where
  gpr := verifyingSatState.gpr
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x2194 then
    VG.Proof.Dsa.validKeyWitness[a.toNat - 0x2000]?.getD 0 else verifyingSatState.mem a
  rd := verifyingSatState.rd
  wr := verifyingSatState.wr

/-- The octets of a memory that holds `l` from `base` on. -/
theorem bytesAt_window {m : Mem} {base n : Nat} {l : List Byte} (hl : l.length = n) (hb : base + n < 2 ^ 64)
    (hm : ∀ a : Addr, base ≤ a.toNat → a.toNat < base + n → m a = l[a.toNat - base]?.getD 0) :
    Spec.Rsa.bytesAt m (BitVec.ofNat 64 base) n = l := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range, hl]
  · intro i h₁ h₂
    have hi : i < n := by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h₁; exact h₁
    have e : (BitVec.ofNat 64 base + BitVec.ofNat 64 i).toNat = base + i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb, hi]),
        Nat.mod_eq_of_lt (by omega_using [hb]), Nat.mod_eq_of_lt (by omega_using [hl, hb, h₂])]
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    rw [hm _ (by omega_using [e]) (by omega_using [hi, e]), e, Nat.add_sub_cancel_left, List.getElem?_eq_getElem h₂, Option.getD_some]

theorem prevalidatedSat_key :
    Spec.Rsa.bytesAt prevalidatedSatState.mem 0x2000 404 = VG.Proof.Dsa.validKeyWitness :=
  bytesAt_window (base := 0x2000) VG.Proof.Dsa.validKeyWitness_length (by decide) fun a h₁ h₂ => by
    simp only [prevalidatedSatState]
    exact ite_eq_left ⟨h₁, h₂⟩

theorem prevalidatedSat_valid : Spec.Dsa.validatePublicKeyBytes 128 20
    (Spec.Rsa.bytesAt prevalidatedSatState.mem 0x2000 404) = true := by
  rw [prevalidatedSat_key]; exact VG.Proof.Dsa.validKeyWitness_valid

theorem prevalidatedSatisfiable : ∃ s, (Spec.Dsa.verifyPrevalidatedContract abi).pre s := by
  have ho : ∃ s, (Spec.Dsa.verifyContract abi).pre s ∧ s = prevalidatedSatState := by
    sig_implies_sat [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four]
      [prevalidatedSatState, verifyingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using prevalidatedSatState
  obtain ⟨s, h, rfl⟩ := ho
  exact ⟨_, prevalidatedPre_of h prevalidatedSat_valid⟩

theorem prevalidatedSatisfiable8 : ∃ s, (Spec.Dsa.verifyPrevalidatedContract abi 8).pre s := by
  have ho : ∃ s, (Spec.Dsa.verifyContract abi 8).pre s ∧ s = prevalidatedSatState := by
    sig_implies_sat [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four, List.range,
      List.range.loop]
      [prevalidatedSatState, verifyingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using prevalidatedSatState
  obtain ⟨s, h, rfl⟩ := ho
  exact ⟨_, prevalidatedPre_of h prevalidatedSat_valid⟩

theorem prevalidated_verified (M : Mont) (Sq : MontS)
    (hmx : (Prevalidated.verify Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (Prevalidated.verify Sq.mm M.mm) (Spec.Dsa.verifyPrevalidatedContract abi) :=
  ⟨prevalidatedCorrect M Sq hmx, prevalidatedConstantTime M Sq, prevalidatedSatisfiable⟩

theorem validating_implies8 :
    (Spec.Dsa.validatePublicKeyContract abi).Implies (Spec.Dsa.validatePublicKeyContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argRegs, stackArgs_zero,
      List.range, List.range.loop] at h
    sig_split h
    sig_pre [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argRegs, stackArgs_zero,
      List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argRegs,
    stackArgs_zero, List.range, List.range.loop]
  pub := by intro s t _ _ h; exact h
  sat := by
    sig_implies_sat [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argRegs,
      stackArgs_zero, List.range, List.range.loop]
      [validatingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using validatingSatState

theorem validating_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hp : (Spec.Dsa.validatePublicKeyContract abi).post s b) :
    (Spec.Dsa.validatePublicKeyContract abi).post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  sig_post [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argRegs, stackArgs_zero,
    List.range, List.range.loop] at hp ⊢
  simpa only [State.patch_gpr] using hp

theorem validating_call_verified (M : Mont) (Sq : MontS) {c : Prog isa}
    (hc : c.InlineOk = true) (hin : c.inline = Prevalidated.validate Sq.mm M.mm)
    (hmx : (Prevalidated.validate Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Dsa.validatePublicKeyContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ validatingCorrect M Sq hmx) (hin ▸ validatingConstantTime M Sq)
    validating_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h)
    (fun s b hv u _ _ hp => validating_patch s b hv u hp)

theorem prevalidated_implies8 :
    (Spec.Dsa.verifyPrevalidatedContract abi).Implies (Spec.Dsa.verifyPrevalidatedContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four, List.range,
      List.range.loop] at h
    sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four, List.range,
      List.range.loop] at h
    sig_split h
    sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four, List.range,
      List.range.loop]
    sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four, List.range,
      List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs,
    stackArgs_four, List.range, List.range.loop]
  pub := by intro s t _ _ h; exact h
  sat := prevalidatedSatisfiable8

theorem prevalidated_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hp : (Spec.Dsa.verifyPrevalidatedContract abi).post s b) :
    (Spec.Dsa.verifyPrevalidatedContract abi).post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  sig_post [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four, List.range,
    List.range.loop] at hp ⊢
  sig_post [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four, List.range,
    List.range.loop] at hp ⊢
  simpa only [State.patch_gpr] using hp

theorem prevalidated_call_verified (M : Mont) (Sq : MontS) {c : Prog isa}
    (hc : c.InlineOk = true) (hin : c.inline = Prevalidated.verify Sq.mm M.mm)
    (hmx : (Prevalidated.verify Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Dsa.verifyPrevalidatedContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ prevalidatedCorrect M Sq hmx) (hin ▸ prevalidatedConstantTime M Sq)
    prevalidated_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h)
    (fun s b hv u _ _ hp => prevalidated_patch s b hv u hp)

end VG.Proof.Dsa.X86_64
