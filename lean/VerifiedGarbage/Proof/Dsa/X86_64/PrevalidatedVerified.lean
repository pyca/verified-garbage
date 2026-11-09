module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Impl.Dsa.X86_64.Prevalidated
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Spec.Dsa.Prevalidated
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
public import VerifiedGarbage.Proof.Dsa.X86_64.ValidateCT
public import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedCT
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABIPre
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABIPost
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingAgreement
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingVerified
import VerifiedGarbage.Proof.Dsa.X86_64.ParametersVerified
import VerifiedGarbage.Proof.Dsa.X86_64.ABIRegions
public import VerifiedGarbage.Proof.Dsa.Validation
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig

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
  omega

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
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    rw [hm _ (by omega) (by omega), e, Nat.add_sub_cancel_left, List.getElem?_eq_getElem h₂, Option.getD_some]

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
