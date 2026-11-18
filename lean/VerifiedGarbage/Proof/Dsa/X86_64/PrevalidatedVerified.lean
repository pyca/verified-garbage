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
import VerifiedGarbage.Proof.Dsa.X86_64.ParametersVerified
import VerifiedGarbage.Proof.Dsa.X86_64.ABIRegions
public import VerifiedGarbage.Proof.Dsa.Validation
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Proof.Dsa.X86_64.Prevalidated
import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86_64.PublicSlices
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingCT
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingPublic
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingInitialize

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
