module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
public import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedSignCT
public import VerifiedGarbage.Proof.Dsa.PrivateKeyWitness
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Dsa.AArch64.PublicSlices
import VerifiedGarbage.Proof.Dsa.AArch64.SigningCT
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.AArch64.SigningPublic
import VerifiedGarbage.Proof.Dsa.AArch64.ABIRegions

/-! ### `Dsa.AArch64.SigningABIPre`, which this module and modules that import it used -/

section

/-! # The shared signing precondition supplies every machine-level resource -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem SigningABI.pre {s : State} (h : SigningABI s) : SigningPre h.input s := by
  have hs : Scr s (stackArg s 1) ((stackArg s 2).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  have hargs : (⟨stackArgAddr s 0, 24⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine ⟨scratch_prefix hs h.used (by decide), ?_, ?_, ?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ofNat_toNat64 _).symm
  · intro j hj
    exact stackWord_read (count := 3) hargs (by omega_using [hj]) (by decide)
  · intro i hi
    simpa only [Nat.mul_zero, off_zero, SigningABI.input] using Nat.le_trans h.used (stackWord_separate (count := 3) (j := 0) h.scratchArgs (by decide) (by decide) i hi)
  · exact (ofNat_toNat64 _).symm
  · change stackArg s 0 = BitVec.ofNat 64 (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat).length
    rw [bytesAt_length, ofNat_toNat64]
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x3).isLt) h.keyScratch) h.used
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x6).isLt) h.nonceScratch) h.used
  · exact source_shrink (src_of_region (p := s.gpr .x7) (by rw [h.rd]; simp) (Nat.le_of_lt (stackArg s 0).isLt) h.digestScratch) h.used
  · intro i hi
    exact ⟨_, by rw [h.wr]; simp, contains_byte _ (by change i < 2 * (s.gpr .x6).toNat at hi; rw [h.outLength]; exact hi)
      (Nat.le_of_lt (s.gpr .x1).isLt)⟩
  · intro i hi
    exact Nat.le_trans h.used (out_scr h.outScratch (contains_byte _
      (by change i < 2 * (s.gpr .x6).toNat at hi; rw [h.outLength]; exact hi) (Nat.le_of_lt (s.gpr .x1).isLt)))

def SigningABI.call {s : State} (h : SigningABI s) : SigningCall := ⟨h.input, s, h.pre⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.SigningVerified`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.SigningAgreement`, which this module and modules that import it used -/

section

/-! # Only the signing ABI's declared public observations determine its schedule -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem signingLayout_eq {p₁ p₂ : SigningInput} {s₁ s₂ : State}
    {hp₁ : s₁.gpr .x4 = BitVec.ofNat 64 p₁.pLen} {hp₂ : s₂.gpr .x4 = BitVec.ofNat 64 p₂.pLen}
    (hb : p₁.base = p₂.base) (hp : p₁.pLen = p₂.pLen) (hq : p₁.qLen = p₂.qLen)
    (hd : p₁.digestPointer = p₂.digestPointer) (hdl : p₁.digest.length = p₂.digest.length)
    (hpb : p₁.components.p = p₂.components.p) (hqb : p₁.components.q = p₂.components.q)
    (hdi : s₁.gpr .x0 = s₂.gpr .x0) (hdx : s₁.gpr .x2 = s₂.gpr .x2)
    (h8 : s₁.gpr .x4 = s₂.gpr .x4) (h9 : s₁.gpr .x5 = s₂.gpr .x5) :
    p₁.layout s₁ hp₁ = p₂.layout s₂ hp₂ := by
  have hac : p₁.accepted = p₂.accepted := by
    unfold SigningInput.accepted
    congr 1
  have hprefix : p₁.prefixLength = p₂.prefixLength := by
    unfold SigningInput.prefixLength
    rw [hdl, hqb]
  have hfields : signFieldValues s₁ (BitVec.ofNat 64 p₁.qLen) p₁.digestPointer
      (BitVec.ofNat 64 p₁.digest.length) (BitVec.ofNat 64 p₁.prefixLength) p₁.accepted =
      signFieldValues s₂ (BitVec.ofNat 64 p₂.qLen) p₂.digestPointer
      (BitVec.ofNat 64 p₂.digest.length) (BitVec.ofNat 64 p₂.prefixLength) p₂.accepted := by
    funext f
    cases f <;> simp only [signFieldValues, hq, hd, hdl, hprefix, hac, hdi, hdx, h8, h9]
  unfold SigningInput.layout
  congr 1
  · exact congrArg Spec.Dsa.decodeBE hpb
  · exact congrArg Spec.Dsa.decodeBE hqb

theorem signingAgreement {s₁ s₂ : State} (h₁ : SigningABI s₁) (h₂ : SigningABI s₂)
    (hdi : s₁.gpr .x0 = s₂.gpr .x0) (hdx : s₁.gpr .x2 = s₂.gpr .x2)
    (h8 : s₁.gpr .x4 = s₂.gpr .x4) (h9 : s₁.gpr .x5 = s₂.gpr .x5)
    (hsp : s₁.sp = s₂.sp)
    (a0 : s₁.gpr .x6 = s₂.gpr .x6) (a1 : s₁.gpr .x7 = s₂.gpr .x7)
    (a2 : stackArg s₁ 0 = stackArg s₂ 0) (a3 : stackArg s₁ 1 = stackArg s₂ 1)
    (hpub : h₁.input.key.take (3 * h₁.input.pLen + h₁.input.qLen) =
      h₂.input.key.take (3 * h₂.input.pLen + h₂.input.qLen)) : SigningAgrees h₂.call h₁.call := by
  have hp : h₁.input.pLen = h₂.input.pLen := congrArg BitVec.toNat h8
  have hq : h₁.input.qLen = h₂.input.qLen := congrArg BitVec.toNat a0
  have hdl : h₁.input.digest.length = h₂.input.digest.length := by
    change (Spec.Rsa.bytesAt _ _ _).length = (Spec.Rsa.bytesAt _ _ _).length
    rw [bytesAt_length, bytesAt_length, a2]
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
  exact ⟨signingLayout_eq a3 hp hq a1 hdl hpb hqb hdi hdx h8 h9, hpb, hqb, hdl, hsp⟩

theorem signingPublicRelated {s₁ s₂ : State} (h₁ : SigningABI s₁) (h₂ : SigningABI s₂)
    (h : (Spec.Dsa.signContract abi).pub s₁ s₂) : Two SigningStart s₁ s₂ := by
  sig_pub [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, hdi, _, hdx, _, h8, h9, a0, a1, a2, a3, _⟩ := h
  have hpub := (List.append_inj' hl (List.length_singleton.trans List.length_singleton.symm)).1
  have hb := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hpub
  exact ⟨h₂.call, ⟨h₁.call, signingAgreement h₁ h₂ hdi hdx h8 h9 hsp a0 a1 a2 a3 hb, rfl⟩,
    ⟨h₂.call, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, hsp⟩

theorem signingConstantTime (M : Mont) : ConstantTime isa (Spec.Dsa.signContract abi).pre
    (Spec.Dsa.signContract abi).pub (SignVerify.sign M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (signingMain_ct M _ _ _ _ _ _ (signingPublicRelated (signingABI_of h₁) (signingABI_of h₂) hp) e₁ e₂).1

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.SigningABIPost`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.SigningMain`, which only this module used -/

section

/-! # Functional correctness of the complete AArch64 DSA signing program -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem signingSuccess_ok (M : Mont) {p : SigningInput} {original st : State} (h : SigningPre p original)
    (hs : SigningShapePost p original h.pLength st) (ha : p.accepted = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.signingKey M.mm, Checks.privateKey M.mm,
      Core.sign M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true,
      SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result]) st
      (SigningPost p original) := by
  refine WP.seq (WP.mono (signingInitialize_ok h hs ha) fun t ht => ?_)
  have hb := signingAccepted_ok M h ht ha
  apply wpAppendSequences (a := [Checks.signingKey M.mm, Checks.privateKey M.mm,
    Core.sign M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true])
    (b := [SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result])
    (by simp) (by simp)
  exact WP.seq_iff.mp hb

theorem signingMain_ok (M : Mont) {p : SigningInput} {s0 : State} (h : SigningPre p s0) :
    WP isa (SignVerify.sign M.mm) s0 (SigningPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (signingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => signingRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change some (s.gpr .x3 == (0#64)) = some true
    simp only [hs.branch, ha, Bool.not_false]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => signingSuccess_ok M h hs ha)
    change some (s.gpr .x3 == (0#64)) = some false
    simp only [hs.branch, ha, Bool.not_true]

end VG.Proof.Dsa.AArch64

end

end

/-! # Signing correctness and ABI preservation against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem signStatus_u32 (result : Option (List Byte)) :
    ((BitVec.ofNat 64 (Spec.Dsa.signStatus result)).setWidth 32).toNat = Spec.Dsa.signStatus result := by
  cases result <;> rfl

theorem signingSharedPost {s t : State} (h : SigningABI s) (hp : SigningPost h.input s t) :
    (Spec.Dsa.signContract abi).post s t := by
  obtain ⟨hr, hout, _, _⟩ := hp
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
  rw [hr, signStatus_u32]
  refine ⟨rfl, ?_⟩
  rw [h.outLength]
  exact hout

theorem signingCorrect (M : Mont)
    (s : State) (h : (Spec.Dsa.signContract abi).pre s) :
    ∃ trace t, Exec isa (SignVerify.sign M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.signContract abi).post s t := by
  have ha := signingABI_of h
  obtain ⟨trace, t, he, hp⟩ := signingMain_ok M ha.pre
  exact ⟨trace, t, he, abiPreserved_of_keep hp.2.2.2, signingSharedPost ha hp⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # DSA signing verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum.AArch64

/-- An ordinary 1024/160 call with disjoint buffers and an empty digest.
The all-zero key is allowed by the contract and is rejected by the program. -/
def signingSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 40 | .x2 => 0x2000 | .x3 => 424
    | .x4 => 128 | .x5 => 0x4000 | .x6 => 20 | .x7 => 0x5000 | _ => 0
  sp := 0x10000
  mem a := if a = 0x10009 then 0x80 else if a = 0x10011 then 8 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x4000, 20⟩, ⟨0x5000, 0⟩, ⟨0x10000, 24⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x8000, 16384⟩]

theorem signingSatisfiable : ∃ s, (Spec.Dsa.signContract abi).pre s := by
  sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
    [signingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signingSatState

theorem signing_verified (M : Mont) :
    Verified target (SignVerify.sign M.mm) (Spec.Dsa.signContract abi) :=
  ⟨signingCorrect M, signingConstantTime M, signingSatisfiable⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # An AArch64 DSA signing attempt for a validated private key against its contract

`prevalidated_sign_verified` is the program's proof against
`signContractWith validatePrivateKeyBytes`. The randomized wrapper
(`vg_dsa_sign_random_prevalidated`) calls it. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64 VG.Proof.Bignum.AArch64

theorem prevalidatedSigningCorrect (M : Mont)
    (s : State) (h : (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).pre s) :
    ∃ trace t, Exec isa (PrevalidatedSign.sign M.mm) s trace t ∧ abiPreserved s t ∧
      (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).post s t := by
  obtain ⟨hs, hv⟩ := signWith_pre h
  have ha := signingABI_of hs
  obtain ⟨trace, t, he, hp⟩ := prevalidatedSignMain_ok M ha.pre hv
  exact ⟨trace, t, he, abiPreserved_of_keep hp.2.2.2, signWith_post (signingSharedPost ha hp)⟩

theorem prevalidatedSigningConstantTime (M : Mont) :
    ConstantTime isa (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).pre
      (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).pub (PrevalidatedSign.sign M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (prevalidatedSignMain_ct M _ _ _ _ _ _
    (signingPublicRelated (signingABI_of (signWith_pre h₁).1) (signingABI_of (signWith_pre h₂).1)
      (signWith_pub hp)) e₁ e₂).1

/-- `signingSatState` with `validPrivateKeyWitness` at `0x2000`. -/
def prevalidatedSignSatState : State where
  gpr := signingSatState.gpr
  sp := signingSatState.sp
  rd := signingSatState.rd
  wr := signingSatState.wr
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x21a8 then
    VG.Proof.Dsa.validPrivateKeyWitness[a.toNat - 0x2000]?.getD 0 else signingSatState.mem a

theorem prevalidatedSignSatisfiable :
    ∃ s, (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).pre s := by
  have hb : Spec.Rsa.bytesAt prevalidatedSignSatState.mem 0x2000 424 = VG.Proof.Dsa.validPrivateKeyWitness :=
    VG.Proof.Dsa.bytesAt_of_list (lo := 0x2000) (by decide +kernel) (by decide) fun a h1 h2 => by
      have h : 0x2000 ≤ a.toNat ∧ a.toNat < 0x21a8 := ⟨h1, h2⟩
      simp only [prevalidatedSignSatState, h, and_self, ↓reduceIte]
  have ho : ∃ s, (Spec.Dsa.signContract abi).pre s ∧ s = prevalidatedSignSatState := by
    sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
      [prevalidatedSignSatState, signingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using prevalidatedSignSatState
  obtain ⟨s, h, rfl⟩ := ho
  refine ⟨_, signWith_of_pre h ?_⟩
  change Spec.Dsa.validatePrivateKeyBytes 128 20 (Spec.Rsa.bytesAt prevalidatedSignSatState.mem 0x2000 424) = true
  rw [hb]
  exact VG.Proof.Dsa.validPrivateKeyWitness_valid

theorem prevalidated_sign_verified (M : Mont) :
    Verified target (PrevalidatedSign.sign M.mm) (signContractWith Spec.Dsa.validatePrivateKeyBytes abi) :=
  ⟨prevalidatedSigningCorrect M, prevalidatedSigningConstantTime M, prevalidatedSignSatisfiable⟩

end VG.Proof.Dsa.AArch64
