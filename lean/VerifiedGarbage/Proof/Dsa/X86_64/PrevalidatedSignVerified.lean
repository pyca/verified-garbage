module

public import VerifiedGarbage.Proof.Dsa.X86_64.Backend
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCall
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedSignCT
public import VerifiedGarbage.Proof.Dsa.PrivateKeyWitness
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningABIPre
import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedVerified
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningABI
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningReturn
import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86_64.PublicSlices
import VerifiedGarbage.Proof.Dsa.X86_64.SigningCT

/-! ### `Dsa.X86_64.Calls`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.SigningVerified`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.SigningAgreement`, which this module and modules that import it used -/

section

/-! # Only the signing ABI's declared public observations determine its schedule -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem signingLayout_eq {p₁ p₂ : SigningInput} {s₁ s₂ : State}
    {hp₁ : s₁.gpr .r8 = BitVec.ofNat 64 p₁.pLen} {hp₂ : s₂.gpr .r8 = BitVec.ofNat 64 p₂.pLen}
    (hb : p₁.base = p₂.base) (hp : p₁.pLen = p₂.pLen) (hq : p₁.qLen = p₂.qLen)
    (hd : p₁.digestPointer = p₂.digestPointer) (hdl : p₁.digest.length = p₂.digest.length)
    (hpb : p₁.components.p = p₂.components.p) (hqb : p₁.components.q = p₂.components.q)
    (hdi : s₁.gpr .rdi = s₂.gpr .rdi) (hdx : s₁.gpr .rdx = s₂.gpr .rdx)
    (h8 : s₁.gpr .r8 = s₂.gpr .r8) (h9 : s₁.gpr .r9 = s₂.gpr .r9) :
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
    (hdi : s₁.gpr .rdi = s₂.gpr .rdi) (hdx : s₁.gpr .rdx = s₂.gpr .rdx)
    (h8 : s₁.gpr .r8 = s₂.gpr .r8) (h9 : s₁.gpr .r9 = s₂.gpr .r9)
    (hsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (a0 : stackArg s₁ 0 = stackArg s₂ 0) (a1 : stackArg s₁ 1 = stackArg s₂ 1)
    (a2 : stackArg s₁ 2 = stackArg s₂ 2) (a3 : stackArg s₁ 3 = stackArg s₂ 3)
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
  sig_pub [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, hdi, _, hdx, _, h8, h9, a0, a1, a2, a3, _⟩ := h
  have hpub := (List.append_inj' hl (List.length_singleton.trans List.length_singleton.symm)).1
  have hb := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hpub
  exact ⟨h₂.call, ⟨h₁.call, signingAgreement h₁ h₂ hdi hdx h8 h9 hsp a0 a1 a2 a3 hb, rfl⟩,
    ⟨h₂.call, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩⟩

theorem signingConstantTime (M : Mont) (Sq : MontS) : ConstantTime isa (Spec.Dsa.signContract abi).pre
    (Spec.Dsa.signContract abi).pub (SignVerify.sign Sq.mm M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (signingMain_ct M Sq _ _ _ _ _ _ (signingPublicRelated (signingABI_of h₁) (signingABI_of h₂) hp) e₁ e₂).1

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.SigningABIPost`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.SigningMain`, which only this module used -/

section

/-! # Functional correctness of the complete x86-64 DSA signing program -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem signingSuccess_ok (M : Mont) (Sq : MontS) {p : SigningInput} {original st : State} (h : SigningPre p original)
    (hs : SigningShapePost p original h.pLength st) (ha : p.accepted = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.signingKey Sq.mm M.mm, Checks.privateKey Sq.mm M.mm,
      Core.sign Sq.mm M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true,
      SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result]) st
      (SigningPost p original) := by
  refine WP.seq (WP.mono (signingInitialize_ok h hs ha) fun t ht => ?_)
  have hb := signingAccepted_ok M Sq h ht ha
  apply wpAppendSequences (a := [Checks.signingKey Sq.mm M.mm, Checks.privateKey Sq.mm M.mm,
    Core.sign Sq.mm M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true])
    (b := [SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result])
    (by simp) (by simp)
  exact WP.seq_iff.mp hb

theorem signingMain_ok (M : Mont) (Sq : MontS) {p : SigningInput} {s0 : State} (h : SigningPre p s0) :
    WP isa (SignVerify.sign Sq.mm M.mm) s0 (SigningPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (signingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => signingRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change eval .e s = some true
    simp only [eval, hs.branch, ha, Bool.not_false]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => signingSuccess_ok M Sq h hs ha)
    change eval .e s = some false
    simp only [eval, hs.branch, ha, Bool.not_true]

end VG.Proof.Dsa.X86_64

end

end

/-! # Signing correctness and ABI preservation against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem signingGprPreserved {s t : State} (h : SigningABI s) (hp : SigningPost h.input s t) :
    gprPreserved s t := by
  obtain ⟨_, _, hsaved, hf, hk⟩ := hp
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
  · have hret := contains_byte (s.gpr .rsp) (i := i) (len := 8) hi (by decide)
    apply hf _ (Nat.le_trans h.used (out_scr h.retScratch hret))
    intro j hj he
    apply h.retOut _ hret
    rw [he]
    exact contains_byte _ (by change j < 2 * (stackArg s 0).toNat at hj; rw [h.outLength]; exact hj)
      (Nat.le_of_lt (s.gpr .rsi).isLt)

theorem signStatus_u32 (result : Option (List Byte)) :
    ((BitVec.ofNat 64 (Spec.Dsa.signStatus result)).setWidth 32).toNat = Spec.Dsa.signStatus result := by
  cases result <;> rfl

theorem signingSharedPost {s t : State} (h : SigningABI s) (hp : SigningPost h.input s t) :
    (Spec.Dsa.signContract abi).post s t := by
  obtain ⟨hr, hout, _, _, _⟩ := hp
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five]
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five]
  rw [hr, signStatus_u32]
  refine ⟨rfl, ?_⟩
  rw [h.outLength]
  exact hout

theorem signingCorrect (M : Mont) (Sq : MontS)
    (hmx : (SignVerify.sign Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : (Spec.Dsa.signContract abi).pre s) :
    ∃ trace t, Exec isa (SignVerify.sign Sq.mm M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.signContract abi).post s t := by
  have ha := signingABI_of h
  obtain ⟨trace, t, he, hp⟩ := signingMain_ok M Sq ha.pre
  exact ⟨trace, t, he, abiPreserved_of_exec hmx he (signingGprPreserved ha hp), signingSharedPost ha hp⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # DSA signing verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum.X86_64

/-- An ordinary 1024/160 call with disjoint buffers and an empty digest.
The all-zero key is allowed by the contract and is rejected by the program. -/
def signingSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 40 | .rdx => 0x2000 | .rcx => 424
    | .r8 => 128 | .r9 => 0x4000 | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10008 then 20 else if a = 0x10011 then 0x50
    else if a = 0x10021 then 0x80 else if a = 0x10029 then 8 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x4000, 20⟩, ⟨0x5000, 0⟩, ⟨0x10008, 40⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x8000, 16384⟩]

theorem signingSatisfiable : ∃ s, (Spec.Dsa.signContract abi).pre s := by
  sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five]
    [signingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signingSatState

theorem signing_verified (M : Mont) (Sq : MontS)
    (hmx : (SignVerify.sign Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (SignVerify.sign Sq.mm M.mm) (Spec.Dsa.signContract abi) :=
  ⟨signingCorrect M Sq hmx, signingConstantTime M Sq, signingSatisfiable⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # DSA using RSA's callable Montgomery kernels

The shared contracts already parameterize stack use. Calls need eight bytes
for the return address; the arithmetic and leakage proofs apply to their
inlined bodies. Output buffers remain disjoint from that stack slot.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem signing_implies8 : (Spec.Dsa.signContract abi).Implies (Spec.Dsa.signContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop] at h
    sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop] at h
    sig_split h
    sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
    sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
  pub := by intro s t _ _ h; exact h
  sat := by
    sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
      [signingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signingSatState

theorem signing_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.Dsa.signContract abi).pre s) (hc : Clear (hole (s.gpr .rsp)) s)
    (hp : (Spec.Dsa.signContract abi).post s b) :
    (Spec.Dsa.signContract abi).post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have ha := signingABI_of hs
  have hm := Clear.miss_wr hc (by rw [ha.wr]; exact List.mem_cons_self)
    ha.outBound (Nat.le_refl _)
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop] at hp ⊢
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop] at hp ⊢
  simpa only [State.patch_gpr, patch_mem, bytesAt_overlay hm] using hp

theorem signing_call_verified (M : Mont) (Sq : MontS) {c : Prog isa}
    (hc : c.InlineOk = true) (hin : c.inline = SignVerify.sign Sq.mm M.mm)
    (hmx : (SignVerify.sign Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Dsa.signContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ signingCorrect M Sq hmx) (hin ▸ signingConstantTime M Sq)
    signing_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h)
    signing_patch

end VG.Proof.Dsa.X86_64

end

end

/-! # An x86-64 DSA signing attempt for a validated private key against its contract

`prevalidated_sign_verified` is the program's proof against
`signContractWith validatePrivateKeyBytes`, and
`prevalidated_sign_call_verified` that of the code that calls the
Montgomery kernels, whose return addresses take eight bytes of stack. The
randomized wrapper (`vg_dsa_sign_random_prevalidated`) calls it. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Rsa.X86_64

theorem prevalidatedSigningCorrect (M : Mont) (Sq : MontS)
    (hmx : (PrevalidatedSign.sign Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).pre s) :
    ∃ trace t, Exec isa (PrevalidatedSign.sign Sq.mm M.mm) s trace t ∧ abiPreserved s t ∧
      (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).post s t := by
  obtain ⟨hs, hv⟩ := signWith_pre h
  have ha := signingABI_of hs
  obtain ⟨trace, t, he, hp⟩ := prevalidatedSignMain_ok M Sq ha.pre hv
  exact ⟨trace, t, he, abiPreserved_of_exec hmx he (signingGprPreserved ha hp),
    signWith_post (signingSharedPost ha hp)⟩

theorem prevalidatedSigningConstantTime (M : Mont) (Sq : MontS) :
    ConstantTime isa (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).pre
      (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).pub (PrevalidatedSign.sign Sq.mm M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (prevalidatedSignMain_ct M Sq _ _ _ _ _ _
    (signingPublicRelated (signingABI_of (signWith_pre h₁).1) (signingABI_of (signWith_pre h₂).1)
      (signWith_pub hp)) e₁ e₂).1

/-- `signingSatState` with `validPrivateKeyWitness` at `0x2000`. -/
def prevalidatedSignSatState : State where
  gpr := signingSatState.gpr
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x21a8 then
    validPrivateKeyWitness[a.toNat - 0x2000]?.getD 0 else signingSatState.mem a
  rd := signingSatState.rd
  wr := signingSatState.wr

theorem prevalidatedSignSat_key :
    Spec.Rsa.bytesAt prevalidatedSignSatState.mem 0x2000 424 = validPrivateKeyWitness :=
  bytesAt_window (base := 0x2000) validPrivateKeyWitness_length (by decide) fun a h₁ h₂ => by
    simp only [prevalidatedSignSatState]
    exact ite_eq_left ⟨h₁, h₂⟩

theorem prevalidatedSignSat_valid : Spec.Dsa.validatePrivateKeyBytes 128 20
    (Spec.Rsa.bytesAt prevalidatedSignSatState.mem 0x2000 424) = true := by
  rw [prevalidatedSignSat_key]; exact validPrivateKeyWitness_valid

theorem prevalidatedSignSatisfiable :
    ∃ s, (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).pre s := by
  have ho : ∃ s, (Spec.Dsa.signContract abi).pre s ∧ s = prevalidatedSignSatState := by
    sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five]
      [prevalidatedSignSatState, signingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using prevalidatedSignSatState
  obtain ⟨s, h, rfl⟩ := ho
  exact ⟨_, signWith_of_pre h prevalidatedSignSat_valid⟩

theorem prevalidatedSignSatisfiable8 :
    ∃ s, (signContractWith Spec.Dsa.validatePrivateKeyBytes abi 8).pre s := by
  have ho : ∃ s, (Spec.Dsa.signContract abi 8).pre s ∧ s = prevalidatedSignSatState := by
    sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range,
      List.range.loop]
      [prevalidatedSignSatState, signingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using prevalidatedSignSatState
  obtain ⟨s, h, rfl⟩ := ho
  exact ⟨_, signWith_of_pre h prevalidatedSignSat_valid⟩

theorem prevalidated_sign_verified (M : Mont) (Sq : MontS)
    (hmx : (PrevalidatedSign.sign Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (PrevalidatedSign.sign Sq.mm M.mm) (signContractWith Spec.Dsa.validatePrivateKeyBytes abi) :=
  ⟨prevalidatedSigningCorrect M Sq hmx, prevalidatedSigningConstantTime M Sq,
    prevalidatedSignSatisfiable⟩

theorem prevalidatedSign_implies8 : (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).Implies
    (signContractWith Spec.Dsa.validatePrivateKeyBytes abi 8) where
  pre := by
    intro s h
    sig_pre [signContractWith, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop] at h
    sig_pre [signContractWith, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop] at h
    sig_split h
    sig_pre [signContractWith, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
    sig_pre [signContractWith, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [signContractWith, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range,
    List.range.loop]
  pub := by intro s t _ _ h; exact h
  sat := prevalidatedSignSatisfiable8

theorem prevalidatedSign_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).pre s) (hc : Clear (hole (s.gpr .rsp)) s)
    (hp : (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).post s b) :
    (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).post s (b.patch (hole (s.gpr .rsp)) hv u) :=
  signWith_post (signing_patch s b hv u (signWith_pre hs).1 hc (signWith_post' hp))

theorem prevalidated_sign_call_verified (M : Mont) (Sq : MontS) {c : Prog isa}
    (hc : c.InlineOk = true) (hin : c.inline = PrevalidatedSign.sign Sq.mm M.mm)
    (hmx : (PrevalidatedSign.sign Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (signContractWith Spec.Dsa.validatePrivateKeyBytes abi 8) :=
  Verified.of_inline_sig hc (hin ▸ prevalidatedSigningCorrect M Sq hmx) (hin ▸ prevalidatedSigningConstantTime M Sq)
    prevalidatedSign_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h)
    prevalidatedSign_patch

end VG.Proof.Dsa.X86_64
