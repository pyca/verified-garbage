module

public import VerifiedGarbage.Proof.Dsa.X86_64.Backend
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCall
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedSignCT
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningABIPost
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningVerified
public import VerifiedGarbage.Proof.Dsa.PrivateKeyWitness
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
import VerifiedGarbage.Proof.Dsa.X86_64.SigningABIPre
import VerifiedGarbage.Proof.Dsa.X86_64.SigningAgreement
import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedVerified
import VerifiedGarbage.Proof.Dsa.X86_64.Calls
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.Encoding

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
