module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
public import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedSignCT
public import VerifiedGarbage.Proof.Dsa.AArch64.SigningVerified
public import VerifiedGarbage.Proof.Dsa.PrivateKeyWitness
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Dsa.AArch64.SigningABIPre
import VerifiedGarbage.Proof.Dsa.AArch64.SigningABIPost
import VerifiedGarbage.Proof.Dsa.AArch64.SigningAgreement
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode

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
  have hb : Spec.Rsa.bytesAt prevalidatedSignSatState.mem 0x2000 424 = VG.Proof.Dsa.validPrivateKeyWitness := by
    decide +kernel
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
