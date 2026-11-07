module

public import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCheckedCT
public import VerifiedGarbage.Proof.Dsa.AArch64.DeriveVerified
public import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedSat
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Dsa.DomainChecked
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode

/-! # AArch64 DSA key derivation for a checked domain, against its contract

`Generate.deriveChecked` is verified against `deriveKeyDomainCheckedContract`
(`Spec/Dsa/DomainChecked.lean`): `deriveKeyContract` under the precondition
that the exact domain bytes pass `checkParametersBytes`. Key generation calls
it once its domain check has returned 1. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem deriveChecked_pre {s : State} {stack : Nat}
    (h : (Spec.Dsa.deriveKeyDomainCheckedContract abi stack).pre s) :
    (Spec.Dsa.deriveKeyContract abi stack).pre s ∧
      Spec.Dsa.checkParametersBytes (s.gpr .x4).toNat (s.gpr .x6).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) = true := by
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs] at h
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs] at h
  sig_split h
  refine ⟨?_, by assumption⟩
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  sig_and_intros <;> with_reducible assumption

theorem deriveChecked_of_pre {s : State} {stack : Nat} (h : (Spec.Dsa.deriveKeyContract abi stack).pre s)
    (hc : Spec.Dsa.checkParametersBytes (s.gpr .x4).toNat (s.gpr .x6).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) = true) :
    (Spec.Dsa.deriveKeyDomainCheckedContract abi stack).pre s := by
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs] at h
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs] at h
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  sig_split h
  sig_and_intros <;> with_reducible assumption

theorem deriveCheckedCorrect (M : Mont)
    (s : State) (h : (Spec.Dsa.deriveKeyDomainCheckedContract abi).pre s) :
    ∃ trace t, Exec isa (Generate.deriveChecked M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.deriveKeyDomainCheckedContract abi).post s t := by
  obtain ⟨hd, hc⟩ := deriveChecked_pre h
  have ha := deriveABI_of hd
  obtain ⟨trace, t, he, hp⟩ := deriveCheckedMain_ok M ha.pre hc
  refine ⟨trace, t, he, derivePreserved ha hp, ?_⟩
  have hs := deriveSharedPost ha hp
  sig_post [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs] at hs
  sig_post [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  exact hs

theorem deriveCheckedConstantTime (M : Mont) :
    ConstantTime isa (Spec.Dsa.deriveKeyDomainCheckedContract abi).pre
      (Spec.Dsa.deriveKeyDomainCheckedContract abi).pub (Generate.deriveChecked M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (deriveCheckedMain_ct M _ _ _ _ _ _
    (derivePublicRelated (deriveABI_of (deriveChecked_pre h₁).1) (deriveABI_of (deriveChecked_pre h₂).1) hp)
      e₁ e₂).1

/-- `validatedSatKey`'s domain p‖q‖g, its first 276 bytes. -/
def validDomainWitness : List Byte := validatedSatKey.take 276

/-- `deriveSatState` with `validDomainWitness` at `0x2000`. -/
def deriveCheckedSatState : State where
  gpr := deriveSatState.gpr
  sp := deriveSatState.sp
  rd := deriveSatState.rd
  wr := deriveSatState.wr
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x2114 then
    validDomainWitness[a.toNat - 0x2000]?.getD 0 else deriveSatState.mem a

theorem deriveCheckedSat_valid : Spec.Dsa.checkParametersBytes 128 20
    (Spec.Rsa.bytesAt deriveCheckedSatState.mem 0x2000 276) = true := by
  decide +kernel

theorem deriveCheckedSatisfiable : ∃ s, (Spec.Dsa.deriveKeyDomainCheckedContract abi).pre s := by
  have ho : ∃ s, (Spec.Dsa.deriveKeyContract abi).pre s ∧ s = deriveCheckedSatState := by
    sig_implies_sat [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
      [deriveCheckedSatState, deriveSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using deriveCheckedSatState
  obtain ⟨s, h, rfl⟩ := ho
  exact ⟨_, deriveChecked_of_pre h deriveCheckedSat_valid⟩

theorem derive_checked_verified (M : Mont) :
    Verified target (Generate.deriveChecked M.mm) (Spec.Dsa.deriveKeyDomainCheckedContract abi) :=
  ⟨deriveCheckedCorrect M, deriveCheckedConstantTime M, deriveCheckedSatisfiable⟩

end VG.Proof.Dsa.AArch64
