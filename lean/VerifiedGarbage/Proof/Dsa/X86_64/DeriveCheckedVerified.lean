module

public import VerifiedGarbage.Proof.Dsa.X86_64.DeriveCheckedCT
public import VerifiedGarbage.Proof.Dsa.X86_64.DeriveVerified
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Dsa.Validation
public import VerifiedGarbage.Spec.Dsa.DomainChecked
-- Proofs inside exposed definitions (structure values) use these: Lean needs them public.
public import VerifiedGarbage.Proof.Bignum.Octets -- shake: keep
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Dsa.X86_64.KeygenCalls
import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedVerified
import VerifiedGarbage.Proof.Rsa.X86_64.CallMont

/-! # x86-64 DSA key derivation for a checked domain, against its contract

`Generate.deriveChecked` is verified against `deriveKeyDomainCheckedContract`
(`Spec/Dsa/DomainChecked.lean`): `deriveKeyContract` under the precondition
that the exact domain bytes pass `checkParametersBytes`. Key generation calls
it once its domain check has returned 1. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Rsa.X86_64

theorem deriveChecked_pre {s : State} {stack : Nat}
    (h : (Spec.Dsa.deriveKeyDomainCheckedContract abi stack).pre s) :
    (Spec.Dsa.deriveKeyContract abi stack).pre s ∧
      Spec.Dsa.checkParametersBytes (s.gpr .r8).toNat (stackArg s 0).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) = true := by
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
    List.range, List.range.loop] at h
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
    List.range, List.range.loop] at h
  sig_split h
  refine ⟨?_, by assumption⟩
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range,
    List.range.loop]
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range,
    List.range.loop]
  sig_and_intros <;> with_reducible assumption

theorem deriveChecked_of_pre {s : State} {stack : Nat} (h : (Spec.Dsa.deriveKeyContract abi stack).pre s)
    (hc : Spec.Dsa.checkParametersBytes (s.gpr .r8).toNat (stackArg s 0).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) = true) :
    (Spec.Dsa.deriveKeyDomainCheckedContract abi stack).pre s := by
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range,
    List.range.loop] at h
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range,
    List.range.loop] at h
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
    List.range, List.range.loop]
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
    List.range, List.range.loop]
  sig_split h
  sig_and_intros <;> with_reducible assumption

theorem deriveCheckedCorrect (M : Mont) (Sq : MontS)
    (hmx : (Generate.deriveChecked Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : (Spec.Dsa.deriveKeyDomainCheckedContract abi).pre s) :
    ∃ trace t, Exec isa (Generate.deriveChecked Sq.mm M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.deriveKeyDomainCheckedContract abi).post s t := by
  obtain ⟨hd, hc⟩ := deriveChecked_pre h
  have ha := deriveABI_of hd
  obtain ⟨trace, t, he, hp⟩ := deriveCheckedMain_ok M Sq ha.pre hc
  exact ⟨trace, t, he, abiPreserved_of_exec hmx he (deriveGprPreserved ha hp), deriveSharedPost ha hp⟩

theorem deriveCheckedConstantTime (M : Mont) (Sq : MontS) :
    ConstantTime isa (Spec.Dsa.deriveKeyDomainCheckedContract abi).pre
      (Spec.Dsa.deriveKeyDomainCheckedContract abi).pub (Generate.deriveChecked Sq.mm M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (deriveCheckedMain_ct M Sq _ _ _ _ _ _
    (derivePublicRelated (deriveABI_of (deriveChecked_pre h₁).1) (deriveABI_of (deriveChecked_pre h₂).1) hp)
      e₁ e₂).1

/-- `validKeyWitness`'s domain, the first 276 of its bytes. -/
def validDomainWitness : List Byte := VG.Proof.Dsa.validKeyWitness.take 276

theorem validDomainWitness_length : validDomainWitness.length = 276 := by
  simp only [validDomainWitness, List.length_take, VG.Proof.Dsa.validKeyWitness_length]; rfl

theorem validDomainWitness_valid : Spec.Dsa.checkParametersBytes 128 20 validDomainWitness = true := by
  decide +kernel

/-- `deriveSatState` with `validDomainWitness` at `0x2000`. -/
def deriveCheckedSatState : State where
  gpr := deriveSatState.gpr
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x2114 then
    validDomainWitness[a.toNat - 0x2000]?.getD 0 else deriveSatState.mem a
  rd := deriveSatState.rd
  wr := deriveSatState.wr

theorem deriveCheckedSat_domain :
    Spec.Rsa.bytesAt deriveCheckedSatState.mem 0x2000 276 = validDomainWitness :=
  bytesAt_window (base := 0x2000) validDomainWitness_length (by decide) fun a h₁ h₂ => by
    simp only [deriveCheckedSatState]
    exact ite_eq_left ⟨h₁, h₂⟩

theorem deriveCheckedSat_valid : Spec.Dsa.checkParametersBytes 128 20
    (Spec.Rsa.bytesAt deriveCheckedSatState.mem 0x2000 276) = true := by
  rw [deriveCheckedSat_domain]; exact validDomainWitness_valid

theorem deriveCheckedSatisfiable : ∃ s, (Spec.Dsa.deriveKeyDomainCheckedContract abi).pre s := by
  have ho : ∃ s, (Spec.Dsa.deriveKeyContract abi).pre s ∧ s = deriveCheckedSatState := by
    sig_implies_sat [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three]
      [deriveCheckedSatState, deriveSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using deriveCheckedSatState
  obtain ⟨s, h, rfl⟩ := ho
  exact ⟨_, deriveChecked_of_pre h deriveCheckedSat_valid⟩

theorem deriveCheckedSatisfiable8 : ∃ s, (Spec.Dsa.deriveKeyDomainCheckedContract abi 8).pre s := by
  have ho : ∃ s, (Spec.Dsa.deriveKeyContract abi 8).pre s ∧ s = deriveCheckedSatState := by
    sig_implies_sat [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
      List.range, List.range.loop]
      [deriveCheckedSatState, deriveSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using deriveCheckedSatState
  obtain ⟨s, h, rfl⟩ := ho
  exact ⟨_, deriveChecked_of_pre h deriveCheckedSat_valid⟩

theorem derive_checked_verified (M : Mont) (Sq : MontS)
    (hmx : (Generate.deriveChecked Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (Generate.deriveChecked Sq.mm M.mm) (Spec.Dsa.deriveKeyDomainCheckedContract abi) :=
  ⟨deriveCheckedCorrect M Sq hmx, deriveCheckedConstantTime M Sq, deriveCheckedSatisfiable⟩

theorem deriveChecked_implies8 :
    (Spec.Dsa.deriveKeyDomainCheckedContract abi).Implies (Spec.Dsa.deriveKeyDomainCheckedContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
      List.range, List.range.loop] at h
    sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
      List.range, List.range.loop] at h
    sig_split h
    sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
      List.range, List.range.loop]
    sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
      List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs,
    stackArgs_three, List.range, List.range.loop]
  pub := by intro s t _ _ h; exact h
  sat := deriveCheckedSatisfiable8

theorem deriveChecked_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.Dsa.deriveKeyDomainCheckedContract abi).pre s) (hc : Clear (hole (s.gpr .rsp)) s)
    (hp : (Spec.Dsa.deriveKeyDomainCheckedContract abi).post s b) :
    (Spec.Dsa.deriveKeyDomainCheckedContract abi).post s (b.patch (hole (s.gpr .rsp)) hv u) :=
  derive_patch s b hv u (deriveChecked_pre hs).1 hc hp

theorem derive_checked_call_verified (M : Mont) (Sq : MontS) {c : Prog isa}
    (hc : c.InlineOk = true) (hin : c.inline = Generate.deriveChecked Sq.mm M.mm)
    (hmx : (Generate.deriveChecked Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Dsa.deriveKeyDomainCheckedContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ deriveCheckedCorrect M Sq hmx) (hin ▸ deriveCheckedConstantTime M Sq)
    deriveChecked_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h)
    deriveChecked_patch

end VG.Proof.Dsa.X86_64
