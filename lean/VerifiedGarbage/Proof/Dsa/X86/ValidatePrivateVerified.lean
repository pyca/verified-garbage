module

public import VerifiedGarbage.Impl.Dsa.X86.PrevalidatedSign
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Dsa.X86.ValidatePrivateCT
import VerifiedGarbage.Proof.Dsa.X86.ValidatePrivate
import VerifiedGarbage.Proof.Dsa.X86.PublicDomain

/-! # i686 DSA private-key validation against its shared contract -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86

theorem privateValidatingPublic {s t : State} (H : (Spec.Dsa.validatePrivateKeyContract abi 108).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ (∀ i < 6, arg s i = arg t i) ∧
      Spec.Dsa.publicBytesLeak (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) =
      Spec.Dsa.publicBytesLeak (arg t 2).toNat (arg t 3).toNat
        (Spec.Rsa.bytesAt t.mem (argumentPointer t 0) (arg t 1).toNat) := by
  sig_pub [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argSlots, argVal,
    argBytes] at H
  obtain ⟨SP, Leak, a0, a1, a2, a3, a4, a5⟩ := H
  refine ⟨SP, fun i hi => ?_, (List.append_inj' Leak rfl).1⟩
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem privateValidatingPublicDomain {s t : State}
    (H : (Spec.Dsa.validatePrivateKeyContract abi 108).pub s t) :
    (privateValidatingKey s).params.p = (privateValidatingKey t).params.p ∧
      (privateValidatingKey s).params.q = (privateValidatingKey t).params.q := by
  obtain ⟨_, Args, Leak⟩ := privateValidatingPublic H
  rw [Args 2 (by decide), Args 3 (by decide)] at Leak
  have D := publicLeak_domain Leak
  simpa only [privateValidatingKey, Args 2 (by decide), Args 3 (by decide)] using D

theorem privateValidatingCorrect (s : State) (h : (Spec.Dsa.validatePrivateKeyContract abi 108).pre s) :
    ∃ trace t, Exec isa PrevalidatedSign.validate s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.validatePrivateKeyContract abi 108).post s t := by
  obtain ⟨trace, t, E, V, ABI, _⟩ := privateValidatingOperation_spec (privateValidatingABI_of h)
  refine ⟨trace, t, E, ABI, ?_⟩
  sig_post [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argSlots, argVal,
    argBytes]
  change ((t.gpr .edx ++ t.gpr .eax).setWidth 32).toNat = _
  rw [BitVec.setWidth_append_eq_right]
  exact V

theorem privateValidatingConstantTime : ConstantTime isa (Spec.Dsa.validatePrivateKeyContract abi 108).pre
    (Spec.Dsa.validatePrivateKeyContract abi 108).pub PrevalidatedSign.validate := by
  intro s t tr ur sf tf S T H E F
  have Args := privateValidatingPublic H
  have Domain := privateValidatingPublicDomain H
  exact privateValidatingOperation_agrees (privateValidatingABI_of S) (privateValidatingABI_of T) Args.2.1
    Args.1 Domain.1 Domain.2 E F

/-- A supported-width, disjoint call; the zero key is rejected. -/
def privateValidatingSatState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 32 else if a = 0x20008 then 168 else if a = 0x20009 then 1
    else if a = 0x2000c then 128 else if a = 0x20010 then 20 else if a = 0x20015 then 128
    else if a = 0x20019 then 8 else 0
  rd := [⟨0x2000, 424⟩]
  wr := [⟨0x8000, 16384⟩, ⟨0x20004, 24⟩]

theorem privateValidatingSatisfiable : ∃ s, (Spec.Dsa.validatePrivateKeyContract abi 108).pre s := by
  have a0 : arg privateValidatingSatState 0 = 0x2000 := by decide
  have a1 : arg privateValidatingSatState 1 = 424 := by decide
  have a2 : arg privateValidatingSatState 2 = 128 := by decide
  have a3 : arg privateValidatingSatState 3 = 20 := by decide
  have a4 : arg privateValidatingSatState 4 = 0x8000 := by decide
  have a5 : arg privateValidatingSatState 5 = 2048 := by decide
  have e : argAddr privateValidatingSatState 0 = 0x20004 := by decide
  have esp : privateValidatingSatState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig,
    abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, e, esp, privateValidatingSatState] using privateValidatingSatState

theorem privateValidating_verified :
    Verified target PrevalidatedSign.validate (Spec.Dsa.validatePrivateKeyContract abi 108) :=
  ⟨privateValidatingCorrect, privateValidatingConstantTime, privateValidatingSatisfiable⟩

end VG.Proof.Dsa.X86
