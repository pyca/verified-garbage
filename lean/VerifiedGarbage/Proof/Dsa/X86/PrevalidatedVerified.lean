module

public import VerifiedGarbage.Impl.Dsa.X86.Prevalidated
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Dsa.Validation
public import VerifiedGarbage.Proof.Dsa.X86.Verified
public import VerifiedGarbage.Proof.Dsa.X86.PrevalidatedCT
import VerifiedGarbage.Proof.Dsa.X86.Validating
import VerifiedGarbage.Proof.Dsa.X86.Prevalidated
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
import VerifiedGarbage.Proof.Dsa.X86.SharedPublic
import VerifiedGarbage.Proof.Dsa.X86.PublicDomain

/-! # i686 DSA public-key validation and prevalidated verification against the shared contracts -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86

theorem validatingPublicArgs {s t : State} (H : (Spec.Dsa.validatePublicKeyContract abi 108).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 6, arg s i = arg t i := by
  sig_pub [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem validatingPublicDomain {s t : State} (H : (Spec.Dsa.validatePublicKeyContract abi 108).pub s t) :
    (validatingKey s).params.p = (validatingKey t).params.p ∧
      (validatingKey s).params.q = (validatingKey t).params.q := by
  have Args := (validatingPublicArgs H).2
  have Leak : Spec.Dsa.publicBytesLeak (arg s 2).toNat (arg s 3).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) =
      Spec.Dsa.publicBytesLeak (arg t 2).toNat (arg t 3).toNat
        (Spec.Rsa.bytesAt t.mem (argumentPointer t 0) (arg t 1).toNat) := by
    sig_pub [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argSlots, argVal,
      argBytes] at H
    exact H.2.1
  rw [Args 2 (by decide), Args 3 (by decide)] at Leak
  have D := publicLeak_domain Leak
  simpa only [validatingKey, Args 2 (by decide), Args 3 (by decide)] using D

theorem validatingCorrect (s : State) (h : (Spec.Dsa.validatePublicKeyContract abi 108).pre s) :
    ∃ trace t, Exec isa Prevalidated.validate s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.validatePublicKeyContract abi 108).post s t := by
  obtain ⟨trace, t, E, V, ABI, _⟩ := validatingOperation_spec (validatingABI_of h)
  refine ⟨trace, t, E, ABI, ?_⟩
  sig_post [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argSlots, argVal, argBytes]
  change ((t.gpr .edx ++ t.gpr .eax).setWidth 32).toNat = _
  rw [BitVec.setWidth_append_eq_right]
  exact V

theorem validatingConstantTime : ConstantTime isa (Spec.Dsa.validatePublicKeyContract abi 108).pre
    (Spec.Dsa.validatePublicKeyContract abi 108).pub Prevalidated.validate := by
  intro s t tr ur sf tf S T H E F
  have Args := validatingPublicArgs H
  have Domain := validatingPublicDomain H
  exact validatingOperation_agrees (validatingABI_of S) (validatingABI_of T) Args.2 Args.1 Domain.1 Domain.2 E F

/-- A supported-width, disjoint call; the zero key is rejected. -/
def validatingSatState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 32 else if a = 0x20008 then 148 else if a = 0x20009 then 1
    else if a = 0x2000c then 128 else if a = 0x20010 then 20 else if a = 0x20015 then 128
    else if a = 0x20019 then 8 else 0
  rd := [⟨0x2000, 404⟩]
  wr := [⟨0x8000, 16384⟩, ⟨0x20004, 24⟩]

theorem validatingSatisfiable : ∃ s, (Spec.Dsa.validatePublicKeyContract abi 108).pre s := by
  have a0 : arg validatingSatState 0 = 0x2000 := by decide
  have a1 : arg validatingSatState 1 = 404 := by decide
  have a2 : arg validatingSatState 2 = 128 := by decide
  have a3 : arg validatingSatState 3 = 20 := by decide
  have a4 : arg validatingSatState 4 = 0x8000 := by decide
  have a5 : arg validatingSatState 5 = 2048 := by decide
  have e : argAddr validatingSatState 0 = 0x20004 := by decide
  have esp : validatingSatState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig,
    abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, e, esp, validatingSatState] using validatingSatState

theorem validating_verified :
    Verified target Prevalidated.validate (Spec.Dsa.validatePublicKeyContract abi 108) :=
  ⟨validatingCorrect, validatingConstantTime, validatingSatisfiable⟩

theorem prevalidatedABI_of {s : State} (h : (Spec.Dsa.verifyPrevalidatedContract abi 108).pre s) :
    VerifyingABI s ∧ Spec.Dsa.validatePublicKeyBytes (arg s 2).toNat (arg s 3).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) = true := by
  sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  sig_split h
  exact ⟨by constructor <;> with_reducible assumption, by assumption⟩

theorem prevalidatedPre_of {s : State} (h : (Spec.Dsa.verifyContract abi 108).pre s)
    (hv : Spec.Dsa.validatePublicKeyBytes (arg s 2).toNat (arg s 3).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) = true) :
    (Spec.Dsa.verifyPrevalidatedContract abi 108).pre s := by
  sig_pre [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argSlots, argVal, argBytes, stackBelow]
  sig_split h
  sig_and_intros <;> with_reducible assumption

theorem prevalidatedCorrect (s : State) (h : (Spec.Dsa.verifyPrevalidatedContract abi 108).pre s) :
    ∃ trace t, Exec isa Prevalidated.verify s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.verifyPrevalidatedContract abi 108).post s t := by
  obtain ⟨A, valid⟩ := prevalidatedABI_of h
  obtain ⟨trace, t, E, V, ABI, _⟩ := prevalidatedOperation_spec A valid
  refine ⟨trace, t, E, ABI, ?_⟩
  sig_post [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argSlots, argVal, argBytes]
  change ((t.gpr .edx ++ t.gpr .eax).setWidth 32).toNat = _
  rw [BitVec.setWidth_append_eq_right]
  exact V

theorem prevalidatedConstantTime : ConstantTime isa (Spec.Dsa.verifyPrevalidatedContract abi 108).pre
    (Spec.Dsa.verifyPrevalidatedContract abi 108).pub Prevalidated.verify := by
  intro s t tr ur sf tf S T H E F
  change (Spec.Dsa.verifyContract abi 108).pub s t at H
  have Args := verifyingPublicArgs H
  have Domain := verifyingPublicDomain H
  exact prevalidatedOperation_agrees (prevalidatedABI_of S).1 (prevalidatedABI_of T).1 Args.2 Args.1
    Domain.1 Domain.2 E F

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

theorem prevalidatedSatisfiable : ∃ s, (Spec.Dsa.verifyPrevalidatedContract abi 108).pre s := by
  have a0 : arg prevalidatedSatState 0 = 8192 := by decide
  have a1 : arg prevalidatedSatState 1 = 404 := by decide
  have a2 : arg prevalidatedSatState 2 = 128 := by decide
  have a3 : arg prevalidatedSatState 3 = 20 := by decide
  have a4 : arg prevalidatedSatState 4 = 16384 := by decide
  have a5 : arg prevalidatedSatState 5 = 40 := by decide
  have a6 : arg prevalidatedSatState 6 = 20480 := by decide
  have a7 : arg prevalidatedSatState 7 = 0 := by decide
  have a8 : arg prevalidatedSatState 8 = 32768 := by decide
  have a9 : arg prevalidatedSatState 9 = 2048 := by decide
  have e : argAddr prevalidatedSatState 0 = 0x20004 := by decide
  have esp : prevalidatedSatState.gpr .esp = 0x20000 := rfl
  have ho : ∃ s, (Spec.Dsa.verifyContract abi 108).pre s ∧ s = prevalidatedSatState := by
    sig_implies_sat [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argSlots, argVal, argBytes, stackBelow]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, e, esp, prevalidatedSatState, verifyingSatState]
      using prevalidatedSatState
  obtain ⟨s, h, rfl⟩ := ho
  have key : Spec.Rsa.bytesAt prevalidatedSatState.mem (argumentPointer prevalidatedSatState 0)
      (arg prevalidatedSatState 1).toNat = VG.Proof.Dsa.validKeyWitness := by
    have p0 : argumentPointer prevalidatedSatState 0 = BitVec.ofNat 64 0x2000 := by
      unfold argumentPointer; rw [a0]; rfl
    rw [p0, a1]
    exact bytesAt_window (base := 0x2000) VG.Proof.Dsa.validKeyWitness_length (by decide) fun a h₁ h₂ => by
      simp only [prevalidatedSatState]
      exact ite_eq_left ⟨h₁, h₂⟩
  refine ⟨_, prevalidatedPre_of h ?_⟩
  rw [key, a2, a3]
  exact VG.Proof.Dsa.validKeyWitness_valid

theorem prevalidated_verified :
    Verified target Prevalidated.verify (Spec.Dsa.verifyPrevalidatedContract abi 108) :=
  ⟨prevalidatedCorrect, prevalidatedConstantTime, prevalidatedSatisfiable⟩

end VG.Proof.Dsa.X86
