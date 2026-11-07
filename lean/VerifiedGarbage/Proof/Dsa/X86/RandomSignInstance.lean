module

public import VerifiedGarbage.Proof.Dsa.X86.Verified
public import VerifiedGarbage.Impl.Dsa.X86.RandomSign
public import VerifiedGarbage.Proof.Dsa.X86.RandomCall
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.PrivateKeyWitness
import VerifiedGarbage.Proof.Dsa.X86.PrevalidatedVerified

import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Dsa.X86.RandomSignCT
import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
public import VerifiedGarbage.Impl.Dsa.X86.PrevalidatedSign
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.SignContractWith
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Dsa.X86.PrevalidatedSignCT
import VerifiedGarbage.Proof.Dsa.X86.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.X86.SharedPublic
import VerifiedGarbage.Proof.Dsa.X86.PublicDomain

/-! # The randomized signer, calling the fully checked `vg_dsa_sign` or `vg_dsa_sign_prevalidated` (x86) -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/RandomSignVerified.lean`, which only this module imported.
section

/-! # The x86 randomized signer meets its contract -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86.RandomSign

/-- A disjoint 1024/160 call with an empty tape. -/
def randomSignSatState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 0x10 else if a = 0x20008 then 40 else if a = 0x2000d then 0x70
    else if a = 0x20011 then 0x20 else if a = 0x20014 then 0xa8 else if a = 0x20015 then 1
    else if a = 0x20018 then 128 else if a = 0x2001c then 20 else if a = 0x20021 then 0x50
    else if a = 0x20029 then 0x60 else if a = 0x20031 then 0x80 else if a = 0x20034 then 0x40
    else if a = 0x20035 then 8 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x5000, 0⟩, ⟨0x6000, 0⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x7000, 8⟩, ⟨0x8000, 16896⟩, ⟨0x20004, 52⟩]

theorem randomSign_satisfiable : ∃ s, (Spec.Dsa.randomSignContract abi 232).pre s := by
  have a0 : arg randomSignSatState 0 = 0x1000 := by decide
  have a1 : arg randomSignSatState 1 = 40 := by decide
  have a2 : arg randomSignSatState 2 = 0x7000 := by decide
  have a3 : arg randomSignSatState 3 = 0x2000 := by decide
  have a4 : arg randomSignSatState 4 = 424 := by decide
  have a5 : arg randomSignSatState 5 = 128 := by decide
  have a6 : arg randomSignSatState 6 = 20 := by decide
  have a7 : arg randomSignSatState 7 = 0x5000 := by decide
  have a8 : arg randomSignSatState 8 = 0 := by decide
  have a9 : arg randomSignSatState 9 = 0x6000 := by decide
  have a10 : arg randomSignSatState 10 = 0 := by decide
  have a11 : arg randomSignSatState 11 = 0x8000 := by decide
  have a12 : arg randomSignSatState 12 = 2112 := by decide
  have e : argAddr randomSignSatState 0 = 0x20004 := by decide
  have esp : randomSignSatState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argSlots, argVal, argBytes,
    stackBelow] [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e, esp, randomSignSatState]
    using randomSignSatState

/-- A signer that accepts every key, in the randomized wrapper. -/
theorem randomSign_verified (F : SignFn) (hall : ∀ s, KeyValid F.valid s) :
    Verified target (code F.name F.code) (Spec.Dsa.randomSignContract abi 232) :=
  ⟨fun s h => randomSign_correct F s h (hall s),
    fun s t tr ur sf tf hs ht => randomSign_constantTime F s t tr ur sf tf ⟨hs, hall s⟩ ⟨ht, hall t⟩,
    randomSign_satisfiable⟩

theorem randomPrevalidated_pre {s : State} (h : (Spec.Dsa.randomSignPrevalidatedContract abi 232).pre s) :
    (Spec.Dsa.randomSignContract abi 232).pre s ∧ KeyValid Spec.Dsa.validatePrivateKeyBytes s := by
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  sig_split h
  refine ⟨?_, by unfold KeyValid rInput; assumption⟩
  sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros <;> with_reducible assumption

theorem randomPrevalidated_of_pre {s : State} (h : (Spec.Dsa.randomSignContract abi 232).pre s)
    (hv : KeyValid Spec.Dsa.validatePrivateKeyBytes s) :
    (Spec.Dsa.randomSignPrevalidatedContract abi 232).pre s := by
  unfold KeyValid rInput at hv
  sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, abi, argSlots, argVal, argBytes,
    stackBelow]
  sig_split h
  sig_and_intros <;> with_reducible assumption

/-- `randomSignSatState` with `validPrivateKeyWitness` at `0x2000`. -/
def randomPrevalidatedSatState : State where
  gpr := randomSignSatState.gpr
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x21a8 then
    VG.Proof.Dsa.validPrivateKeyWitness[a.toNat - 0x2000]?.getD 0 else randomSignSatState.mem a
  rd := randomSignSatState.rd
  wr := randomSignSatState.wr

theorem randomPrevalidated_satisfiable :
    ∃ s, (Spec.Dsa.randomSignPrevalidatedContract abi 232).pre s := by
  have a0 : arg randomPrevalidatedSatState 0 = 0x1000 := by decide
  have a1 : arg randomPrevalidatedSatState 1 = 40 := by decide
  have a2 : arg randomPrevalidatedSatState 2 = 0x7000 := by decide
  have a3 : arg randomPrevalidatedSatState 3 = 0x2000 := by decide
  have a4 : arg randomPrevalidatedSatState 4 = 424 := by decide
  have a5 : arg randomPrevalidatedSatState 5 = 128 := by decide
  have a6 : arg randomPrevalidatedSatState 6 = 20 := by decide
  have a7 : arg randomPrevalidatedSatState 7 = 0x5000 := by decide
  have a8 : arg randomPrevalidatedSatState 8 = 0 := by decide
  have a9 : arg randomPrevalidatedSatState 9 = 0x6000 := by decide
  have a10 : arg randomPrevalidatedSatState 10 = 0 := by decide
  have a11 : arg randomPrevalidatedSatState 11 = 0x8000 := by decide
  have a12 : arg randomPrevalidatedSatState 12 = 2112 := by decide
  have e : argAddr randomPrevalidatedSatState 0 = 0x20004 := by decide
  have esp : randomPrevalidatedSatState.gpr .esp = 0x20000 := rfl
  have ho : ∃ s, (Spec.Dsa.randomSignContract abi 232).pre s ∧ s = randomPrevalidatedSatState := by
    sig_implies_sat [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argSlots, argVal, argBytes,
      stackBelow] [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e, esp, randomPrevalidatedSatState,
      randomSignSatState] using randomPrevalidatedSatState
  obtain ⟨s, h, rfl⟩ := ho
  refine ⟨_, randomPrevalidated_of_pre h ?_⟩
  have p3 : argumentPointer randomPrevalidatedSatState 3 = BitVec.ofNat 64 0x2000 := by
    unfold argumentPointer; rw [a3]; rfl
  show Spec.Dsa.validatePrivateKeyBytes (arg randomPrevalidatedSatState 5).toNat
    (arg randomPrevalidatedSatState 6).toNat (Spec.Rsa.bytesAt randomPrevalidatedSatState.mem
      (argumentPointer randomPrevalidatedSatState 3) (arg randomPrevalidatedSatState 4).toNat) = true
  have key : Spec.Rsa.bytesAt randomPrevalidatedSatState.mem (argumentPointer randomPrevalidatedSatState 3)
      (arg randomPrevalidatedSatState 4).toNat = VG.Proof.Dsa.validPrivateKeyWitness := by
    rw [p3, a4]
    exact bytesAt_window (base := 0x2000) VG.Proof.Dsa.validPrivateKeyWitness_length (by decide)
      fun a h₁ h₂ => by simp only [randomPrevalidatedSatState]; exact ite_eq_left ⟨h₁, h₂⟩
  rw [key, a5, a6]
  exact VG.Proof.Dsa.validPrivateKeyWitness_valid

/-- A signer for validated keys, in the randomized wrapper. -/
theorem randomSignPrevalidated_verified (F : SignFn) (hF : F.valid = Spec.Dsa.validatePrivateKeyBytes) :
    Verified target (code F.name F.code) (Spec.Dsa.randomSignPrevalidatedContract abi 232) := by
  obtain ⟨name, code, valid, verified, noSp, depth⟩ := F
  subst hF
  exact ⟨fun s h => randomSign_correct ⟨name, code, _, verified, noSp, depth⟩ s
      (randomPrevalidated_pre h).1 (randomPrevalidated_pre h).2,
    fun s t tr ur sf tf hs ht => randomSign_constantTime ⟨name, code, _, verified, noSp, depth⟩
      s t tr ur sf tf (randomPrevalidated_pre hs) (randomPrevalidated_pre ht),
    randomPrevalidated_satisfiable⟩

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86

/-! ## Signing for a validated private key against `signContractWith validatePrivateKeyBytes` -/

/-- The fully checked signer, against `signContractWith` of a predicate
every key satisfies. -/
theorem signing_verified_with :
    Verified target (Entry.operation true) (signContractWith (fun _ _ _ => true) abi 108) :=
  Verified.of_narrow signing_verified (fun s => s) (fun _ s => s)
    (fun _ h => (signWith_pre h).1) (fun _ _ _ _ e => e) (fun _ _ _ _ _ ha hp => ⟨ha, hp⟩)
    (fun _ _ _ _ h => h)
    (by obtain ⟨s, hs⟩ := signing_verified.2.2; exact ⟨s, signWith_of_pre hs rfl⟩)

theorem prevalidatedSigningCorrect (s : State)
    (h : (signContractWith Spec.Dsa.validatePrivateKeyBytes abi 108).pre s) :
    ∃ trace t, Exec isa PrevalidatedSign.sign s trace t ∧ abiPreserved s t ∧
      (signContractWith Spec.Dsa.validatePrivateKeyBytes abi 108).post s t := by
  obtain ⟨hp, hv⟩ := signWith_pre h
  obtain ⟨trace, t, E, V, B, ABI, _⟩ := prevalidatedSigningOperation_spec (signingABI_of hp) hv
  refine ⟨trace, t, E, ABI, ?_⟩
  sig_post [signContractWith, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes]
  change ((t.gpr .edx ++ t.gpr .eax).setWidth 32).toNat = _ ∧ _
  rw [BitVec.setWidth_append_eq_right]
  exact ⟨V, B⟩

theorem prevalidatedSigningConstantTime :
    ConstantTime isa (signContractWith Spec.Dsa.validatePrivateKeyBytes abi 108).pre
      (signContractWith Spec.Dsa.validatePrivateKeyBytes abi 108).pub PrevalidatedSign.sign := by
  intro s t tr ur sf tf S T H E F
  change (Spec.Dsa.signContract abi 108).pub s t at H
  have Args := signingPublicArgs H
  have Domain := signingPublicDomain H
  exact prevalidatedSigningOperation_agrees (signingABI_of (signWith_pre S).1)
    (signingABI_of (signWith_pre T).1) Args.2 Args.1 Domain.1 Domain.2 E F

/-- `signingSatState` with `validPrivateKeyWitness` at `0x2000`. -/
def prevalidatedSignSatState : State where
  gpr := signingSatState.gpr
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x21a8 then
    VG.Proof.Dsa.validPrivateKeyWitness[a.toNat - 0x2000]?.getD 0 else signingSatState.mem a
  rd := signingSatState.rd
  wr := signingSatState.wr

theorem prevalidatedSignSatisfiable :
    ∃ s, (signContractWith Spec.Dsa.validatePrivateKeyBytes abi 108).pre s := by
  have a0 : arg prevalidatedSignSatState 0 = 4096 := by decide
  have a1 : arg prevalidatedSignSatState 1 = 40 := by decide
  have a2 : arg prevalidatedSignSatState 2 = 8192 := by decide
  have a3 : arg prevalidatedSignSatState 3 = 424 := by decide
  have a4 : arg prevalidatedSignSatState 4 = 128 := by decide
  have a5 : arg prevalidatedSignSatState 5 = 16384 := by decide
  have a6 : arg prevalidatedSignSatState 6 = 20 := by decide
  have a7 : arg prevalidatedSignSatState 7 = 20480 := by decide
  have a8 : arg prevalidatedSignSatState 8 = 0 := by decide
  have a9 : arg prevalidatedSignSatState 9 = 32768 := by decide
  have a10 : arg prevalidatedSignSatState 10 = 2048 := by decide
  have e : argAddr prevalidatedSignSatState 0 = 0x20004 := by decide
  have esp : prevalidatedSignSatState.gpr .esp = 0x20000 := rfl
  have ho : ∃ s, (Spec.Dsa.signContract abi 108).pre s ∧ s = prevalidatedSignSatState := by
    sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes, stackBelow]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp, prevalidatedSignSatState, signingSatState]
      using prevalidatedSignSatState
  obtain ⟨s, h, rfl⟩ := ho
  have key : Spec.Rsa.bytesAt prevalidatedSignSatState.mem (argumentPointer prevalidatedSignSatState 2)
      (arg prevalidatedSignSatState 3).toNat = VG.Proof.Dsa.validPrivateKeyWitness := by
    have p2 : argumentPointer prevalidatedSignSatState 2 = BitVec.ofNat 64 0x2000 := by
      unfold argumentPointer; rw [a2]; rfl
    rw [p2, a3]
    exact bytesAt_window (base := 0x2000) VG.Proof.Dsa.validPrivateKeyWitness_length (by decide)
      fun a h₁ h₂ => by
        simp only [prevalidatedSignSatState]
        exact ite_eq_left ⟨h₁, h₂⟩
  refine ⟨_, signWith_of_pre h ?_⟩
  rw [key, a4, a6]
  exact VG.Proof.Dsa.validPrivateKeyWitness_valid

theorem prevalidatedSigning_verified :
    Verified target PrevalidatedSign.sign (signContractWith Spec.Dsa.validatePrivateKeyBytes abi 108) :=
  ⟨prevalidatedSigningCorrect, prevalidatedSigningConstantTime, prevalidatedSignSatisfiable⟩

/-! ## The randomized signer's instances -/

/-- The fully checked supplied-nonce signer. -/
def signFn : SignFn where
  name := "vg_dsa_sign"
  code := Entry.operation true
  valid := fun _ _ _ => true
  verified := signing_verified_with
  noSp := NoSp.of_all (by decide +kernel)
  depth := by decide +kernel

theorem randomSigning_verified :
    Verified target (RandomSign.code signFn.name signFn.code) (Spec.Dsa.randomSignContract abi 232) :=
  randomSign_verified signFn fun _ => rfl

/-- The supplied-nonce signer for a validated private key, as registered. -/
def prevalidatedSignFn : SignFn where
  name := "vg_dsa_sign_prevalidated"
  code := PrevalidatedSign.sign
  valid := Spec.Dsa.validatePrivateKeyBytes
  verified := prevalidatedSigning_verified
  noSp := NoSp.of_all (by decide +kernel)
  depth := by decide +kernel

theorem randomSigningPrevalidated_verified :
    Verified target (RandomSign.code prevalidatedSignFn.name prevalidatedSignFn.code)
      (Spec.Dsa.randomSignPrevalidatedContract abi 232) :=
  randomSignPrevalidated_verified prevalidatedSignFn rfl

end VG.Proof.Dsa.X86
