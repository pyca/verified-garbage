module

public import VerifiedGarbage.Proof.Dsa.X86.PrevalidatedVerified
public import VerifiedGarbage.Impl.Dsa.X86.RandomSign
public import VerifiedGarbage.Proof.Dsa.X86.RandomAttempt
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.PrivateKeyWitness
import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Dsa.X86.RandomBodyCT
public import VerifiedGarbage.Proof.Dsa.SignContractWith
import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
public import VerifiedGarbage.Impl.Dsa.X86.PrevalidatedSign
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Dsa.X86.PrevalidatedSignCT
import VerifiedGarbage.Proof.Dsa.X86.PublicDomain

/-! ### `Dsa.X86.RandomSignCT`, which only this module used -/

section

/-!
# The randomized signer is constant time (x86)

The contract's public data (the arguments, the public key bytes, the status,
the consumption and the trace) gives two entries the same `BodyPub`, and the
frame's allocation leaks nothing.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random VG.Impl.Dsa.X86.RandomSign

theorem drop_take_prefix {α : Type} (xs : List α) {p q n : Nat} (h : p + q ≤ n) :
    (xs.drop p).take q = ((xs.take n).drop p).take q := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega_using [h])]

/-- Two entries with the same public data: the same arguments, q, public
key bytes, status and trace. -/
theorem random_public {s t : State} (H : (randomSignCheckedContract abi 232).pub s t) :
    pubOf s = pubOf t ∧ keyLeak s = keyLeak t ∧ (rResult s).status = (rResult t).status ∧
      (rResult s).trace = (rResult t).trace := by
  sig_pub [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argSlots, argVal, argBytes] at H
  obtain ⟨hsp, hleak, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := H
  change keyLeak s ++ [(rResult s).status, (rResult s).used] ++ (rResult s).trace =
    keyLeak t ++ [(rResult t).status, (rResult t).used] ++ (rResult t).trace at hleak
  have hlen : (keyLeak s).length = (keyLeak t).length := by
    simp only [keyLeak, Spec.Dsa.publicBytesLeak, rInput, List.length_map, List.length_take, rBytes_length,
      a4, a5, a6]
  rw [List.append_assoc, List.append_assoc] at hleak
  obtain ⟨hk, hrest⟩ := List.append_inj hleak hlen
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrest
  obtain ⟨hst, -, htr⟩ := hrest
  refine ⟨?_, hk, hst, htr⟩
  have hargs : ∀ i < 13, X86.arg s i = X86.arg t i := by
    intro i hi
    have c : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 := by omega_using [hi]
    rcases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]
  have hkey : (rInput s).key.take (3 * (rInput s).pLen + (rInput s).qLen) =
      (rInput t).key.take (3 * (rInput t).pLen + (rInput t).qLen) :=
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hk
  have hp : (rInput s).pLen = (rInput t).pLen := congrArg BitVec.toNat a5
  have hq : (rInput s).qLen = (rInput t).qLen := congrArg BitVec.toNat a6
  simp only [pubOf, Pub.mk.injEq]
  refine ⟨hsp, List.map_congr_left fun i hi => hargs i (List.mem_range.mp hi), ?_⟩
  unfold rQBytes
  rw [drop_take_prefix _ (n := 3 * (rInput s).pLen + (rInput s).qLen) (by omega_using []), hkey,
    drop_take_prefix (rInput t).key (n := 3 * (rInput t).pLen + (rInput t).qLen) (by omega_using []), hp, hq]

theorem alloc_push {s₀ : State} (A : RandomSignABI s₀) :
    isa.push (.alloc Random.frameBytes) s₀ = some (allocated Random.frameBytes s₀) := by
  have hsp : Random.frameBytes ≤ (s₀.gpr .esp).toNat := by have := A.stackLow; unfold Random.frameBytes; omega_using [this]
  have hn : 0 < Random.frameBytes ∧ Random.frameBytes < 4096 ∧ Random.frameBytes % 4 = 0 := by decide
  simp only [isa, push, hn.1, hn.2.1, hn.2.2, hsp, and_self, ite_true]
  rfl

/-- `vg_dsa_sign_random` leaks only what its contract makes public. -/
theorem randomSign_constantTime (F : SignFn) :
    ConstantTime isa (fun s => (randomSignCheckedContract abi 232).pre s ∧ KeyValid F.valid s)
      (randomSignCheckedContract abi 232).pub (code F.name F.code) := by
  intro s t tsa tsb u w ⟨hs, hvs⟩ ⟨ht, hvt⟩ hpub ea eb
  have As := randomSignABI_of hs
  have At' := randomSignABI_of ht
  obtain ⟨e, hk, hst, htr⟩ := random_public hpub
  cases ea with
  | frame hap hab _ =>
    cases eb with
    | frame hbp hbb _ =>
      rw [alloc_push As, Option.some.injEq] at hap
      rw [alloc_push At', Option.some.injEq] at hbp
      subst hap hbp
      have hh := body_ct F _ _ _ _ _ _ ⟨⟨pubOf s, keyLeak s, (rResult s).status, (rResult s).trace⟩,
        ⟨s, As, rfl, ⟨rfl, rfl, rfl, hvs⟩, rfl⟩,
        ⟨t, At', e.symm, ⟨hk.symm, hst.symm, htr.symm, hvt⟩, rfl⟩⟩ hab hbb |>.1
      simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using hh

end VG.Proof.Dsa.X86

end

end


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

theorem randomSign_satisfiable : ∃ s, (randomSignCheckedContract abi 232).pre s := by
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
  sig_implies_sat [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argSlots, argVal, argBytes,
    stackBelow] [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e, esp, randomSignSatState]
    using randomSignSatState

/-- A signer that accepts every key, in the randomized wrapper. -/
theorem randomSign_verified (F : SignFn) (hall : ∀ s, KeyValid F.valid s) :
    Verified target (code F.name F.code) (randomSignCheckedContract abi 232) :=
  ⟨fun s h => randomSign_correct F s h (hall s),
    fun s t tr ur sf tf hs ht => randomSign_constantTime F s t tr ur sf tf ⟨hs, hall s⟩ ⟨ht, hall t⟩,
    randomSign_satisfiable⟩

theorem randomPrevalidated_pre {s : State} (h : (Spec.Dsa.randomSignPrevalidatedContract abi 232).pre s) :
    (randomSignCheckedContract abi 232).pre s ∧ KeyValid Spec.Dsa.validatePrivateKeyBytes s := by
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  sig_split h
  refine ⟨?_, by unfold KeyValid rInput; assumption⟩
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros <;> with_reducible assumption

theorem randomPrevalidated_of_pre {s : State} (h : (randomSignCheckedContract abi 232).pre s)
    (hv : KeyValid Spec.Dsa.validatePrivateKeyBytes s) :
    (Spec.Dsa.randomSignPrevalidatedContract abi 232).pre s := by
  unfold KeyValid rInput at hv
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argSlots, argVal, argBytes, stackBelow] at h
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
  have ho : ∃ s, (randomSignCheckedContract abi 232).pre s ∧ s = randomPrevalidatedSatState := by
    sig_implies_sat [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argSlots, argVal, argBytes,
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
    Verified target (RandomSign.code signFn.name signFn.code) (randomSignCheckedContract abi 232) :=
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
