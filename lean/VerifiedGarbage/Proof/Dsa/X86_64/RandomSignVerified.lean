module

public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCall
public import VerifiedGarbage.Spec.Dsa.RandomSign

public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallResult
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCorrect
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignConstantTime
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignABI
public import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedSignVerified
public import VerifiedGarbage.Proof.Dsa.SignContractWith
import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedVerified
import VerifiedGarbage.Proof.Framework.Omega
/-! Complete verification of randomized DSA signing for every x86-64 backend:
`vg_dsa_sign_random`, which calls the fully checked signer, and
`vg_dsa_sign_random_prevalidated`, which calls the signer for a validated
private key. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64

def randomSignSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 40 | .rdx => 0x7000 | .rcx => 0x2000
    | .r8 => 424 | .r9 => 128 | .rsp => 0x1000000000000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x21a8 then validPrivateKeyWitness[a.toNat - 0x2000]?.getD 0
    else if a = 0x1000000000008 then 20 else if a = 0x1000000000011 then 0x50
    else if a = 0x1000000000021 then 0x60 else if a = 0x1000000000031 then 0x80
    else if a = 0x1000000000038 then 0x40 else if a = 0x1000000000039 then 8 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x5000, 0⟩, ⟨0x6000, 0⟩, ⟨0x1000000000008, 56⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x7000, 8⟩, ⟨0x8000, 16896⟩]

private theorem sat_arg_0 : stackArg randomSignSatState 0 = 20 := by
  decide +kernel

private theorem sat_arg_1 : stackArg randomSignSatState 1 = 20480 := by
  decide +kernel

private theorem sat_arg_2 : stackArg randomSignSatState 2 = 0 := by
  decide +kernel

private theorem sat_arg_3 : stackArg randomSignSatState 3 = 24576 := by
  decide +kernel

private theorem sat_arg_4 : stackArg randomSignSatState 4 = 0 := by
  decide +kernel

private theorem sat_arg_5 : stackArg randomSignSatState 5 = 32768 := by
  decide +kernel

private theorem sat_arg_6 : stackArg randomSignSatState 6 = 2112 := by
  decide +kernel

theorem random_sign_sat_pre (extra : Nat) (hb : extra < 2 ^ 32) :
    (randomSignCheckedContract abi (extra + 256)).pre randomSignSatState := by
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, stackArgs_seven]
  sig_and_intros
  all_goals try simp only [sat_arg_0, sat_arg_1, sat_arg_2, sat_arg_3, sat_arg_4, sat_arg_5, sat_arg_6]
  all_goals first
    | (change extra + 256 ≤ 281474976710656; omega)
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel
    | (intro a h₁ h₂; simp only [Region.Contains, stackArgAddr, randomSignSatState] at h₁ h₂; bv_omega)

theorem random_sign_satisfiable (v : Backend) :
    ∃ s, (randomSignCheckedContract abi (v.stack + 256)).pre s :=
  ⟨_, random_sign_sat_pre v.stack v.stackBound⟩

/-- A backend's fully checked signer, which accepts every key. -/
def Backend.signer (v : Backend) : Signer where
  name := randomSignerName v
  code := SignVerify.sign v.sq v.mul
  stack := v.stack
  valid := fun _ _ _ => true
  verified := Verified.of_narrow v.signVerified (fun s => s) (fun _ s => s)
    (fun _ h => (signWith_pre h).1) (fun _ _ _ _ e => e) (fun _ _ _ _ _ ha hp => ⟨ha, signWith_post hp⟩)
    (fun _ _ _ _ h => signWith_pub h)
    (by obtain ⟨s, hs⟩ := v.signVerified.2.2; exact ⟨s, signWith_of_pre hs rfl⟩)
  sp := v.signSp
  depth := v.signDepth
  stackBound := v.stackBound

theorem random_sign_verified (v : Backend) :
    Verified target (RandomSign.code (randomSignerName v) (SignVerify.sign v.sq v.mul))
      (randomSignCheckedContract abi (v.stack + 256)) :=
  ⟨fun s h => random_sign_correct v.signer s h rfl,
    fun s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ => random_sign_constantTime v.signer s₁ s₂ t₁ t₂ u₁ u₂ ⟨h₁, rfl⟩ ⟨h₂, rfl⟩,
    random_sign_satisfiable v⟩

def prevalidatedSignerName (v : Backend) : String := "vg_dsa_sign_prevalidated" ++ v.suffix

/-- A backend's signer for a validated private key. -/
def Backend.prevalidatedSigner (v : Backend) : Signer where
  name := prevalidatedSignerName v
  code := PrevalidatedSign.sign v.sq v.mul
  stack := v.stack
  valid := Spec.Dsa.validatePrivateKeyBytes
  verified := v.prevalidatedSignVerified
  sp := v.prevalidatedSignSp
  depth := v.prevalidatedSignDepth
  stackBound := v.stackBound

theorem randomPrevalidated_pre {extra : Nat} {s : State}
    (h : (Spec.Dsa.randomSignPrevalidatedContract abi (extra + 256)).pre s) :
    (randomSignCheckedContract abi (extra + 256)).pre s ∧
      Spec.Dsa.validatePrivateKeyBytes (s.gpr .r9).toNat (stackArg s 0).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) = true := by
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, abi, argRegs, stackArgs_seven,
    show extra + 256 = (extra + 255) + 1 from rfl, List.range, List.range.loop] at h
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, abi, argRegs, stackArgs_seven,
    List.range, List.range.loop] at h
  sig_split h
  refine ⟨?_, by assumption⟩
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, stackArgs_seven,
    show extra + 256 = (extra + 255) + 1 from rfl, List.range, List.range.loop]
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, stackArgs_seven,
    List.range, List.range.loop]
  sig_and_intros <;> with_reducible assumption

theorem randomPrevalidated_of_pre {extra : Nat} {s : State}
    (h : (randomSignCheckedContract abi (extra + 256)).pre s)
    (hv : Spec.Dsa.validatePrivateKeyBytes (s.gpr .r9).toNat (stackArg s 0).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) = true) :
    (Spec.Dsa.randomSignPrevalidatedContract abi (extra + 256)).pre s := by
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, stackArgs_seven,
    show extra + 256 = (extra + 255) + 1 from rfl, List.range, List.range.loop] at h
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, stackArgs_seven,
    List.range, List.range.loop] at h
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, abi, argRegs, stackArgs_seven,
    show extra + 256 = (extra + 255) + 1 from rfl, List.range, List.range.loop]
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, abi, argRegs, stackArgs_seven,
    List.range, List.range.loop]
  sig_split h
  sig_and_intros <;> with_reducible assumption

theorem random_sign_sat_key :
    Spec.Rsa.bytesAt randomSignSatState.mem 0x2000 424 = validPrivateKeyWitness :=
  bytesAt_window (base := 0x2000) validPrivateKeyWitness_length (by decide) fun a h₁ h₂ => by
    simp only [randomSignSatState]
    exact ite_eq_left ⟨h₁, h₂⟩

theorem random_sign_prevalidated_verified (v : Backend) :
    Verified target (RandomSign.code (prevalidatedSignerName v) (PrevalidatedSign.sign v.sq v.mul))
      (Spec.Dsa.randomSignPrevalidatedContract abi (v.stack + 256)) :=
  ⟨fun s h => random_sign_correct v.prevalidatedSigner s (randomPrevalidated_pre h).1
      (randomPrevalidated_pre h).2,
    fun s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ => random_sign_constantTime v.prevalidatedSigner s₁ s₂ t₁ t₂ u₁ u₂
      (randomPrevalidated_pre h₁) (randomPrevalidated_pre h₂),
    ⟨_, randomPrevalidated_of_pre (random_sign_sat_pre v.stack v.stackBound) (by
      change Spec.Dsa.validatePrivateKeyBytes 128 20 (Spec.Rsa.bytesAt randomSignSatState.mem 0x2000 424) = true
      rw [random_sign_sat_key]
      exact validPrivateKeyWitness_valid)⟩⟩

end VG.Proof.Dsa.X86_64
