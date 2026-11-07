module

public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallResult
public import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedSignVerified
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignABI

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCorrect
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignConstantTime
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
/-! Complete verification of randomized DSA signing for every AArch64 backend:
`vg_dsa_sign_random`, which calls the fully checked signer, and
`vg_dsa_sign_random_prevalidated`, which calls the signer for a validated
private key. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64

def randomSignSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 40 | .x2 => 0x7000 | .x3 => 0x2000
    | .x4 => 424 | .x5 => 128 | .x6 => 20 | .x7 => 0x5000 | _ => 0
  sp := 0x1000000000000
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x21a8 then
      VG.Proof.Dsa.validPrivateKeyWitness[a.toNat - 0x2000]?.getD 0
    else if a = 0x1000000000009 then 0x60 else if a = 0x1000000000019 then 0x80
    else if a = 0x1000000000020 then 0x40 else if a = 0x1000000000021 then 8 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x5000, 0⟩, ⟨0x6000, 0⟩, ⟨0x1000000000000, 40⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x7000, 8⟩, ⟨0x8000, 16896⟩]

private theorem sat_arg_0 : stackArg randomSignSatState 0 = 0 := by decide +kernel
private theorem sat_arg_1 : stackArg randomSignSatState 1 = 24576 := by decide +kernel
private theorem sat_arg_2 : stackArg randomSignSatState 2 = 0 := by decide +kernel
private theorem sat_arg_3 : stackArg randomSignSatState 3 = 32768 := by decide +kernel
private theorem sat_arg_4 : stackArg randomSignSatState 4 = 2112 := by decide +kernel

theorem random_sign_sat_pre (extra : Nat) (hb : extra < 2 ^ 32) :
    (Spec.Dsa.randomSignContract abi (extra + 256)).pre randomSignSatState := by
  sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs]
  sig_and_intros
  all_goals try simp only [sat_arg_0, sat_arg_1, sat_arg_2, sat_arg_3, sat_arg_4]
  all_goals first
    | (change extra + 256 ≤ 281474976710656; omega)
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel
    | (intro a h₁ h₂; simp only [Region.Contains, stackArgAddr, randomSignSatState] at h₁ h₂; bv_omega)

theorem random_sign_satisfiable (v : Backend) :
    ∃ s, (Spec.Dsa.randomSignContract abi (v.stack + 256)).pre s :=
  ⟨_, random_sign_sat_pre v.stack v.stackBound⟩

/-- A backend's fully checked signer, which accepts every key. -/
def Backend.signer (v : Backend) : Signer where
  name := randomSignerName v
  code := SignVerify.sign v.mul
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
    Verified target (RandomSign.code (randomSignerName v) (SignVerify.sign v.mul))
      (Spec.Dsa.randomSignContract abi (v.stack + 256)) :=
  ⟨fun s h => random_sign_correct v.signer s h rfl,
    fun s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ => random_sign_constantTime v.signer s₁ s₂ t₁ t₂ u₁ u₂ ⟨h₁, rfl⟩ ⟨h₂, rfl⟩,
    random_sign_satisfiable v⟩

def prevalidatedSignerName (v : Backend) : String := "vg_dsa_sign_prevalidated" ++ v.suffix

/-- A backend's signer for a validated private key. -/
def Backend.prevalidatedSigner (v : Backend) : Signer where
  name := prevalidatedSignerName v
  code := PrevalidatedSign.sign v.mul
  stack := v.stack
  valid := Spec.Dsa.validatePrivateKeyBytes
  verified := v.prevalidatedSignVerified
  sp := v.prevalidatedSignSp
  depth := v.prevalidatedSignDepth
  stackBound := v.stackBound

theorem randomPrevalidated_pre {extra : Nat} {s : State}
    (h : (Spec.Dsa.randomSignPrevalidatedContract abi (extra + 256)).pre s) :
    (Spec.Dsa.randomSignContract abi (extra + 256)).pre s ∧
      Spec.Dsa.validatePrivateKeyBytes (s.gpr .x5).toNat (s.gpr .x6).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) = true := by
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs,
    show extra + 256 = (extra + 255) + 1 from rfl] at h
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, abi, argRegs,
    randomSignStackArgs] at h
  sig_split h
  refine ⟨?_, by assumption⟩
  sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs,
    show extra + 256 = (extra + 255) + 1 from rfl]
  sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs]
  sig_and_intros <;> with_reducible assumption

theorem randomPrevalidated_of_pre {extra : Nat} {s : State}
    (h : (Spec.Dsa.randomSignContract abi (extra + 256)).pre s)
    (hv : Spec.Dsa.validatePrivateKeyBytes (s.gpr .x5).toNat (s.gpr .x6).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) = true) :
    (Spec.Dsa.randomSignPrevalidatedContract abi (extra + 256)).pre s := by
  sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs,
    show extra + 256 = (extra + 255) + 1 from rfl] at h
  sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs] at h
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs,
    show extra + 256 = (extra + 255) + 1 from rfl]
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, abi, argRegs,
    randomSignStackArgs]
  sig_split h
  sig_and_intros <;> with_reducible assumption

theorem random_sign_sat_key :
    Spec.Rsa.bytesAt randomSignSatState.mem 0x2000 424 = VG.Proof.Dsa.validPrivateKeyWitness := by
  decide +kernel

theorem random_sign_prevalidated_verified (v : Backend) :
    Verified target (RandomSign.code (prevalidatedSignerName v) (PrevalidatedSign.sign v.mul))
      (Spec.Dsa.randomSignPrevalidatedContract abi (v.stack + 256)) :=
  ⟨fun s h => random_sign_correct v.prevalidatedSigner s (randomPrevalidated_pre h).1
      (randomPrevalidated_pre h).2,
    fun s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ => random_sign_constantTime v.prevalidatedSigner s₁ s₂ t₁ t₂ u₁ u₂
      (randomPrevalidated_pre h₁) (randomPrevalidated_pre h₂),
    ⟨_, randomPrevalidated_of_pre (random_sign_sat_pre v.stack v.stackBound) (by
      change Spec.Dsa.validatePrivateKeyBytes 128 20 (Spec.Rsa.bytesAt randomSignSatState.mem 0x2000 424) = true
      rw [random_sign_sat_key]
      exact VG.Proof.Dsa.validPrivateKeyWitness_valid)⟩⟩

end VG.Proof.Dsa.AArch64
