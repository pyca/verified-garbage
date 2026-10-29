module

public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
public import VerifiedGarbage.Spec.Dsa.RandomSign

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCorrect
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignConstantTime
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
/-! Complete verification of randomized DSA signing for every AArch64 backend. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64

def randomSignSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 40 | .x2 => 0x7000 | .x3 => 0x2000
    | .x4 => 424 | .x5 => 128 | .x6 => 20 | .x7 => 0x5000 | _ => 0
  sp := 0x1000000000000
  mem a := if a = 0x1000000000009 then 0x60 else if a = 0x1000000000019 then 0x80
    else if a = 0x1000000000020 then 0x40 else if a = 0x1000000000021 then 8 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x5000, 0⟩, ⟨0x6000, 0⟩, ⟨0x1000000000000, 40⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x7000, 8⟩, ⟨0x8000, 16896⟩]

private theorem sat_arg_0 : stackArg randomSignSatState 0 = 0 := by decide +kernel
private theorem sat_arg_1 : stackArg randomSignSatState 1 = 24576 := by decide +kernel
private theorem sat_arg_2 : stackArg randomSignSatState 2 = 0 := by decide +kernel
private theorem sat_arg_3 : stackArg randomSignSatState 3 = 32768 := by decide +kernel
private theorem sat_arg_4 : stackArg randomSignSatState 4 = 2112 := by decide +kernel

theorem random_sign_satisfiable (v : Backend) :
    ∃ s, (Spec.Dsa.randomSignContract abi (v.stack + 256)).pre s := by
  have hb := v.stackBound
  refine ⟨randomSignSatState, ?_⟩
  sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs]
  sig_and_intros
  all_goals try simp only [sat_arg_0, sat_arg_1, sat_arg_2, sat_arg_3, sat_arg_4]
  all_goals first
    | (change v.stack + 256 ≤ 281474976710656; omega)
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel
    | (intro a h₁ h₂; simp only [Region.Contains, stackArgAddr, randomSignSatState] at h₁ h₂; bv_omega)

theorem random_sign_verified (v : Backend) :
    Verified target (RandomSign.code (randomSignerName v) (SignVerify.sign v.mul))
      (Spec.Dsa.randomSignContract abi (v.stack + 256)) :=
  ⟨random_sign_correct v, random_sign_constantTime v, random_sign_satisfiable v⟩

end VG.Proof.Dsa.AArch64
