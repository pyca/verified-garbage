module
public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCall
public import VerifiedGarbage.Spec.Dsa.RandomSign

import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCorrect
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignConstantTime
import VerifiedGarbage.Proof.Framework.Omega

/-! Complete verification of randomized DSA signing for every x86-64 backend. -/
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
  mem a := if a = 0x1000000000008 then 20 else if a = 0x1000000000011 then 0x50
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

theorem random_sign_satisfiable (v : Backend) :
    ∃ s, (Spec.Dsa.randomSignContract abi (v.stack + 256)).pre s := by
  have hb := v.stackBound
  refine ⟨randomSignSatState, ?_⟩
  sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, stackArgs_seven]
  sig_and_intros
  all_goals try simp only [sat_arg_0, sat_arg_1, sat_arg_2, sat_arg_3, sat_arg_4, sat_arg_5, sat_arg_6]
  all_goals first
    | (change v.stack + 256 ≤ 281474976710656; omega)
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel
    | (intro a h₁ h₂; simp only [Region.Contains, stackArgAddr, randomSignSatState] at h₁ h₂; bv_omega)

theorem random_sign_verified (v : Backend) :
    Verified target (RandomSign.code (randomSignerName v) (SignVerify.sign v.sq v.mul))
      (Spec.Dsa.randomSignContract abi (v.stack + 256)) :=
  ⟨random_sign_correct v, random_sign_constantTime v, random_sign_satisfiable v⟩

end VG.Proof.Dsa.X86_64
