module
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyCheck

import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyConstantTime
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyCorrect

/-! # Complete verification of DSA key generation for every x86-64 backend -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64

def keygenSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 424 | .rdx => 0x7000 | .rcx => 0x2000
    | .r8 => 276 | .r9 => 128 | .rsp => 0x1000000000000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x1000000000008 then 20 else if a = 0x1000000000011 then 0x50
    else if a = 0x1000000000021 then 0x80 else if a = 0x1000000000029 then 0x24 else 0
  rd := [⟨0x2000, 276⟩, ⟨0x5000, 0⟩, ⟨0x1000000000008, 40⟩]
  wr := [⟨0x1000, 424⟩, ⟨0x7000, 8⟩, ⟨0x8000, 73728⟩]

private theorem sat_arg_0 : stackArg keygenSatState 0 = 20 := by
  decide +kernel

private theorem sat_arg_1 : stackArg keygenSatState 1 = 20480 := by
  decide +kernel

private theorem sat_arg_2 : stackArg keygenSatState 2 = 0 := by
  decide +kernel

private theorem sat_arg_3 : stackArg keygenSatState 3 = 32768 := by
  decide +kernel

private theorem sat_arg_4 : stackArg keygenSatState 4 = 9216 := by
  decide +kernel

theorem keygen_satisfiable (v : Backend) :
    ∃ s, (Spec.Dsa.generateKeyContract abi (v.stack + 256)).pre s := by
  have hb := v.stackBound
  refine ⟨keygenSatState, ?_⟩
  sig_pre [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, stackArgs_five']
  sig_and_intros
  all_goals try simp only [sat_arg_0, sat_arg_1, sat_arg_2, sat_arg_3, sat_arg_4]
  all_goals first
    | (change v.stack + 256 ≤ 281474976710656; omega)
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel
    | (intro a h₁ h₂; simp only [Region.Contains, stackArgAddr, keygenSatState] at h₁ h₂; bv_omega)

theorem keygen_verified (v : Backend) :
    Verified target (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.sq v.mul)
        (Generate.deriveKey v.sq v.mul))
      (Spec.Dsa.generateKeyContract abi (v.stack + 256)) :=
  ⟨keygen_correct v, keygen_constantTime v, keygen_satisfiable v⟩

end VG.Proof.Dsa.X86_64
