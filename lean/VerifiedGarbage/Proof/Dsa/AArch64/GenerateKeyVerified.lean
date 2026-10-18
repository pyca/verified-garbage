module

public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyConstantTime
import VerifiedGarbage.Proof.Framework.Omega

/-! # Complete verification of DSA key generation for every AArch64 backend -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64

def keygenSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 424 | .x2 => 0x7000 | .x3 => 0x2000
    | .x4 => 276 | .x5 => 128 | .x6 => 20 | .x7 => 0x5000 | _ => 0
  sp := 0x1000000000000
  mem a := if a = 0x1000000000009 then 0x80 else if a = 0x1000000000011 then 0x24 else 0
  rd := [⟨0x2000, 276⟩, ⟨0x5000, 0⟩, ⟨0x1000000000000, 24⟩]
  wr := [⟨0x1000, 424⟩, ⟨0x7000, 8⟩, ⟨0x8000, 73728⟩]

private theorem sat_arg_0 : stackArg keygenSatState 0 = 0 := by decide +kernel
private theorem sat_arg_1 : stackArg keygenSatState 1 = 32768 := by decide +kernel
private theorem sat_arg_2 : stackArg keygenSatState 2 = 9216 := by decide +kernel

theorem keygen_satisfiable (v : Backend) :
    ∃ s, (Spec.Dsa.generateKeyContract abi (v.stack + 256)).pre s := by
  have hb := v.stackBound
  refine ⟨keygenSatState, ?_⟩
  sig_pre [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, keygenStackArgs]
  sig_and_intros
  all_goals try simp only [sat_arg_0, sat_arg_1, sat_arg_2]
  all_goals first
    | (change v.stack + 256 ≤ 281474976710656; omega)
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel
    | (intro a h₁ h₂; simp only [Region.Contains, stackArgAddr, keygenSatState] at h₁ h₂; bv_omega)

theorem keygen_verified (v : Backend) :
    Verified target (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.mul)
        (Generate.deriveKey v.mul))
      (Spec.Dsa.generateKeyContract abi (v.stack + 256)) :=
  ⟨keygen_correct v, keygen_constantTime v, keygen_satisfiable v⟩

end VG.Proof.Dsa.AArch64
