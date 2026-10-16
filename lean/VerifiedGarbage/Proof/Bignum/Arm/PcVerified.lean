module

public import VerifiedGarbage.Proof.Bignum.Arm.PcContract
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.TCB.Arm.Target
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # ARMv7 public precomputation is verified against the shared RSA contract -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

/-- A 64-byte input with separate output, workspace, and stack arguments. -/
def pcSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 16 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x40 else if a = 0x8004 then 0x20 else if a = 0x8005 then 4 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x4000, 8448⟩]

theorem pc_contract_sat : ∃ s, (Spec.Rsa.publicPrecomputeContract abi 56).pre s := by
  sig_implies_sat [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [pcSatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
      Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, Spec.Rsa.scratchWords] using pcSatState

theorem precompute_verified : Verified target PcFn.code (Spec.Rsa.publicPrecomputeContract abi 56) :=
  ⟨pc_contract_correct, pc_contract_ct, pc_contract_sat⟩

end VG.Proof.Bignum.Arm
