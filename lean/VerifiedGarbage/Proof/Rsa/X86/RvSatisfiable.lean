module
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Rsa.X86.RvABI


/-! # A concrete caller establishes satisfiability of the recovery contract -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16
    else if a = 0x20008 then 64
    else if a = 0x2000d then 32
    else if a = 0x20010 then 64
    else if a = 0x20015 then 64
    else if a = 0x20018 then 64
    else if a = 0x2001d then 80
    else if a = 0x20020 then 1
    else if a = 0x20025 then 96
    else if a = 0x20028 then 1
    else if a = 0x2002e then 1
    else if a = 0x20030 then 32
    else if a = 0x20031 then 4 else 0
  rd := [⟨0x4000, 64⟩, ⟨0x5000, 1⟩, ⟨0x6000, 1⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x10000, 8448⟩, ⟨0x20004, 48⟩]

theorem satisfiable : ∃ s, (Spec.Rsa.recoverPrimesContract abi 96).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 64 := by decide
  have a4 : arg satState 4 = 16384 := by decide
  have a5 : arg satState 5 = 64 := by decide
  have a6 : arg satState 6 = 20480 := by decide
  have a7 : arg satState 7 = 1 := by decide
  have a8 : arg satState 8 = 24576 := by decide
  have a9 : arg satState 9 = 1 := by decide
  have a10 : arg satState 10 = 65536 := by decide
  have a11 : arg satState 11 = 1056 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, e, esp, satState, Spec.Rsa.lenValid, Spec.Rsa.scratchWords] using satState

end VG.Proof.Rsa.X86.Recover
