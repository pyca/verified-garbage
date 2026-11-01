module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Offset

/-! # A concrete i686 state meets the prepared multiplication contract -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86

def satWord (k : Nat) : BitVec 64 :=
  if k = 6 then 2 else if k = 7 then 0xFFFFFFFFFFFFFFFF
  else if 8 ≤ k ∧ k < 16 then BitVec.ofNat 64 (0x1100 + (k - 8) * 32)
  else if k = 32 then 1 else 0

def satArg (i : Nat) : BitVec 32 :=
  if i = 0 then 0x1000 else if i = 1 then 64 else 1

def satMem : Mem := fun x =>
  if (x - 0x1000).toNat < 512 then
    (satWord ((x - 0x1000).toNat / 8)).extractLsb' (8 * ((x - 0x1000).toNat % 8)) 8
  else if (x - 0x8004).toNat < 20 then
    (satArg ((x - 0x8004).toNat / 4)).extractLsb' (8 * ((x - 0x8004).toNat % 4)) 8
  else 0

def satState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x8004, 20⟩]
  wr := [⟨0x1000, 512⟩]

theorem satisfiable : ∃ s, (Proof.Rsa.Mont.mulContract abi 16).pre s := by
  sig_implies_sat [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argSlots, argVal, argBytes, stackBelow]
    [satState, arg, argAddr, Mem.readW, Mem.read] using satState

end VG.Proof.Mont.X86.Compact
