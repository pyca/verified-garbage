module

import VerifiedGarbage.Proof.Bignum.Arm.MontContract
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.MontContract
meta import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.TCB.Arm.Target
public import Batteries.Logic
public import VerifiedGarbage.Impl.Bignum.Arm.MontFn
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.TCB.Arm.Target

/-! # Verified ARMv7 Montgomery multiplication against the shared RSA contract -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

/-- A minimal valid workspace: two-word numbers and modulus one. -/
def montSatWord (k : Nat) : BitVec 64 :=
  if k = 6 then 2 else if k = 7 then 0xFFFFFFFFFFFFFFFF
  else if 8 ≤ k ∧ k < 16 then BitVec.ofNat 64 (0x1100 + (k - 8) * 32)
  else if k = 32 then 1 else 0

def montSatMem : Mem := fun x =>
  if x = 0x8000 then 1 else
  let i := (x - 0x1000).toNat
  if i < 512 then (montSatWord (i / 8)).extractLsb' (8 * (i % 8)) 8 else 0

def montSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 1 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem := montSatMem
  rd := [⟨0x8000, 4⟩]
  wr := [⟨0x1000, 512⟩]

theorem mont_contract_sat : ∃ s, (Proof.Rsa.Mont.mulContract abi 36).pre s := by
  sig_implies_sat [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [montSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using montSatState

theorem mont_verified : Verified target MontFn.mul (Proof.Rsa.Mont.mulContract abi 36) :=
  ⟨mont_contract_correct, mont_contract_ct, mont_contract_sat⟩

end VG.Proof.Bignum.Arm
