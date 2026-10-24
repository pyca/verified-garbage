module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Rsa.PPC64LE.Priv
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCorrect
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCT
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# `vg_rsa_private_checked` on PPC64LE: verified against the shared contract

`fnContract` states the shared contract's postcondition on the registers and
the stack (`priv_implies`); with correctness (`code_correct`) and constant
time (`code_ct`), `code` is verified for the `frameBytes` bytes of stack its
frame uses (`priv_verified`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv

/-- The shared contract, its postcondition on the registers and the stack. -/
def fnContract : Contract isa where
  pre := (Spec.Rsa.privateCheckedContract abi frameBytes).pre
  post := fnPost
  pub := (Spec.Rsa.privateCheckedContract abi frameBytes).pub

/-- A state meeting the precondition: a 64-byte modulus, input and `out`, a
one-byte exponent, primes, exponents and `qInv`, and the stack arguments at
`0x10060`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x2000 | .r6 => 64 | .r7 => 0x3000 | .r8 => 1
    | .r9 => 0x4000 | .r10 => 64 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := if a = 0x10061 then 0x41 else if a = 0x10068 then 1 else if a = 0x10071 then 0x42
    else if a = 0x10078 then 1 else if a = 0x10081 then 0x43 else if a = 0x10088 then 1
    else if a = 0x10091 then 0x44 else if a = 0x10098 then 1 else if a = 0x100A1 then 0x45
    else if a = 0x100A8 then 1 else if a = 0x100B2 then 0x02 else if a = 0x100B8 then 0x20
    else if a = 0x100B9 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 64⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x4500, 1⟩, ⟨0x10060, 96⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 8448⟩]

theorem priv_implies : fnContract.Implies (Spec.Rsa.privateCheckedContract abi frameBytes) where
  pre := fun _ h => h
  post := by
    sig_implies_post [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, fnContract,
      fnPost, stackArgs_twelve, List.append_eq]
  pub := fun _ _ _ _ h => h
  sat := by
    sig_implies_sat [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, fnContract,
      stackArgs_twelve, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using satState

/-- `vg_rsa_private_checked`. -/
theorem priv_verified : Verified target code (Spec.Rsa.privateCheckedContract abi frameBytes) :=
  Verified.of_correct code_correct code_ct priv_implies

end VG.Proof.Rsa.PPC64LE.Priv
