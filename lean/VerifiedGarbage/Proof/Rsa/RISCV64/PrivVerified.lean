module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Rsa.RISCV64.Priv
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCorrect
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCT

/-!
# `vg_rsa_private_checked` on RISC-V: verified against the shared contract

`fnContract` states the shared contract's postcondition on the registers and
the stack (`priv_implies`); with correctness (`code_correct`) and constant
time (`code_ct`), `code` is verified for the `frameBytes` bytes of stack its
frame uses (`priv_verified`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Priv

open VG VG.RISCV64 VG.Impl.Rsa.RISCV64.Priv

/-- The shared contract, its postcondition on the registers and the stack. -/
def fnContract : Contract isa where
  pre := (Spec.Rsa.privateCheckedContract RISCV64.abi frameBytes).pre
  post := fnPost
  pub := (Spec.Rsa.privateCheckedContract RISCV64.abi frameBytes).pub

/-- A state meeting the precondition: a 64-byte modulus, input and `out`, a
one-byte exponent, primes, exponents and `qInv`, and the stack arguments at
`0x10000`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 64 | .a4 => 0x3000 | .a5 => 1
    | .a6 => 0x4000 | .a7 => 64 | _ => 0
  sp := 0x10000
  mem a :=
    bif Nat.beq a.toNat 0x10001 then 0x41 else bif Nat.beq a.toNat 0x10008 then 1
    else bif Nat.beq a.toNat 0x10011 then 0x42 else bif Nat.beq a.toNat 0x10018 then 1
    else bif Nat.beq a.toNat 0x10021 then 0x43 else bif Nat.beq a.toNat 0x10028 then 1
    else bif Nat.beq a.toNat 0x10031 then 0x44 else bif Nat.beq a.toNat 0x10038 then 1
    else bif Nat.beq a.toNat 0x10041 then 0x45 else bif Nat.beq a.toNat 0x10048 then 1
    else bif Nat.beq a.toNat 0x10052 then 0x02 else bif Nat.beq a.toNat 0x10058 then 0x20
    else bif Nat.beq a.toNat 0x10059 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 64⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x4500, 1⟩, ⟨0x10000, 96⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 8448⟩]

theorem priv_implies : fnContract.Implies (Spec.Rsa.privateCheckedContract RISCV64.abi frameBytes) where
  pre := fun _ h => h
  post := by
    sig_implies_post [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, RISCV64.abi,
      RISCV64.argRegs, fnContract, fnPost, stackArgs_twelve, List.append_eq]
  pub := fun _ _ _ _ h => h
  sat := by
    sig_implies_sat [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, RISCV64.abi,
      RISCV64.argRegs, fnContract, stackArgs_twelve, List.append_eq] [satState, stackArg, stackArgAddr,
      Mem.readW, Mem.read] using satState

/-- `vg_rsa_private_checked`. -/
theorem priv_verified :
    Verified RISCV64.target code (Spec.Rsa.privateCheckedContract RISCV64.abi frameBytes) :=
  Verified.of_correct code_correct code_ct priv_implies

end VG.Proof.Rsa.RISCV64.Priv
