module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Rsa.RISCV64.Priv
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCorrect
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCT
public import VerifiedGarbage.Proof.Rsa.Contract
meta import VerifiedGarbage.Proof.Rsa.Contract

/-!
# `vg_rsa_private_checked` on RISC-V: the shared contract on the registers

`fnContract` states the shared contract's postcondition on the registers and
the stack.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Priv

open VG VG.RISCV64 VG.Impl.Rsa.RISCV64.Priv

/-- The shared contract, its postcondition on the registers and the stack. -/
def fnContract : Contract isa where
  pre := (Proof.Rsa.privateCheckedContract RISCV64.abi frameBytes).pre
  post := fnPost
  pub := (Proof.Rsa.privateCheckedContract RISCV64.abi frameBytes).pub

end VG.Proof.Rsa.RISCV64.Priv
